/******************************************************************************
 * WinPcap/Npcap FFI Bindings for OCaml                                       *
 *                                                                             *
 * This provides direct bindings to pcap.dll (WinPcap/Npcap) for Windows.    *
 * On Unix, it would link against libpcap.                                    *
 ******************************************************************************/

#include <caml/mlvalues.h>
#include <caml/memory.h>
#include <caml/alloc.h>
#include <caml/fail.h>
#include <caml/custom.h>
#include <caml/callback.h>

#ifdef _WIN32
#include <winsock2.h>
#endif

#include <pcap.h>
#include <string.h>

/* Custom block for pcap_t handle */
#define Pcap_val(v) (*((pcap_t **) Data_custom_val(v)))

static void finalize_pcap(value v) {
    pcap_t *handle = Pcap_val(v);
    if (handle != NULL) {
        pcap_close(handle);
    }
}

static struct custom_operations pcap_ops = {
    "org.sammathnaur.pcap",
    finalize_pcap,
    custom_compare_default,
    custom_hash_default,
    custom_serialize_default,
    custom_deserialize_default,
    custom_compare_ext_default,
    custom_fixed_length_default
};

/* Allocate a custom block for pcap_t */
static value alloc_pcap(pcap_t *handle) {
    value v = alloc_custom(&pcap_ops, sizeof(pcap_t *), 0, 1);
    Pcap_val(v) = handle;
    return v;
}

/* CAMLprim: Open a network device for packet capture
 * pcap_open : string -> int -> bool -> int -> pcap_t
 * Parameters:
 *   device: interface name (e.g., "\\Device\\NPF_{GUID}" on Windows)
 *   snaplen: snapshot length (max bytes per packet)
 *   promisc: promiscuous mode (true/false)
 *   timeout_ms: read timeout in milliseconds
 */
CAMLprim value caml_pcap_open(value device, value snaplen, value promisc, value timeout_ms) {
    CAMLparam4(device, snaplen, promisc, timeout_ms);
    CAMLlocal1(result);

    char errbuf[PCAP_ERRBUF_SIZE];
    pcap_t *handle;

    handle = pcap_open_live(
        String_val(device),
        Int_val(snaplen),
        Bool_val(promisc) ? 1 : 0,
        Int_val(timeout_ms),
        errbuf
    );

    if (handle == NULL) {
        caml_failwith(errbuf);
    }

    result = alloc_pcap(handle);
    CAMLreturn(result);
}

/* CAMLprim: Find all available network devices
 * pcap_findalldevs : unit -> string list
 */
CAMLprim value caml_pcap_findalldevs(value unit) {
    CAMLparam1(unit);
    CAMLlocal2(result, cons);

    char errbuf[PCAP_ERRBUF_SIZE];
    pcap_if_t *alldevs, *d;

    if (pcap_findalldevs(&alldevs, errbuf) == -1) {
        caml_failwith(errbuf);
    }

    result = Val_emptylist;
    for (d = alldevs; d != NULL; d = d->next) {
        cons = caml_alloc(2, 0);  /* Cons cell */
        Store_field(cons, 0, caml_copy_string(d->name));
        Store_field(cons, 1, result);
        result = cons;
    }

    pcap_freealldevs(alldevs);
    CAMLreturn(result);
}

/* CAMLprim: Set a filter on the pcap handle
 * pcap_setfilter : pcap_t -> string -> unit
 */
CAMLprim value caml_pcap_setfilter(value handle_val, value filter_str) {
    CAMLparam2(handle_val, filter_str);

    pcap_t *handle = Pcap_val(handle_val);
    struct bpf_program fp;

    if (pcap_compile(handle, &fp, String_val(filter_str), 1, PCAP_NETMASK_UNKNOWN) == -1) {
        caml_failwith(pcap_geterr(handle));
    }

    if (pcap_setfilter(handle, &fp) == -1) {
        pcap_freecode(&fp);
        caml_failwith(pcap_geterr(handle));
    }

    pcap_freecode(&fp);
    CAMLreturn(Val_unit);
}

/* CAMLprim: Capture one packet (blocking)
 * pcap_next : pcap_t -> bytes option
 * Returns None on timeout, Some bytes on packet capture
 */
CAMLprim value caml_pcap_next(value handle_val) {
    CAMLparam1(handle_val);
    CAMLlocal2(result, packet_data);

    pcap_t *handle = Pcap_val(handle_val);
    struct pcap_pkthdr *header;
    const u_char *pkt_data;
    int res;

    res = pcap_next_ex(handle, &header, &pkt_data);

    if (res == 1) {
        /* Packet captured successfully */
        packet_data = caml_alloc_string(header->caplen);
        memcpy(Bytes_val(packet_data), pkt_data, header->caplen);

        result = caml_alloc(1, 0);  /* Some */
        Store_field(result, 0, packet_data);
    } else if (res == 0) {
        /* Timeout */
        result = Val_int(0);  /* None */
    } else if (res == -1) {
        /* Error */
        caml_failwith(pcap_geterr(handle));
    } else {
        /* EOF (should not happen in live capture) */
        result = Val_int(0);  /* None */
    }

    CAMLreturn(result);
}

/* CAMLprim: Send a raw packet
 * pcap_sendpacket : pcap_t -> bytes -> unit
 */
CAMLprim value caml_pcap_sendpacket(value handle_val, value packet) {
    CAMLparam2(handle_val, packet);

    pcap_t *handle = Pcap_val(handle_val);
    int res;

    res = pcap_sendpacket(handle, Bytes_val(packet), caml_string_length(packet));

    if (res != 0) {
        caml_failwith(pcap_geterr(handle));
    }

    CAMLreturn(Val_unit);
}

/* CAMLprim: Close pcap handle
 * pcap_close : pcap_t -> unit
 */
CAMLprim value caml_pcap_close(value handle_val) {
    CAMLparam1(handle_val);

    pcap_t *handle = Pcap_val(handle_val);
    if (handle != NULL) {
        pcap_close(handle);
        Pcap_val(handle_val) = NULL;
    }

    CAMLreturn(Val_unit);
}

/* CAMLprim: Get MAC address of an interface (Windows-specific using GetAdaptersInfo)
 * get_interface_mac : string -> string
 * Returns MAC address as 6-byte string
 */
#ifdef _WIN32
#include <iphlpapi.h>
#pragma comment(lib, "iphlpapi.lib")

CAMLprim value caml_get_interface_mac(value device_name) {
    CAMLparam1(device_name);
    CAMLlocal1(result);

    ULONG buflen = 15000;
    PIP_ADAPTER_INFO pAdapterInfo = (IP_ADAPTER_INFO *) malloc(buflen);

    if (GetAdaptersInfo(pAdapterInfo, &buflen) == ERROR_BUFFER_OVERFLOW) {
        free(pAdapterInfo);
        pAdapterInfo = (IP_ADAPTER_INFO *) malloc(buflen);
    }

    if (GetAdaptersInfo(pAdapterInfo, &buflen) == NO_ERROR) {
        PIP_ADAPTER_INFO pAdapter = pAdapterInfo;
        const char *dev = String_val(device_name);

        while (pAdapter) {
            /* Check if adapter name matches */
            if (strstr(dev, pAdapter->AdapterName) != NULL) {
                if (pAdapter->AddressLength == 6) {
                    result = caml_alloc_string(6);
                    memcpy(Bytes_val(result), pAdapter->Address, 6);
                    free(pAdapterInfo);
                    CAMLreturn(result);
                }
            }
            pAdapter = pAdapter->Next;
        }
    }

    free(pAdapterInfo);
    caml_failwith("Could not find interface MAC address");
}
#else
/* Unix/Linux: Use ioctl SIOCGIFHWADDR */
#include <sys/ioctl.h>
#include <net/if.h>
#include <unistd.h>

CAMLprim value caml_get_interface_mac(value device_name) {
    CAMLparam1(device_name);
    CAMLlocal1(result);

    struct ifreq ifr;
    int fd = socket(AF_INET, SOCK_DGRAM, 0);

    if (fd < 0) {
        caml_failwith("Could not create socket");
    }

    strncpy(ifr.ifr_name, String_val(device_name), IFNAMSIZ-1);

    if (ioctl(fd, SIOCGIFHWADDR, &ifr) == 0) {
        result = caml_alloc_string(6);
        memcpy(Bytes_val(result), ifr.ifr_hwaddr.sa_data, 6);
        close(fd);
        CAMLreturn(result);
    }

    close(fd);
    caml_failwith("Could not get interface MAC address");
}
#endif
