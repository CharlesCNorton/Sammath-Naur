(******************************************************************************)
(* OCaml Bindings to WinPcap/Npcap - Interface                                *)
(******************************************************************************)

(** Opaque handle to a pcap capture session *)
type t

(** {2 Device Management} *)

(** [pcap_open device snaplen promisc timeout_ms] opens a network device
    for packet capture.
    @param device Device name (e.g., "\\Device\\NPF_{GUID}" on Windows)
    @param snaplen Maximum bytes to capture per packet (usually 65536)
    @param promisc Enable promiscuous mode (capture all packets)
    @param timeout_ms Read timeout in milliseconds
    @raise Failure if device cannot be opened *)
val pcap_open : string -> int -> bool -> int -> t

(** [pcap_findalldevs ()] returns a list of all available network devices.
    @raise Failure if device enumeration fails *)
val pcap_findalldevs : unit -> string list

(** [find_default_device ()] returns the first available network device.
    @raise Failure if no devices found *)
val find_default_device : unit -> string

(** {2 Filtering} *)

(** [pcap_setfilter handle filter_str] sets a BPF filter on the capture.
    @param handle Pcap handle
    @param filter_str BPF filter expression (e.g., "arp", "tcp port 80")
    @raise Failure if filter is invalid or cannot be set *)
val pcap_setfilter : t -> string -> unit

(** {2 Packet Capture and Injection} *)

(** [pcap_next handle] captures the next packet (blocking).
    Returns [Some bytes] on success, [None] on timeout.
    @raise Failure on capture error *)
val pcap_next : t -> bytes option

(** [pcap_sendpacket handle packet] sends a raw packet.
    @param handle Pcap handle
    @param packet Raw packet bytes including all headers
    @raise Failure if send fails *)
val pcap_sendpacket : t -> bytes -> unit

(** {2 Resource Management} *)

(** [pcap_close handle] closes the pcap handle and releases resources.
    It is safe to call this multiple times. *)
val pcap_close : t -> unit

(** {2 Interface Information} *)

(** [get_interface_mac device] retrieves the MAC address of a network interface.
    Returns 6 bytes representing the MAC address.
    @raise Failure if interface not found or MAC cannot be retrieved *)
val get_interface_mac : string -> bytes

(** {2 Convenience Functions} *)

(** [open_for_arp device] opens a device with standard settings for ARP capture:
    - Snapshot length: 65536
    - Promiscuous mode: enabled
    - Timeout: 1000ms
    - Filter: "arp"
    @raise Failure if device cannot be opened or filter cannot be set *)
val open_for_arp : string -> t

(** [list_devices ()] returns the list of all available network devices.
    Alias for {!pcap_findalldevs}. *)
val list_devices : unit -> string list
