#include <caml/mlvalues.h>
#include <caml/alloc.h>
#include <caml/memory.h>
#include <caml/fail.h>
#include <caml/callback.h>
#include <caml/bigarray.h>

#ifdef _WIN32
#include <winsock2.h>
#include <ws2tcpip.h>
#include <iphlpapi.h>
#pragma comment(lib, "ws2_32.lib")
#pragma comment(lib, "iphlpapi.lib")
#else
#include <sys/socket.h>
#include <sys/ioctl.h>
#include <linux/if_packet.h>
#include <linux/if_ether.h>
#include <linux/netlink.h>
#include <linux/rtnetlink.h>
#include <net/if.h>
#include <arpa/inet.h>
#include <unistd.h>
#include <string.h>
#include <errno.h>
#endif

#define ETH_P_ARP 0x0806
#define ARP_FRAME_SIZE 42

CAMLprim value caml_create_raw_socket(value iface_name) {
  CAMLparam1(iface_name);

#ifdef _WIN32
  caml_failwith("Raw sockets not yet implemented for Windows - use WinPcap/Npcap");
  CAMLreturn(Val_int(-1));
#else
  int sockfd = socket(AF_PACKET, SOCK_RAW, htons(ETH_P_ARP));
  if (sockfd < 0) {
    char error_msg[256];
    snprintf(error_msg, sizeof(error_msg),
             "Failed to create raw socket: %s (are you root?)",
             strerror(errno));
    caml_failwith(error_msg);
  }

  struct ifreq ifr;
  memset(&ifr, 0, sizeof(ifr));
  strncpy(ifr.ifr_name, String_val(iface_name), IFNAMSIZ - 1);

  if (ioctl(sockfd, SIOCGIFINDEX, &ifr) < 0) {
    close(sockfd);
    char error_msg[256];
    snprintf(error_msg, sizeof(error_msg),
             "Failed to get interface index for %s: %s",
             String_val(iface_name), strerror(errno));
    caml_failwith(error_msg);
  }

  struct sockaddr_ll sll;
  memset(&sll, 0, sizeof(sll));
  sll.sll_family = AF_PACKET;
  sll.sll_protocol = htons(ETH_P_ARP);
  sll.sll_ifindex = ifr.ifr_ifindex;

  if (bind(sockfd, (struct sockaddr*)&sll, sizeof(sll)) < 0) {
    close(sockfd);
    char error_msg[256];
    snprintf(error_msg, sizeof(error_msg),
             "Failed to bind socket: %s", strerror(errno));
    caml_failwith(error_msg);
  }

  CAMLreturn(Val_int(sockfd));
#endif
}

CAMLprim value caml_send_ethernet_frame(value sockfd, value frame, value len) {
  CAMLparam3(sockfd, frame, len);

#ifdef _WIN32
  caml_failwith("Raw socket send not implemented for Windows");
#else
  ssize_t sent = send(Int_val(sockfd),
                      Bytes_val(frame),
                      Int_val(len),
                      0);

  if (sent < 0) {
    char error_msg[256];
    snprintf(error_msg, sizeof(error_msg),
             "Failed to send frame: %s", strerror(errno));
    caml_failwith(error_msg);
  }

  if (sent != Int_val(len)) {
    char error_msg[256];
    snprintf(error_msg, sizeof(error_msg),
             "Partial send: %zd of %d bytes", sent, Int_val(len));
    caml_failwith(error_msg);
  }
#endif

  CAMLreturn(Val_unit);
}

CAMLprim value caml_recv_ethernet_frame(value sockfd, value buffer) {
  CAMLparam2(sockfd, buffer);

#ifdef _WIN32
  caml_failwith("Raw socket recv not implemented for Windows");
  CAMLreturn(Val_int(0));
#else
  ssize_t recv_len = recvfrom(Int_val(sockfd),
                               Bytes_val(buffer),
                               caml_string_length(buffer),
                               0,
                               NULL,
                               NULL);

  if (recv_len < 0) {
    if (errno == EINTR) {
      CAMLreturn(Val_int(0));
    }
    char error_msg[256];
    snprintf(error_msg, sizeof(error_msg),
             "Failed to receive frame: %s", strerror(errno));
    caml_failwith(error_msg);
  }

  CAMLreturn(Val_int(recv_len));
#endif
}

CAMLprim value caml_get_interface_mac(value iface_name) {
  CAMLparam1(iface_name);
  CAMLlocal1(result);

#ifdef _WIN32
  caml_failwith("Interface MAC lookup not yet implemented for Windows");
  CAMLreturn(Val_unit);
#else
  int sockfd = socket(AF_INET, SOCK_DGRAM, 0);
  if (sockfd < 0) {
    caml_failwith("Failed to create socket for MAC lookup");
  }

  struct ifreq ifr;
  memset(&ifr, 0, sizeof(ifr));
  strncpy(ifr.ifr_name, String_val(iface_name), IFNAMSIZ - 1);

  if (ioctl(sockfd, SIOCGIFHWADDR, &ifr) < 0) {
    close(sockfd);
    char error_msg[256];
    snprintf(error_msg, sizeof(error_msg),
             "Failed to get MAC address for %s: %s",
             String_val(iface_name), strerror(errno));
    caml_failwith(error_msg);
  }

  close(sockfd);

  result = caml_alloc_string(6);
  memcpy(Bytes_val(result), ifr.ifr_hwaddr.sa_data, 6);

  CAMLreturn(result);
#endif
}

CAMLprim value caml_get_interface_ipv4(value iface_name) {
  CAMLparam1(iface_name);
  CAMLlocal1(result);

#ifdef _WIN32
  caml_failwith("Interface IPv4 lookup not yet implemented for Windows");
  CAMLreturn(Val_unit);
#else
  int sockfd = socket(AF_INET, SOCK_DGRAM, 0);
  if (sockfd < 0) {
    caml_failwith("Failed to create socket for IP lookup");
  }

  struct ifreq ifr;
  memset(&ifr, 0, sizeof(ifr));
  strncpy(ifr.ifr_name, String_val(iface_name), IFNAMSIZ - 1);

  if (ioctl(sockfd, SIOCGIFADDR, &ifr) < 0) {
    close(sockfd);
    char error_msg[256];
    snprintf(error_msg, sizeof(error_msg),
             "Failed to get IP address for %s: %s",
             String_val(iface_name), strerror(errno));
    caml_failwith(error_msg);
  }

  close(sockfd);

  struct sockaddr_in *addr = (struct sockaddr_in *)&ifr.ifr_addr;
  result = caml_alloc_string(4);
  memcpy(Bytes_val(result), &addr->sin_addr.s_addr, 4);

  CAMLreturn(result);
#endif
}

CAMLprim value caml_netlink_update_arp(value iface_name, value ip_addr, value mac_addr) {
  CAMLparam3(iface_name, ip_addr, mac_addr);

#ifdef _WIN32
  caml_failwith("Netlink not available on Windows - use ARP API");
  CAMLreturn(Val_unit);
#else
  int sockfd = socket(AF_NETLINK, SOCK_RAW, NETLINK_ROUTE);
  if (sockfd < 0) {
    char error_msg[256];
    snprintf(error_msg, sizeof(error_msg),
             "Failed to create netlink socket: %s", strerror(errno));
    caml_failwith(error_msg);
  }

  struct {
    struct nlmsghdr nlh;
    struct ndmsg ndm;
    char buf[256];
  } req;

  memset(&req, 0, sizeof(req));

  req.nlh.nlmsg_len = NLMSG_LENGTH(sizeof(struct ndmsg));
  req.nlh.nlmsg_flags = NLM_F_REQUEST | NLM_F_CREATE | NLM_F_REPLACE;
  req.nlh.nlmsg_type = RTM_NEWNEIGH;

  req.ndm.ndm_family = AF_INET;
  req.ndm.ndm_state = NUD_REACHABLE;
  req.ndm.ndm_ifindex = if_nametoindex(String_val(iface_name));

  if (req.ndm.ndm_ifindex == 0) {
    close(sockfd);
    char error_msg[256];
    snprintf(error_msg, sizeof(error_msg),
             "Interface %s not found", String_val(iface_name));
    caml_failwith(error_msg);
  }

  struct rtattr *rta = (struct rtattr *)
    (((char *)&req) + NLMSG_ALIGN(req.nlh.nlmsg_len));
  rta->rta_type = NDA_DST;
  rta->rta_len = RTA_LENGTH(4);
  memcpy(RTA_DATA(rta), Bytes_val(ip_addr), 4);
  req.nlh.nlmsg_len = NLMSG_ALIGN(req.nlh.nlmsg_len) + RTA_LENGTH(4);

  rta = (struct rtattr *)
    (((char *)&req) + NLMSG_ALIGN(req.nlh.nlmsg_len));
  rta->rta_type = NDA_LLADDR;
  rta->rta_len = RTA_LENGTH(6);
  memcpy(RTA_DATA(rta), Bytes_val(mac_addr), 6);
  req.nlh.nlmsg_len = NLMSG_ALIGN(req.nlh.nlmsg_len) + RTA_LENGTH(6);

  if (send(sockfd, &req, req.nlh.nlmsg_len, 0) < 0) {
    close(sockfd);
    char error_msg[256];
    snprintf(error_msg, sizeof(error_msg),
             "Failed to update kernel ARP table: %s", strerror(errno));
    caml_failwith(error_msg);
  }

  close(sockfd);
#endif

  CAMLreturn(Val_unit);
}

CAMLprim value caml_set_socket_timeout(value sockfd, value timeout_sec) {
  CAMLparam2(sockfd, timeout_sec);

#ifdef _WIN32
  DWORD timeout = Int_val(timeout_sec) * 1000;
  if (setsockopt(Int_val(sockfd), SOL_SOCKET, SO_RCVTIMEO,
                 (const char*)&timeout, sizeof(timeout)) < 0) {
    caml_failwith("Failed to set socket timeout");
  }
#else
  struct timeval tv;
  tv.tv_sec = Int_val(timeout_sec);
  tv.tv_usec = 0;

  if (setsockopt(Int_val(sockfd), SOL_SOCKET, SO_RCVTIMEO,
                 &tv, sizeof(tv)) < 0) {
    char error_msg[256];
    snprintf(error_msg, sizeof(error_msg),
             "Failed to set socket timeout: %s", strerror(errno));
    caml_failwith(error_msg);
  }
#endif

  CAMLreturn(Val_unit);
}

CAMLprim value caml_close_socket(value sockfd) {
  CAMLparam1(sockfd);

#ifdef _WIN32
  closesocket(Int_val(sockfd));
#else
  close(Int_val(sockfd));
#endif

  CAMLreturn(Val_unit);
}
