(******************************************************************************)
(* OCaml Bindings to WinPcap/Npcap via C FFI                                  *)
(******************************************************************************)

(* Abstract type for pcap handle *)
type t

(* External C functions *)
external pcap_open : string -> int -> bool -> int -> t = "caml_pcap_open"
external pcap_findalldevs : unit -> string list = "caml_pcap_findalldevs"
external pcap_setfilter : t -> string -> unit = "caml_pcap_setfilter"
external pcap_next : t -> bytes option = "caml_pcap_next"
external pcap_sendpacket : t -> bytes -> unit = "caml_pcap_sendpacket"
external pcap_close : t -> unit = "caml_pcap_close"
external get_interface_mac : string -> bytes = "caml_get_interface_mac"

(* Helper: Find the first suitable network device *)
let find_default_device () =
  match pcap_findalldevs () with
  | [] -> failwith "No network devices found"
  | dev :: _ -> dev

(* Helper: Open device with standard settings for ARP *)
let open_for_arp device =
  let handle = pcap_open device 65536 true 1000 in
  pcap_setfilter handle "arp";
  handle

(* Helper: List all devices with descriptions *)
let list_devices () =
  pcap_findalldevs ()
