external create_raw_socket : string -> Unix.file_descr = "caml_create_raw_socket"
external send_ethernet_frame : Unix.file_descr -> bytes -> int -> unit = "caml_send_ethernet_frame"
external recv_ethernet_frame : Unix.file_descr -> bytes -> int = "caml_recv_ethernet_frame"
external get_interface_mac : string -> bytes = "caml_get_interface_mac"
external get_interface_ipv4 : string -> bytes = "caml_get_interface_ipv4"
external netlink_update_arp : string -> bytes -> bytes -> unit = "caml_netlink_update_arp"
external set_socket_timeout : Unix.file_descr -> int -> unit = "caml_set_socket_timeout"
external close_socket : Unix.file_descr -> unit = "caml_close_socket"

type raw_socket = {
  fd: Unix.file_descr;
  interface: string;
  mac_addr: bytes;
  ip_addr: bytes;
}

exception Socket_error of string
exception Invalid_packet of string

let format_mac mac =
  if Bytes.length mac <> 6 then
    raise (Invalid_argument "MAC address must be 6 bytes");
  Printf.sprintf "%02x:%02x:%02x:%02x:%02x:%02x"
    (int_of_char (Bytes.get mac 0))
    (int_of_char (Bytes.get mac 1))
    (int_of_char (Bytes.get mac 2))
    (int_of_char (Bytes.get mac 3))
    (int_of_char (Bytes.get mac 4))
    (int_of_char (Bytes.get mac 5))

let format_ipv4 ip =
  if Bytes.length ip <> 4 then
    raise (Invalid_argument "IPv4 address must be 4 bytes");
  Printf.sprintf "%d.%d.%d.%d"
    (int_of_char (Bytes.get ip 0))
    (int_of_char (Bytes.get ip 1))
    (int_of_char (Bytes.get ip 2))
    (int_of_char (Bytes.get ip 3))

let parse_mac str =
  try
    let parts = String.split_on_char ':' str in
    if List.length parts <> 6 then
      raise (Invalid_argument "MAC address must have 6 octets");
    let mac = Bytes.create 6 in
    List.iteri (fun i hex_str ->
      let value = int_of_string ("0x" ^ hex_str) in
      if value < 0 || value > 255 then
        raise (Invalid_argument "Invalid MAC octet");
      Bytes.set mac i (char_of_int value)
    ) parts;
    mac
  with _ ->
    raise (Invalid_argument ("Invalid MAC address format: " ^ str))

let parse_ipv4 str =
  try
    let parts = String.split_on_char '.' str in
    if List.length parts <> 4 then
      raise (Invalid_argument "IPv4 address must have 4 octets");
    let ip = Bytes.create 4 in
    List.iteri (fun i octet_str ->
      let value = int_of_string octet_str in
      if value < 0 || value > 255 then
        raise (Invalid_argument "Invalid IP octet");
      Bytes.set ip i (char_of_int value)
    ) parts;
    ip
  with _ ->
    raise (Invalid_argument ("Invalid IPv4 address format: " ^ str))

let open_arp_socket ?(timeout=1) interface =
  Printf.printf "STUB: Would open socket on %s with timeout %d\n" interface timeout;
  {
    fd = Unix.stdin;
    interface;
    mac_addr = Bytes.of_string "\x00\x00\x00\x00\x00\x00";
    ip_addr = Bytes.of_string "\x00\x00\x00\x00";
  }

let close_arp_socket socket =
  Printf.printf "STUB: Would close socket on %s\n" socket.interface

type ethernet_frame = {
  dst_mac: bytes;
  src_mac: bytes;
  ethertype: int;
  payload: bytes;
}

let parse_ethernet_frame buffer length =
  if length < 14 then
    raise (Invalid_packet "Frame too short for Ethernet header");
  let dst_mac = Bytes.sub buffer 0 6 in
  let src_mac = Bytes.sub buffer 6 6 in
  let ethertype =
    (int_of_char (Bytes.get buffer 12) lsl 8) lor
    (int_of_char (Bytes.get buffer 13)) in
  let payload = Bytes.sub buffer 14 (length - 14) in
  { dst_mac; src_mac; ethertype; payload }

let construct_ethernet_frame dst_mac src_mac ethertype payload =
  let frame_len = 14 + Bytes.length payload in
  let frame = Bytes.create frame_len in
  Bytes.blit dst_mac 0 frame 0 6;
  Bytes.blit src_mac 0 frame 6 6;
  Bytes.set frame 12 (char_of_int (ethertype lsr 8));
  Bytes.set frame 13 (char_of_int (ethertype land 0xFF));
  Bytes.blit payload 0 frame 14 (Bytes.length payload);
  frame

let send_arp_frame socket arp_payload target_mac =
  Printf.printf "STUB: Would send ARP frame on %s\n" socket.interface

let receive_arp_frame socket =
  None

let sync_arp_entry_to_kernel socket ip_bytes mac_bytes =
  Printf.printf "STUB: Would sync to kernel ARP table\n"

let bytes_to_int_list bytes =
  let rec aux i acc =
    if i < 0 then acc
    else aux (i - 1) (int_of_char (Bytes.get bytes i) :: acc)
  in
  aux (Bytes.length bytes - 1) []

let int_list_to_bytes lst =
  let len = List.length lst in
  let bytes = Bytes.create len in
  List.iteri (fun i value ->
    if value < 0 || value > 255 then
      raise (Invalid_argument "Byte value out of range");
    Bytes.set bytes i (char_of_int value)
  ) lst;
  bytes
