type coq_N = int

type coq_mac = {
  mac_bytes: coq_N list;
  mac_valid: unit;
}

type coq_ipv4 = {
  ipv4_a: coq_N;
  ipv4_b: coq_N;
  ipv4_c: coq_N;
  ipv4_d: coq_N;
}

type coq_arp_packet = {
  arp_op: coq_N;
  arp_sha: coq_mac;
  arp_spa: coq_ipv4;
  arp_tha: coq_mac;
  arp_tpa: coq_ipv4;
}

type coq_cache_entry = {
  ace_ip: coq_ipv4;
  ace_mac: coq_mac;
  ace_ttl: coq_N;
  ace_static: bool;
}

type coq_arp_context = {
  arp_my_mac: coq_mac;
  arp_my_ip: coq_ipv4;
  arp_cache: coq_cache_entry list;
  arp_cache_ttl: coq_N;
}

let bytes_to_coq_mac bytes =
  if Bytes.length bytes <> 6 then
    raise (Invalid_argument "MAC must be 6 bytes");
  let byte_list = [
    int_of_char (Bytes.get bytes 0);
    int_of_char (Bytes.get bytes 1);
    int_of_char (Bytes.get bytes 2);
    int_of_char (Bytes.get bytes 3);
    int_of_char (Bytes.get bytes 4);
    int_of_char (Bytes.get bytes 5);
  ] in
  { mac_bytes = byte_list; mac_valid = () }

let coq_mac_to_bytes mac =
  match mac.mac_bytes with
  | [b0; b1; b2; b3; b4; b5] ->
      let bytes = Bytes.create 6 in
      Bytes.set bytes 0 (char_of_int b0);
      Bytes.set bytes 1 (char_of_int b1);
      Bytes.set bytes 2 (char_of_int b2);
      Bytes.set bytes 3 (char_of_int b3);
      Bytes.set bytes 4 (char_of_int b4);
      Bytes.set bytes 5 (char_of_int b5);
      bytes
  | _ -> raise (Invalid_argument "Invalid MAC structure")

let bytes_to_coq_ipv4 bytes =
  if Bytes.length bytes <> 4 then
    raise (Invalid_argument "IPv4 must be 4 bytes");
  {
    ipv4_a = int_of_char (Bytes.get bytes 0);
    ipv4_b = int_of_char (Bytes.get bytes 1);
    ipv4_c = int_of_char (Bytes.get bytes 2);
    ipv4_d = int_of_char (Bytes.get bytes 3);
  }

let coq_ipv4_to_bytes ip =
  let bytes = Bytes.create 4 in
  Bytes.set bytes 0 (char_of_int ip.ipv4_a);
  Bytes.set bytes 1 (char_of_int ip.ipv4_b);
  Bytes.set bytes 2 (char_of_int ip.ipv4_c);
  Bytes.set bytes 3 (char_of_int ip.ipv4_d);
  bytes

let bytes_to_coq_N_list bytes =
  let rec aux i acc =
    if i < 0 then acc
    else aux (i - 1) (int_of_char (Bytes.get bytes i) :: acc)
  in
  aux (Bytes.length bytes - 1) []

let coq_N_list_to_bytes lst =
  let len = List.length lst in
  let bytes = Bytes.create len in
  List.iteri (fun i n ->
    if n < 0 || n > 255 then
      raise (Invalid_argument "Byte value out of range");
    Bytes.set bytes i (char_of_int n)
  ) lst;
  bytes

let create_initial_context mac_bytes ip_bytes ttl =
  {
    arp_my_mac = bytes_to_coq_mac mac_bytes;
    arp_my_ip = bytes_to_coq_ipv4 ip_bytes;
    arp_cache = [];
    arp_cache_ttl = ttl;
  }

let get_cache_entries ctx =
  ctx.arp_cache

let format_coq_mac mac =
  Network_io_stub.format_mac (coq_mac_to_bytes mac)

let format_coq_ipv4 ip =
  Network_io_stub.format_ipv4 (coq_ipv4_to_bytes ip)

let print_cache_entry entry =
  Printf.printf "  %s -> %s (TTL: %d, Static: %b)\n"
    (format_coq_ipv4 entry.ace_ip)
    (format_coq_mac entry.ace_mac)
    entry.ace_ttl
    entry.ace_static

let print_cache ctx =
  Printf.printf "ARP Cache (%d entries):\n" (List.length ctx.arp_cache);
  List.iter print_cache_entry ctx.arp_cache;
  flush stdout
