(******************************************************************************)
(* Production ARP Daemon - Integration with Verified ARP Implementation      *)
(*                                                                            *)
(* This daemon provides real network integration for the formally verified   *)
(* ARP implementation extracted from Coq. It uses raw sockets (on Unix) or   *)
(* WinPcap/Npcap (on Windows) to capture and inject Ethernet frames.         *)
(*                                                                            *)
(* Architecture:                                                              *)
(*   1. Capture Ethernet frames from network interface                       *)
(*   2. Filter for ARP ethertype (0x0806)                                    *)
(*   3. Parse Ethernet + ARP headers                                         *)
(*   4. Feed to verified process_arp_packet_enhanced                         *)
(*   5. Send any reply packets back to wire                                  *)
(*   6. Maintain timer-driven cache aging and request retries                *)
(******************************************************************************)

open Arp

(* Network byte order conversion *)
let htons x =
  ((x land 0xFF) lsl 8) lor ((x lsr 8) land 0xFF)

let ntohs = htons  (* Symmetric operation *)

let htonl x =
  ((x land 0xFF) lsl 24) lor
  ((x land 0xFF00) lsl 8) lor
  ((x land 0xFF0000) lsr 8) lor
  ((x lsr 24) land 0xFF)

let ntohl = htonl  (* Symmetric operation *)

(* Convert between int and Coq N (which extracts to an inductive type) *)
let rec positive_to_int = function
  | Arp.XI p -> 1 + 2 * (positive_to_int p)
  | Arp.XO p -> 2 * (positive_to_int p)
  | Arp.XH -> 1

let n_to_int = function
  | Arp.N0 -> 0
  | Arp.Npos p -> positive_to_int p

let rec int_to_positive = function
  | 1 -> Arp.XH
  | n when n mod 2 = 0 -> Arp.XO (int_to_positive (n / 2))
  | n -> Arp.XI (int_to_positive (n / 2))

let int_to_n = function
  | 0 -> Arp.N0
  | n when n > 0 -> Arp.Npos (int_to_positive n)
  | _ -> Arp.N0  (* Negative numbers map to 0 *)

(* Broadcast MAC address *)
let mac_broadcast = [int_to_n 0xFF; int_to_n 0xFF; int_to_n 0xFF;
                     int_to_n 0xFF; int_to_n 0xFF; int_to_n 0xFF]

(* Ethernet frame structure *)
type ethernet_frame = {
  eth_dst : bytes;      (* 6 bytes destination MAC *)
  eth_src : bytes;      (* 6 bytes source MAC *)
  eth_type : int;       (* 2 bytes ethertype *)
  eth_payload : bytes;  (* Variable length payload *)
}

let eth_arp_type = 0x0806
let eth_hdr_len = 14

(* Parse Ethernet frame from raw bytes *)
let parse_ethernet_frame data =
  if Bytes.length data < eth_hdr_len then
    None
  else
    let dst = Bytes.sub data 0 6 in
    let src = Bytes.sub data 6 6 in
    let eth_type = (Bytes.get_uint16_be data 12) in
    let payload = Bytes.sub data eth_hdr_len (Bytes.length data - eth_hdr_len) in
    Some {
      eth_dst = dst;
      eth_src = src;
      eth_type;
      eth_payload = payload;
    }

(* Serialize Ethernet frame to raw bytes *)
let serialize_ethernet_frame frame =
  let buf = Bytes.create (eth_hdr_len + Bytes.length frame.eth_payload) in
  Bytes.blit frame.eth_dst 0 buf 0 6;
  Bytes.blit frame.eth_src 0 buf 6 6;
  Bytes.set_uint16_be buf 12 frame.eth_type;
  Bytes.blit frame.eth_payload 0 buf eth_hdr_len (Bytes.length frame.eth_payload);
  buf

(* Convert bytes to Coq byte list *)
let bytes_to_coq_list b =
  let rec aux i acc =
    if i < 0 then acc
    else aux (i-1) ((int_to_n (Bytes.get_uint8 b i)) :: acc)
  in
  aux (Bytes.length b - 1) []

(* Convert Coq byte list to bytes *)
let coq_list_to_bytes lst =
  let len = List.length lst in
  let b = Bytes.create len in
  let rec aux i = function
    | [] -> b
    | x :: xs ->
        Bytes.set_uint8 b i (n_to_int x);
        aux (i+1) xs
  in
  aux 0 lst

(* Convert bytes to MAC address (MAC is just byte list in extracted code) *)
let bytes_to_mac b =
  if Bytes.length b <> 6 then failwith "Invalid MAC address length";
  bytes_to_coq_list b

(* Convert MAC to bytes *)
let mac_to_bytes mac =
  coq_list_to_bytes mac

(* Convert bytes to IPv4 address *)
let bytes_to_ipv4 b =
  if Bytes.length b <> 4 then failwith "Invalid IPv4 address length";
  let lst = bytes_to_coq_list b in
  match lst with
  | [a; b; c; d] -> { ipv4_a = a; ipv4_b = b; ipv4_c = c; ipv4_d = d }
  | _ -> failwith "IPv4 address conversion failed"

(* Parse string IP address like "192.168.1.1" to IPv4Address *)
let parse_ipv4_string s =
  try
    let parts = String.split_on_char '.' s in
    match parts with
    | [a; b; c; d] ->
        let a' = int_to_n (int_of_string a) in
        let b' = int_to_n (int_of_string b) in
        let c' = int_to_n (int_of_string c) in
        let d' = int_to_n (int_of_string d) in
        Some { ipv4_a = a'; ipv4_b = b'; ipv4_c = c'; ipv4_d = d' }
    | _ -> None
  with _ -> None

(* Parse string MAC address like "AA:BB:CC:DD:EE:FF" *)
let parse_mac_string s =
  try
    let parts = String.split_on_char ':' s in
    match parts with
    | [a; b; c; d; e; f] ->
        let to_byte hex = int_to_n (int_of_string ("0x" ^ hex)) in
        Some [to_byte a; to_byte b; to_byte c; to_byte d; to_byte e; to_byte f]
    | _ -> None
  with _ -> None

(* ARP daemon state *)
type daemon_state = {
  mutable ctx : enhancedARPContext;
  mutable last_time : int64;  (* Unix timestamp in milliseconds *)
  interface_name : string;
}

(* Get current time in milliseconds *)
let current_time_ms () =
  Int64.of_float (Unix.gettimeofday () *. 1000.0)

(* Convert int64 timestamp to Coq N *)
let timestamp_to_n ts =
  int_to_n (Int64.to_int ts)

(* Initialize daemon state *)
let init_daemon interface_name my_mac my_ip =
  let initial_ctx = {
    Arp.earp_my_mac = my_mac;
    Arp.earp_my_ip = my_ip;
    Arp.earp_cache = [];
    Arp.earp_state_data = Arp.StateIdle;
    Arp.earp_iface = {
      Arp.if_mac = my_mac;
      Arp.if_ip = my_ip;
      Arp.if_mtu = int_to_n 1500;
      Arp.if_up = true
    };
    Arp.earp_flood_table = [];
    Arp.earp_last_cache_cleanup = int_to_n 0
  } in
  {
    ctx = initial_ctx;
    last_time = current_time_ms ();
    interface_name;
  }

(* Process received ARP packet *)
let process_received_packet state frame =
  (* Parse ARP packet from Ethernet payload *)
  let arp_bytes = bytes_to_coq_list frame.eth_payload in
  match Arp.parse_arp_packet arp_bytes with
  | None ->
      Printf.printf "Failed to parse ARP packet\n%!";
      None
  | Some arp_pkt ->
      let current = current_time_ms () in
      let elapsed = Int64.sub current state.last_time in
      state.last_time <- current;

      (* Call verified ARP processing *)
      let (new_ctx, reply_opt) =
        Arp.process_arp_packet_enhanced
          state.ctx
          arp_pkt
          (timestamp_to_n current)
          (timestamp_to_n elapsed)
      in
      state.ctx <- new_ctx;

      (* If there's a reply, construct Ethernet frame *)
      match reply_opt with
      | None -> None
      | Some reply ->
          let reply_bytes = Arp.serialize_arp_packet reply in
          let reply_payload = coq_list_to_bytes reply_bytes in
          let reply_frame = {
            eth_dst = mac_to_bytes reply.Arp.arp_tha;
            eth_src = mac_to_bytes state.ctx.Arp.earp_my_mac;
            eth_type = eth_arp_type;
            eth_payload = reply_payload;
          } in
          Some (serialize_ethernet_frame reply_frame)

(* Platform-specific raw socket operations *)
module type RAW_SOCKET = sig
  type t
  val open_socket : string -> t
  val receive : t -> bytes option
  val send : t -> bytes -> unit
  val close : t -> unit
end

(* WinPcap/Npcap socket implementation using our FFI bindings *)
module Pcap_socket : RAW_SOCKET = struct
  type t = Pcap.t

  let open_socket interface =
    Pcap.open_for_arp interface

  let receive pcap =
    Pcap.pcap_next pcap

  let send pcap data =
    Pcap.pcap_sendpacket pcap data

  let close pcap =
    Pcap.pcap_close pcap
end

(* Main daemon loop *)
let run_daemon interface my_mac_str my_ip_str =
  match parse_mac_string my_mac_str, parse_ipv4_string my_ip_str with
  | None, _ -> failwith "Invalid MAC address format"
  | _, None -> failwith "Invalid IP address format"
  | Some my_mac, Some my_ip ->
      Printf.printf "=================================================\n";
      Printf.printf "  Formally Verified ARP Daemon (RFC 826)\n";
      Printf.printf "  Extracted from Coq proof assistant\n";
      Printf.printf "=================================================\n";
      Printf.printf "  Interface: %s\n" interface;
      Printf.printf "  MAC: %s\n" my_mac_str;
      Printf.printf "  IP: %s\n" my_ip_str;
      Printf.printf "=================================================\n%!";

      let state = init_daemon interface my_mac my_ip in

      (* Open pcap handle *)
      let module Socket = Pcap_socket in
      let sock = Socket.open_socket interface in
      Printf.printf "✓ Opened network interface\n";
      Printf.printf "✓ ARP filter applied\n";
      Printf.printf "✓ Listening for ARP packets...\n\n%!";

      (* Main packet processing loop *)
      let rec packet_loop () =
        match Socket.receive sock with
        | None ->
            (* Timeout - check for pending timeouts *)
            let current = current_time_ms () in
            let (new_ctx, outgoing) =
              process_timeouts state.ctx (timestamp_to_n current)
            in
            state.ctx <- new_ctx;

            (* Send any retry packets *)
            List.iter (fun retry_pkt ->
              let retry_bytes = serialize_arp_packet retry_pkt in
              let retry_payload = coq_list_to_bytes retry_bytes in
              let retry_frame = {
                eth_dst = mac_to_bytes mac_broadcast;
                eth_src = mac_to_bytes state.ctx.Arp.earp_my_mac;
                eth_type = eth_arp_type;
                eth_payload = retry_payload;
              } in
              Socket.send sock (serialize_ethernet_frame retry_frame);
              Printf.printf "→ Sent ARP retry\n%!"
            ) outgoing;

            packet_loop ()

        | Some packet_bytes ->
            (* Parse Ethernet frame *)
            (match parse_ethernet_frame packet_bytes with
            | None ->
                Printf.printf "✗ Failed to parse Ethernet frame\n%!";
                packet_loop ()

            | Some frame when frame.eth_type <> eth_arp_type ->
                (* Not ARP (shouldn't happen with filter) *)
                packet_loop ()

            | Some frame ->
                Printf.printf "\n📥 ARP packet received:\n";
                Printf.printf "   From: %02X:%02X:%02X:%02X:%02X:%02X\n"
                  (Bytes.get_uint8 frame.eth_src 0)
                  (Bytes.get_uint8 frame.eth_src 1)
                  (Bytes.get_uint8 frame.eth_src 2)
                  (Bytes.get_uint8 frame.eth_src 3)
                  (Bytes.get_uint8 frame.eth_src 4)
                  (Bytes.get_uint8 frame.eth_src 5);

                (* Process with verified ARP implementation *)
                (match process_received_packet state frame with
                | None ->
                    Printf.printf "   → No reply generated\n%!"

                | Some reply_bytes ->
                    (* Send reply *)
                    Socket.send sock reply_bytes;
                    Printf.printf "📤 ARP reply sent\n%!"
                );

                packet_loop ()
            )
      in

      (* Set up signal handler for graceful shutdown *)
      Sys.catch_break true;
      begin
        try
          packet_loop ()
        with
        | Sys.Break ->
            Printf.printf "\n\nShutting down...\n%!";
            Socket.close sock;
            Printf.printf "✓ ARP daemon terminated\n%!"
        | e ->
            Printf.printf "\n\nError: %s\n%!" (Printexc.to_string e);
            Socket.close sock;
            raise e
      end

(* Example usage *)
let () =
  if Array.length Sys.argv < 4 then begin
    Printf.printf "Usage: %s <interface> <mac_address> <ip_address>\n" Sys.argv.(0);
    Printf.printf "Example: %s eth0 AA:BB:CC:DD:EE:FF 192.168.1.100\n" Sys.argv.(0);
    exit 1
  end else
    let interface = Sys.argv.(1) in
    let mac = Sys.argv.(2) in
    let ip = Sys.argv.(3) in
    run_daemon interface mac ip
