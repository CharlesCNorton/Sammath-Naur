open Network_io_stub
open Arp_bridge

type daemon_state = {
  mutable ctx: coq_arp_context;
  socket: raw_socket;
  mutable running: bool;
  mutable stats_received: int;
  mutable stats_sent: int;
  mutable stats_errors: int;
}

let create_daemon_state interface ttl =
  let socket = open_arp_socket ~timeout:1 interface in
  let ctx = create_initial_context socket.mac_addr socket.ip_addr ttl in
  {
    ctx;
    socket;
    running = true;
    stats_received = 0;
    stats_sent = 0;
    stats_errors = 0;
  }

let handle_signal state signum =
  Printf.printf "\nReceived signal %d, shutting down...\n" signum;
  state.running <- false

let print_statistics state =
  Printf.printf "\n=== ARP Daemon Statistics ===\n";
  Printf.printf "Packets received: %d\n" state.stats_received;
  Printf.printf "Packets sent:     %d\n" state.stats_sent;
  Printf.printf "Errors:           %d\n" state.stats_errors;
  Printf.printf "\n";
  print_cache state.ctx;
  flush stdout

let sync_cache_to_kernel state =
  List.iter (fun entry ->
    try
      let ip_bytes = coq_ipv4_to_bytes entry.ace_ip in
      let mac_bytes = coq_mac_to_bytes entry.ace_mac in
      sync_arp_entry_to_kernel state.socket ip_bytes mac_bytes
    with exn ->
      Printf.eprintf "Warning: Failed to sync cache entry: %s\n"
        (Printexc.to_string exn);
      flush stderr
  ) (get_cache_entries state.ctx)

let packet_receive_loop state process_packet_fn =
  Printf.printf "Starting ARP packet receive loop on %s...\n" state.socket.interface;
  Printf.printf "  MAC: %s\n" (format_mac state.socket.mac_addr);
  Printf.printf "  IP:  %s\n" (format_ipv4 state.socket.ip_addr);
  Printf.printf "Press Ctrl+C to stop.\n\n";
  flush stdout;

  let last_sync = ref (Unix.time ()) in
  let sync_interval = 60.0 in

  while state.running do
    try
      match receive_arp_frame state.socket with
      | None -> ()
      | Some arp_payload ->
          state.stats_received <- state.stats_received + 1;

          let arp_bytes = bytes_to_coq_N_list arp_payload in

          begin match process_packet_fn state.ctx arp_bytes with
          | None ->
              Printf.eprintf "Warning: Failed to parse/process ARP packet\n";
              state.stats_errors <- state.stats_errors + 1;
              flush stderr
          | Some (new_ctx, reply_opt) ->
              state.ctx <- new_ctx;

              begin match reply_opt with
              | None -> ()
              | Some reply_bytes ->
                  let reply_payload = coq_N_list_to_bytes reply_bytes in
                  let target_mac = Bytes.make 6 '\xFF' in
                  send_arp_frame state.socket reply_payload target_mac;
                  state.stats_sent <- state.stats_sent + 1;

                  Printf.printf "[%.0f] Sent ARP reply\n" (Unix.time ());
                  flush stdout
              end
          end;

          let current_time = Unix.time () in
          if current_time -. !last_sync > sync_interval then begin
            sync_cache_to_kernel state;
            last_sync := current_time
          end

    with
    | Socket_error msg ->
        Printf.eprintf "Socket error: %s\n" msg;
        state.stats_errors <- state.stats_errors + 1;
        Unix.sleep 1
    | Invalid_packet msg ->
        Printf.eprintf "Invalid packet: %s\n" msg;
        state.stats_errors <- state.stats_errors + 1
    | exn ->
        Printf.eprintf "Unexpected error: %s\n" (Printexc.to_string exn);
        state.stats_errors <- state.stats_errors + 1;
        Unix.sleep 1
  done;

  sync_cache_to_kernel state;
  print_statistics state;
  close_arp_socket state.socket

let parse_and_display_only state arp_bytes =
  Printf.printf "[%.0f] Received ARP packet (%d bytes)\n"
    (Unix.time ())
    (List.length arp_bytes);
  Printf.printf "  Raw bytes: ";
  List.iter (Printf.printf "%02x ") arp_bytes;
  Printf.printf "\n";
  flush stdout;
  Some (state, None)

let main () =
  let interface = ref "eth0" in
  let daemon_mode = ref false in
  let ttl = ref 300 in
  let test_mode = ref false in

  let usage = "Usage: arp_daemon [options]" in
  let specs = [
    ("-i", Arg.Set_string interface, "<iface> Network interface (default: eth0)");
    ("-d", Arg.Set daemon_mode, " Run as daemon");
    ("-t", Arg.Set_int ttl, "<seconds> ARP cache TTL (default: 300)");
    ("--test", Arg.Set test_mode, " Test mode - only display packets, don't process");
  ] in

  Arg.parse specs (fun _ -> ()) usage;

  if Unix.geteuid () <> 0 then begin
    Printf.eprintf "Error: This program requires root privileges.\n";
    Printf.eprintf "Please run with sudo.\n";
    exit 1
  end;

  try
    let state = create_daemon_state !interface !ttl in

    Sys.set_signal Sys.sigint (Sys.Signal_handle (handle_signal state));
    Sys.set_signal Sys.sigterm (Sys.Signal_handle (handle_signal state));

    if !daemon_mode then begin
      Printf.printf "Daemonizing...\n";
      flush stdout;
      if Unix.fork () <> 0 then exit 0;
      ignore (Unix.setsid ());
      if Unix.fork () <> 0 then exit 0;
      Unix.chdir "/";
      Unix.close Unix.stdin;
      Unix.close Unix.stdout;
      Unix.close Unix.stderr;
    end;

    if !test_mode then begin
      Printf.printf "Running in TEST MODE - packets will be displayed but not processed\n";
      packet_receive_loop state parse_and_display_only
    end else begin
      Printf.printf "Note: Coq extraction not yet linked - running in bridge mode\n";
      Printf.printf "To enable full verification, extract RFC826.v and link arp.ml\n";
      packet_receive_loop state parse_and_display_only
    end

  with
  | Socket_error msg ->
      Printf.eprintf "Fatal socket error: %s\n" msg;
      exit 1
  | exn ->
      Printf.eprintf "Fatal error: %s\n" (Printexc.to_string exn);
      Printexc.print_backtrace stderr;
      exit 1

let () = main ()
