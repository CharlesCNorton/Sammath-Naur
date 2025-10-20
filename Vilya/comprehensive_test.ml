open Arp

(* Helper: Build N from int using binary representation *)
let rec n_of_int_real n =
  if n = 0 then N0
  else if n = 1 then Npos XH
  else if n mod 2 = 0 then
    match n_of_int_real (n / 2) with
    | N0 -> N0
    | Npos p -> Npos (XO p)
  else
    match n_of_int_real (n / 2) with
    | N0 -> Npos XH
    | Npos p -> Npos (XI p)

(* Helper: Build MAC from byte array *)
let mac_of_bytes bytes =
  List.map n_of_int_real (Array.to_list bytes)

(* Helper: Build IPv4 from dotted quad *)
let ip_of_quad a b c d =
  { ipv4_a = n_of_int_real a;
    ipv4_b = n_of_int_real b;
    ipv4_c = n_of_int_real c;
    ipv4_d = n_of_int_real d }

(* Helper: N to int for display (approximate for small values) *)
let rec int_of_n = function
  | N0 -> 0
  | Npos p ->
      let rec int_of_positive = function
        | XH -> 1
        | XO p -> 2 * int_of_positive p
        | XI p -> 1 + 2 * int_of_positive p
      in int_of_positive p

let test_count = ref 0
let pass_count = ref 0
let fail_count = ref 0

let test name f =
  incr test_count;
  Printf.printf "Test %d: %s... " !test_count name;
  flush stdout;
  try
    if f () then begin
      incr pass_count;
      print_endline "✓ PASS"
    end else begin
      incr fail_count;
      print_endline "✗ FAIL"
    end
  with e ->
    incr fail_count;
    Printf.printf "✗ EXCEPTION: %s\n" (Printexc.to_string e)

(* ============================================================================
   EDGE CASE TESTS
   ============================================================================ *)

let test_edge_cases () =
  print_endline "\n╔════════════════════════════════════════════╗";
  print_endline "║       EDGE CASE TESTING                    ║";
  print_endline "╚════════════════════════════════════════════╝\n";

  (* Test 1: Zero IP address *)
  test "Zero IP address handling" (fun () ->
    let zero_ip = ip_of_quad 0 0 0 0 in
    let mac = mac_of_bytes [|0x00; 0x11; 0x22; 0x33; 0x44; 0x55|] in
    let probe = make_arp_probe mac zero_ip in
    probe.arp_spa = zero_ip
  );

  (* Test 2: Broadcast MAC *)
  test "Broadcast MAC (FF:FF:FF:FF:FF:FF)" (fun () ->
    let broadcast = mac_of_bytes [|0xFF; 0xFF; 0xFF; 0xFF; 0xFF; 0xFF|] in
    let ip = ip_of_quad 192 168 1 1 in
    let probe = make_arp_probe broadcast ip in
    List.length probe.arp_tha = 6
  );

  (* Test 3: Max IPv4 address (255.255.255.255) *)
  test "Max IPv4 address" (fun () ->
    let max_ip = ip_of_quad 255 255 255 255 in
    let mac = mac_of_bytes [|0x00; 0x11; 0x22; 0x33; 0x44; 0x55|] in
    let packet = make_arp_request mac max_ip max_ip in
    packet.arp_tpa = max_ip
  );

  (* Test 4: Empty cache operations *)
  test "Lookup in empty cache" (fun () ->
    let empty = [] in
    let ip = ip_of_quad 10 0 0 1 in
    lookup_cache empty ip = None
  );

  (* Test 5: Cache with duplicate IPs *)
  test "Add duplicate IP to cache" (fun () ->
    let ip = ip_of_quad 192 168 1 100 in
    let mac1 = mac_of_bytes [|0x00; 0x11; 0x22; 0x33; 0x44; 0x55|] in
    let mac2 = mac_of_bytes [|0xAA; 0xBB; 0xCC; 0xDD; 0xEE; 0xFF|] in
    let cache1 = add_cache_entry [] ip mac1 (n_of_int_real 300) in
    let cache2 = merge_cache_entry cache1 ip mac2 (n_of_int_real 300) in
    (* Should update, not duplicate *)
    List.length cache2 = 1
  );

  (* Test 6: Timer at exact expiration boundary *)
  test "Timer expires at exact boundary" (fun () ->
    let start = n_of_int_real 1000 in
    let duration = n_of_int_real 500 in
    let timer = start_timer duration start in
    timer_expired timer (n_of_int_real 1500) = true
  );

  (* Test 7: Timer just before expiration *)
  test "Timer one tick before expiration" (fun () ->
    let start = n_of_int_real 1000 in
    let duration = n_of_int_real 500 in
    let timer = start_timer duration start in
    timer_expired timer (n_of_int_real 1499) = false
  );

  (* Test 8: Stopped timer never expires *)
  test "Stopped timer with very late time" (fun () ->
    let timer = start_timer (n_of_int_real 1) (n_of_int_real 0) in
    let stopped = stop_timer timer in
    timer_expired stopped (n_of_int_real 999999) = false
  );

  (* Test 9: Flood table - first request always allowed *)
  test "Flood table allows first request" (fun () ->
    let empty = [] in
    let ip = ip_of_quad 10 0 0 1 in
    let (_, allowed) = update_flood_table empty ip (n_of_int_real 1000) in
    allowed = true
  );

  (* Test 10: Flood table - rapid requests from same IP *)
  test "Flood table tracks rapid requests" (fun () ->
    let ip = ip_of_quad 10 0 0 1 in
    let t1 = n_of_int_real 1000 in
    let (table1, _) = update_flood_table [] ip t1 in
    let (table2, _) = update_flood_table table1 ip (n_of_int_real 1001) in
    let (table3, _) = update_flood_table table2 ip (n_of_int_real 1002) in
    List.length table3 = 1
  );

  (* Test 11: Gratuitous ARP has sender = target *)
  test "Gratuitous ARP: spa = tpa" (fun () ->
    let mac = mac_of_bytes [|0x00; 0x11; 0x22; 0x33; 0x44; 0x55|] in
    let ip = ip_of_quad 192 168 1 100 in
    let grat = make_gratuitous_arp mac ip in
    grat.arp_spa = grat.arp_tpa
  );

  (* Test 12: ARP Probe has zero sender IP *)
  test "ARP Probe: spa = 0.0.0.0" (fun () ->
    let mac = mac_of_bytes [|0x00; 0x11; 0x22; 0x33; 0x44; 0x55|] in
    let ip = ip_of_quad 169 254 1 1 in
    let probe = make_arp_probe mac ip in
    probe.arp_spa = ip_of_quad 0 0 0 0
  );

  (* Test 13: Cache aging reduces TTL *)
  test "Cache aging decrements TTL" (fun () ->
    let ip = ip_of_quad 10 0 0 1 in
    let mac = mac_of_bytes [|0x00; 0x11; 0x22; 0x33; 0x44; 0x55|] in
    let cache = add_cache_entry [] ip mac (n_of_int_real 100) in
    let aged = age_cache cache (n_of_int_real 10) in
    List.length aged = 1  (* Entry should still exist *)
  );

  (* Test 14: Cache aging removes expired entries *)
  test "Cache aging removes expired (TTL=0)" (fun () ->
    let ip = ip_of_quad 10 0 0 1 in
    let mac = mac_of_bytes [|0x00; 0x11; 0x22; 0x33; 0x44; 0x55|] in
    let cache = add_cache_entry [] ip mac (n_of_int_real 10) in
    let aged = age_cache cache (n_of_int_real 20) in
    List.length aged = 0  (* Entry should be removed *)
  );

  (* Test 15: Flood table cleanup removes old entries *)
  test "Flood table cleanup removes old" (fun () ->
    let ip = ip_of_quad 10 0 0 1 in
    let (table, _) = update_flood_table [] ip (n_of_int_real 1000) in
    let cleaned = clean_flood_table table (n_of_int_real 20000) in
    List.length cleaned = 0
  );

  ()

(* ============================================================================
   REAL NETWORK PACKET TESTS
   ============================================================================ *)

let test_real_packets () =
  print_endline "\n╔════════════════════════════════════════════╗";
  print_endline "║       REAL NETWORK PACKET TESTS            ║";
  print_endline "╚════════════════════════════════════════════╝\n";

  (* Real ARP Request: "Who has 192.168.1.1? Tell 192.168.1.100" *)
  test "Real ARP Request packet" (fun () ->
    let sender_mac = mac_of_bytes [|0x00; 0x0C; 0x29; 0x3E; 0x43; 0x9A|] in
    let sender_ip = ip_of_quad 192 168 1 100 in
    let target_ip = ip_of_quad 192 168 1 1 in

    let request = make_arp_request sender_mac sender_ip target_ip in

    (* Verify packet structure *)
    request.arp_op = n_of_int_real 1 &&  (* REQUEST *)
    request.arp_sha = sender_mac &&
    request.arp_spa = sender_ip &&
    request.arp_tpa = target_ip
  );

  (* Real ARP Reply *)
  test "Real ARP Reply packet" (fun () ->
    let my_mac = mac_of_bytes [|0x00; 0x50; 0x56; 0xC0; 0x00; 0x08|] in
    let my_ip = ip_of_quad 192 168 1 1 in
    let target_mac = mac_of_bytes [|0x00; 0x0C; 0x29; 0x3E; 0x43; 0x9A|] in
    let target_ip = ip_of_quad 192 168 1 100 in

    let reply = make_arp_reply my_mac my_ip target_mac target_ip in

    reply.arp_op = n_of_int_real 2 &&  (* REPLY *)
    reply.arp_sha = my_mac &&
    reply.arp_spa = my_ip &&
    reply.arp_tha = target_mac &&
    reply.arp_tpa = target_ip
  );

  (* RFC 5227 Gratuitous ARP for 10.0.0.1 *)
  test "RFC 5227 Gratuitous ARP" (fun () ->
    let mac = mac_of_bytes [|0x52; 0x54; 0x00; 0x12; 0x34; 0x56|] in
    let ip = ip_of_quad 10 0 0 1 in
    let grat = make_gratuitous_arp mac ip in
    grat.arp_spa = grat.arp_tpa && grat.arp_spa = ip
  );

  (* RFC 5227 DAD Probe for link-local *)
  test "RFC 5227 DAD Probe for 169.254.x.x" (fun () ->
    let mac = mac_of_bytes [|0x52; 0x54; 0x00; 0xAB; 0xCD; 0xEF|] in
    let link_local = ip_of_quad 169 254 123 45 in
    let probe = make_arp_probe mac link_local in
    probe.arp_spa = ip_of_quad 0 0 0 0 && probe.arp_tpa = link_local
  );

  ()

(* ============================================================================
   PERFORMANCE & SCALABILITY TESTS
   ============================================================================ *)

let test_performance () =
  print_endline "\n╔════════════════════════════════════════════╗";
  print_endline "║       PERFORMANCE & SCALABILITY TESTS      ║";
  print_endline "╚════════════════════════════════════════════╝\n";

  (* Test 1000 cache entries *)
  test "Add 1000 cache entries" (fun () ->
    let rec add_entries cache n =
      if n = 0 then cache
      else
        let ip = ip_of_quad 10 0 (n / 256) (n mod 256) in
        let mac = mac_of_bytes [|0; 0; 0; (n/65536); ((n/256) mod 256); (n mod 256)|] in
        let new_cache = add_cache_entry cache ip mac (n_of_int_real 300) in
        add_entries new_cache (n - 1)
    in
    let start_time = Sys.time () in
    let cache = add_entries [] 1000 in
    let end_time = Sys.time () in
    Printf.printf "(%.3fs) " (end_time -. start_time);
    List.length cache = 1000
  );

  (* Test 1000 lookups *)
  test "Perform 1000 cache lookups" (fun () ->
    let cache = ref [] in
    for i = 1 to 100 do
      let ip = ip_of_quad 10 0 (i / 256) (i mod 256) in
      let mac = mac_of_bytes [|0; 0; 0; 0; i/256; i mod 256|] in
      cache := add_cache_entry !cache ip mac (n_of_int_real 300)
    done;

    let start_time = Sys.time () in
    let found = ref 0 in
    for i = 1 to 1000 do
      let ip = ip_of_quad 10 0 ((i mod 100) / 256) ((i mod 100) mod 256) in
      match lookup_cache !cache ip with
      | Some _ -> incr found
      | None -> ()
    done;
    let end_time = Sys.time () in
    Printf.printf "(%.3fs, found=%d) " (end_time -. start_time) !found;
    !found > 0
  );

  (* Test flood table with many IPs *)
  test "Flood table with 100 different IPs" (fun () ->
    let rec add_floods table n time =
      if n = 0 then table
      else
        let ip = ip_of_quad 192 168 (n / 256) (n mod 256) in
        let (new_table, _) = update_flood_table table ip (n_of_int_real time) in
        add_floods new_table (n - 1) (time + 1)
    in
    let start_time = Sys.time () in
    let table = add_floods [] 100 1000 in
    let end_time = Sys.time () in
    Printf.printf "(%.3fs) " (end_time -. start_time);
    List.length table = 100
  );

  (* Test aging 1000 cache entries *)
  test "Age 1000 cache entries" (fun () ->
    let cache = ref [] in
    for i = 1 to 1000 do
      let ip = ip_of_quad 10 0 (i / 256) (i mod 256) in
      let mac = mac_of_bytes [|0; 0; 0; 0; i/256; i mod 256|] in
      cache := add_cache_entry !cache ip mac (n_of_int_real 1000)
    done;

    let start_time = Sys.time () in
    let aged = age_cache !cache (n_of_int_real 100) in
    let end_time = Sys.time () in
    Printf.printf "(%.3fs) " (end_time -. start_time);
    List.length aged = 1000
  );

  ()

(* ============================================================================
   STATE MACHINE INTEGRATION TESTS
   ============================================================================ *)

let test_state_machine () =
  print_endline "\n╔════════════════════════════════════════════╗";
  print_endline "║       STATE MACHINE INTEGRATION TESTS      ║";
  print_endline "╚════════════════════════════════════════════╝\n";

  (* Complete request-reply cycle *)
  test "Complete ARP request-reply cycle" (fun () ->
    let my_mac = mac_of_bytes [|0x00; 0x50; 0x56; 0xC0; 0x00; 0x01|] in
    let my_ip = ip_of_quad 192 168 1 1 in
    let iface = { if_mac = my_mac; if_ip = my_ip;
                  if_mtu = n_of_int_real 1500; if_up = true } in

    let ctx = {
      earp_my_mac = my_mac;
      earp_my_ip = my_ip;
      earp_cache = [];
      earp_state_data = StateIdle;
      earp_iface = iface;
      earp_flood_table = [];
      earp_last_cache_cleanup = N0
    } in

    let sender_mac = mac_of_bytes [|0x00; 0x0C; 0x29; 0x3E; 0x43; 0x9A|] in
    let sender_ip = ip_of_quad 192 168 1 100 in
    let request = make_arp_request sender_mac sender_ip my_ip in

    let (new_ctx, response) = process_arp_packet_enhanced
      ctx request (n_of_int_real 1000) (n_of_int_real 1) in

    (* Should generate reply AND cache sender *)
    (match response with
     | Some reply -> reply.arp_op = n_of_int_real 2  (* REPLY *)
     | None -> false) &&
    List.length new_ctx.earp_cache = 1
  );

  (* Gratuitous ARP updates cache *)
  test "Gratuitous ARP updates existing entry" (fun () ->
    let my_mac = mac_of_bytes [|0x00; 0x50; 0x56; 0xC0; 0x00; 0x01|] in
    let my_ip = ip_of_quad 192 168 1 1 in
    let other_ip = ip_of_quad 192 168 1 100 in
    let old_mac = mac_of_bytes [|0xAA; 0xBB; 0xCC; 0xDD; 0xEE; 0xFF|] in
    let new_mac = mac_of_bytes [|0x11; 0x22; 0x33; 0x44; 0x55; 0x66|] in

    (* Start with old MAC in cache *)
    let cache = add_cache_entry [] other_ip old_mac (n_of_int_real 300) in

    let iface = { if_mac = my_mac; if_ip = my_ip;
                  if_mtu = n_of_int_real 1500; if_up = true } in
    let ctx = {
      earp_my_mac = my_mac;
      earp_my_ip = my_ip;
      earp_cache = cache;
      earp_state_data = StateIdle;
      earp_iface = iface;
      earp_flood_table = [];
      earp_last_cache_cleanup = N0
    } in

    (* Process gratuitous ARP with new MAC *)
    let grat = make_gratuitous_arp new_mac other_ip in
    let (new_ctx, _) = process_arp_packet_enhanced
      ctx grat (n_of_int_real 2000) (n_of_int_real 1) in

    (* Cache should be updated *)
    List.length new_ctx.earp_cache = 1
  );

  ()

(* ============================================================================
   MAIN TEST RUNNER
   ============================================================================ *)

let () =
  print_endline "\n";
  print_endline "╔══════════════════════════════════════════════════════════╗";
  print_endline "║  RFC 826 ARP - COMPREHENSIVE EXTRACTION TEST SUITE      ║";
  print_endline "╚══════════════════════════════════════════════════════════╝";

  test_edge_cases ();
  test_real_packets ();
  test_performance ();
  test_state_machine ();

  print_endline "\n╔══════════════════════════════════════════════════════════╗";
  Printf.printf "║  TOTAL: %3d tests | PASS: %3d | FAIL: %3d              ║\n"
    !test_count !pass_count !fail_count;
  if !fail_count = 0 then
    print_endline "║                    ALL TESTS PASSED ✓                    ║"
  else
    Printf.printf "║                    %d TESTS FAILED ✗                    ║\n" !fail_count;
  print_endline "╚══════════════════════════════════════════════════════════╝\n";

  exit (if !fail_count = 0 then 0 else 1)
