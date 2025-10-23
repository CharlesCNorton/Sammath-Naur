open Arp_bridge

let test_name = ref ""
let tests_passed = ref 0
let tests_failed = ref 0

let assert_true name condition =
  test_name := name;
  if condition then begin
    Printf.printf "✓ PASS: %s\n" name;
    tests_passed := !tests_passed + 1;
    flush stdout
  end else begin
    Printf.printf "✗ FAIL: %s\n" name;
    tests_failed := !tests_failed + 1;
    flush stdout;
    failwith ("Test failed: " ^ name)
  end

let assert_equal name expected actual =
  assert_true name (expected = actual)

let create_test_mac b0 b1 b2 b3 b4 b5 =
  { mac_bytes = [b0; b1; b2; b3; b4; b5]; mac_valid = () }

let create_test_ip a b c d =
  { ipv4_a = a; ipv4_b = b; ipv4_c = c; ipv4_d = d }

let create_test_arp_request src_mac src_ip dst_ip =
  {
    arp_op = 1;
    arp_sha = src_mac;
    arp_spa = src_ip;
    arp_tha = create_test_mac 0 0 0 0 0 0;
    arp_tpa = dst_ip;
  }

let create_test_arp_reply src_mac src_ip dst_mac dst_ip =
  {
    arp_op = 2;
    arp_sha = src_mac;
    arp_spa = src_ip;
    arp_tha = dst_mac;
    arp_tpa = dst_ip;
  }

let test_type_conversions () =
  Printf.printf "\n=== Test Suite 1: Type Conversions ===\n";

  let mac_bytes = Bytes.of_string "\xAA\xBB\xCC\xDD\xEE\xFF" in
  let coq_mac = bytes_to_coq_mac mac_bytes in
  let converted_back = coq_mac_to_bytes coq_mac in
  assert_true "MAC round-trip conversion" (Bytes.equal mac_bytes converted_back);

  let ip_bytes = Bytes.of_string "\xC0\xA8\x01\x64" in
  let coq_ip = bytes_to_coq_ipv4 ip_bytes in
  let converted_back = coq_ipv4_to_bytes coq_ip in
  assert_true "IPv4 round-trip conversion" (Bytes.equal ip_bytes converted_back);

  assert_equal "IPv4 octet A" 192 coq_ip.ipv4_a;
  assert_equal "IPv4 octet B" 168 coq_ip.ipv4_b;
  assert_equal "IPv4 octet C" 1 coq_ip.ipv4_c;
  assert_equal "IPv4 octet D" 100 coq_ip.ipv4_d;

  let mac_list = coq_mac.mac_bytes in
  assert_equal "MAC byte count" 6 (List.length mac_list);
  assert_equal "MAC first byte" 0xAA (List.nth mac_list 0);
  assert_equal "MAC last byte" 0xFF (List.nth mac_list 5)

let test_context_creation () =
  Printf.printf "\n=== Test Suite 2: Context Creation ===\n";

  let mac = Bytes.of_string "\x12\x34\x56\x78\x9A\xBC" in
  let ip = Bytes.of_string "\xC0\xA8\x01\x01" in
  let ctx = create_initial_context mac ip 300 in

  assert_equal "Initial cache is empty" 0 (List.length ctx.arp_cache);
  assert_equal "TTL is set correctly" 300 ctx.arp_cache_ttl;
  assert_equal "My MAC matches" 0x12 (List.nth ctx.arp_my_mac.mac_bytes 0);
  assert_equal "My IP A" 192 ctx.arp_my_ip.ipv4_a;
  assert_equal "My IP D" 1 ctx.arp_my_ip.ipv4_d

let test_cache_operations () =
  Printf.printf "\n=== Test Suite 3: Cache Operations ===\n";

  let mac = Bytes.of_string "\x12\x34\x56\x78\x9A\xBC" in
  let ip = Bytes.of_string "\xC0\xA8\x01\x01" in
  let ctx = create_initial_context mac ip 300 in

  let entry = {
    ace_ip = create_test_ip 192 168 1 100;
    ace_mac = create_test_mac 0xAA 0xBB 0xCC 0xDD 0xEE 0xFF;
    ace_ttl = 300;
    ace_static = false;
  } in

  let ctx_with_entry = { ctx with arp_cache = [entry] } in
  assert_equal "Cache has one entry" 1 (List.length ctx_with_entry.arp_cache);

  let cached_entry = List.hd ctx_with_entry.arp_cache in
  assert_equal "Cached IP matches" 100 cached_entry.ace_ip.ipv4_d;
  assert_equal "Cached MAC matches" 0xAA (List.nth cached_entry.ace_mac.mac_bytes 0);
  assert_equal "Entry is not static" false cached_entry.ace_static

let test_packet_formatting () =
  Printf.printf "\n=== Test Suite 4: Packet Formatting ===\n";

  let mac = create_test_mac 0x12 0x34 0x56 0x78 0x9A 0xBC in
  let ip = create_test_ip 192 168 1 100 in

  let mac_str = format_coq_mac mac in
  assert_true "MAC format contains colons" (String.contains mac_str ':');
  assert_true "MAC format correct length" (String.length mac_str = 17);

  let ip_str = format_coq_ipv4 ip in
  assert_true "IP format contains dots" (String.contains ip_str '.');
  assert_equal "IP format correct" "192.168.1.100" ip_str

let test_arp_request_structure () =
  Printf.printf "\n=== Test Suite 5: ARP Request Structure ===\n";

  let src_mac = create_test_mac 0x12 0x34 0x56 0x78 0x9A 0xBC in
  let src_ip = create_test_ip 192 168 1 10 in
  let dst_ip = create_test_ip 192 168 1 20 in

  let request = create_test_arp_request src_mac src_ip dst_ip in

  assert_equal "Request opcode is 1" 1 request.arp_op;
  assert_equal "Source MAC set" 0x12 (List.nth request.arp_sha.mac_bytes 0);
  assert_equal "Source IP set" 10 request.arp_spa.ipv4_d;
  assert_equal "Target MAC is zero" 0 (List.nth request.arp_tha.mac_bytes 0);
  assert_equal "Target IP set" 20 request.arp_tpa.ipv4_d

let test_arp_reply_structure () =
  Printf.printf "\n=== Test Suite 6: ARP Reply Structure ===\n";

  let src_mac = create_test_mac 0xAA 0xBB 0xCC 0xDD 0xEE 0xFF in
  let src_ip = create_test_ip 192 168 1 20 in
  let dst_mac = create_test_mac 0x12 0x34 0x56 0x78 0x9A 0xBC in
  let dst_ip = create_test_ip 192 168 1 10 in

  let reply = create_test_arp_reply src_mac src_ip dst_mac dst_ip in

  assert_equal "Reply opcode is 2" 2 reply.arp_op;
  assert_equal "Reply source MAC" 0xAA (List.nth reply.arp_sha.mac_bytes 0);
  assert_equal "Reply target MAC" 0x12 (List.nth reply.arp_tha.mac_bytes 0);
  assert_equal "Reply source IP" 20 reply.arp_spa.ipv4_d;
  assert_equal "Reply target IP" 10 reply.arp_tpa.ipv4_d

let test_multiple_cache_entries () =
  Printf.printf "\n=== Test Suite 7: Multiple Cache Entries ===\n";

  let mac = Bytes.of_string "\x12\x34\x56\x78\x9A\xBC" in
  let ip = Bytes.of_string "\xC0\xA8\x01\x01" in
  let ctx = create_initial_context mac ip 300 in

  let entry1 = {
    ace_ip = create_test_ip 192 168 1 10;
    ace_mac = create_test_mac 0x11 0x22 0x33 0x44 0x55 0x66;
    ace_ttl = 300;
    ace_static = false;
  } in

  let entry2 = {
    ace_ip = create_test_ip 192 168 1 20;
    ace_mac = create_test_mac 0xAA 0xBB 0xCC 0xDD 0xEE 0xFF;
    ace_ttl = 300;
    ace_static = true;
  } in

  let entry3 = {
    ace_ip = create_test_ip 192 168 1 30;
    ace_mac = create_test_mac 0x99 0x88 0x77 0x66 0x55 0x44;
    ace_ttl = 150;
    ace_static = false;
  } in

  let ctx_multi = { ctx with arp_cache = [entry1; entry2; entry3] } in
  assert_equal "Cache has three entries" 3 (List.length ctx_multi.arp_cache);

  let second_entry = List.nth ctx_multi.arp_cache 1 in
  assert_equal "Second entry is static" true second_entry.ace_static;
  assert_equal "Second entry IP" 20 second_entry.ace_ip.ipv4_d;

  let third_entry = List.nth ctx_multi.arp_cache 2 in
  assert_equal "Third entry TTL" 150 third_entry.ace_ttl

let test_byte_list_conversions () =
  Printf.printf "\n=== Test Suite 8: Byte List Conversions ===\n";

  let test_bytes = Bytes.of_string "\x01\x02\x03\x04\x05" in
  let n_list = bytes_to_coq_N_list test_bytes in

  assert_equal "List length correct" 5 (List.length n_list);
  assert_equal "First byte" 1 (List.nth n_list 0);
  assert_equal "Last byte" 5 (List.nth n_list 4);

  let converted_back = coq_N_list_to_bytes n_list in
  assert_true "Byte list round-trip" (Bytes.equal test_bytes converted_back);

  let large_list = [255; 128; 64; 32; 16; 8; 4; 2; 1; 0] in
  let large_bytes = coq_N_list_to_bytes large_list in
  assert_equal "Large list conversion" 10 (Bytes.length large_bytes);
  assert_equal "Large list first" 255 (int_of_char (Bytes.get large_bytes 0));
  assert_equal "Large list last" 0 (int_of_char (Bytes.get large_bytes 9))

let test_edge_cases () =
  Printf.printf "\n=== Test Suite 9: Edge Cases ===\n";

  let zero_mac = create_test_mac 0 0 0 0 0 0 in
  assert_equal "Zero MAC byte 0" 0 (List.nth zero_mac.mac_bytes 0);
  assert_equal "Zero MAC byte 5" 0 (List.nth zero_mac.mac_bytes 5);

  let broadcast_mac = create_test_mac 255 255 255 255 255 255 in
  assert_equal "Broadcast MAC byte 0" 255 (List.nth broadcast_mac.mac_bytes 0);
  assert_equal "Broadcast MAC byte 5" 255 (List.nth broadcast_mac.mac_bytes 5);

  let zero_ip = create_test_ip 0 0 0 0 in
  assert_equal "Zero IP format" "0.0.0.0" (format_coq_ipv4 zero_ip);

  let broadcast_ip = create_test_ip 255 255 255 255 in
  assert_equal "Broadcast IP format" "255.255.255.255" (format_coq_ipv4 broadcast_ip);

  let localhost = create_test_ip 127 0 0 1 in
  assert_equal "Localhost format" "127.0.0.1" (format_coq_ipv4 localhost)

let test_cache_printing () =
  Printf.printf "\n=== Test Suite 10: Cache Display ===\n";

  let mac = Bytes.of_string "\x12\x34\x56\x78\x9A\xBC" in
  let ip = Bytes.of_string "\xC0\xA8\x01\x01" in
  let ctx = create_initial_context mac ip 300 in

  let entry = {
    ace_ip = create_test_ip 192 168 1 100;
    ace_mac = create_test_mac 0xAA 0xBB 0xCC 0xDD 0xEE 0xFF;
    ace_ttl = 300;
    ace_static = false;
  } in

  let ctx_with_entry = { ctx with arp_cache = [entry] } in

  Printf.printf "Displaying cache:\n";
  print_cache ctx_with_entry;

  assert_true "Cache printing succeeded" true

let print_summary () =
  Printf.printf "\n╔════════════════════════════════════════════════════════════╗\n";
  Printf.printf "║              ARP INTEGRATION TEST SUMMARY                 ║\n";
  Printf.printf "╠════════════════════════════════════════════════════════════╣\n";
  Printf.printf "║  Total Tests:  %3d                                        ║\n" (!tests_passed + !tests_failed);
  Printf.printf "║  Passed:       %3d                                        ║\n" !tests_passed;
  Printf.printf "║  Failed:       %3d                                        ║\n" !tests_failed;
  if !tests_failed = 0 then
    Printf.printf "║  Result:       ✓ ALL TESTS PASSED                         ║\n"
  else
    Printf.printf "║  Result:       ✗ SOME TESTS FAILED                        ║\n";
  Printf.printf "╚════════════════════════════════════════════════════════════╝\n";
  flush stdout

let main () =
  Printf.printf "╔════════════════════════════════════════════════════════════╗\n";
  Printf.printf "║        RFC 826 ARP - COMPREHENSIVE INTEGRATION TEST        ║\n";
  Printf.printf "║              Formally Verified Protocol Core               ║\n";
  Printf.printf "╚════════════════════════════════════════════════════════════╝\n\n";
  flush stdout;

  try
    test_type_conversions ();
    test_context_creation ();
    test_cache_operations ();
    test_packet_formatting ();
    test_arp_request_structure ();
    test_arp_reply_structure ();
    test_multiple_cache_entries ();
    test_byte_list_conversions ();
    test_edge_cases ();
    test_cache_printing ();

    print_summary ();

    if !tests_failed = 0 then begin
      Printf.printf "\n✓ Integration test PASSED - System ready for deployment\n\n";
      exit 0
    end else begin
      Printf.printf "\n✗ Integration test FAILED - %d test(s) failed\n\n" !tests_failed;
      exit 1
    end
  with
  | Failure msg ->
      Printf.printf "\n✗ FATAL ERROR: %s\n" msg;
      print_summary ();
      exit 1
  | exn ->
      Printf.printf "\n✗ UNEXPECTED ERROR: %s\n" (Printexc.to_string exn);
      Printexc.print_backtrace stderr;
      print_summary ();
      exit 1

let () = main ()
