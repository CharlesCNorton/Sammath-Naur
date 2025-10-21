(******************************************************************************)
(* Network Device Listing Utility                                             *)
(* Lists all available network interfaces for ARP daemon                      *)
(******************************************************************************)

open Pcap

let format_mac mac =
  let b = mac in
  Printf.sprintf "%02X:%02X:%02X:%02X:%02X:%02X"
    (Bytes.get_uint8 b 0)
    (Bytes.get_uint8 b 1)
    (Bytes.get_uint8 b 2)
    (Bytes.get_uint8 b 3)
    (Bytes.get_uint8 b 4)
    (Bytes.get_uint8 b 5)

let () =
  Printf.printf "════════════════════════════════════════════════════════════\n";
  Printf.printf "  Network Interface Detection\n";
  Printf.printf "════════════════════════════════════════════════════════════\n\n";

  try
    let devices = list_devices () in
    Printf.printf "Found %d network interface(s):\n\n" (List.length devices);

    List.iteri (fun i dev ->
      Printf.printf "[%d] %s\n" (i+1) dev;

      (* Try to get MAC address *)
      begin try
        let mac = get_interface_mac dev in
        Printf.printf "    MAC: %s\n" (format_mac mac)
      with _ ->
        Printf.printf "    MAC: (unable to retrieve)\n"
      end;

      Printf.printf "\n"
    ) devices;

    Printf.printf "════════════════════════════════════════════════════════════\n";
    Printf.printf "  To use with ARP daemon:\n";
    Printf.printf "    ./arp_daemon.exe \"<device_name>\" <mac> <ip>\n";
    Printf.printf "════════════════════════════════════════════════════════════\n"

  with Failure msg ->
    Printf.printf "Error: %s\n" msg;
    Printf.printf "\nMake sure Npcap is installed:\n";
    Printf.printf "  https://npcap.com\n";
    exit 1
