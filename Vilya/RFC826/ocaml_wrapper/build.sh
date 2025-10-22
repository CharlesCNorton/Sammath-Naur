#!/bin/bash
set -e

echo "=== Building ARP Daemon with Formally Verified Core ==="
echo ""

OCAMLC=${OCAMLC:-ocamlc}
OCAMLOPT=${OCAMLOPT:-ocamlopt}
GCC=${GCC:-gcc}

echo "Step 1: Compiling C stubs..."
mkdir -p _build
$GCC -I$(ocamlc -where) -fPIC -Wall -Wextra -O2 -c stubs/network_stubs.c -o _build/network_stubs.o

echo "Step 2: Compiling OCaml modules..."
$OCAMLC -c src/network_io.ml -o _build/network_io.cmo
$OCAMLC -c src/arp_bridge.ml -o _build/arp_bridge.cmo
$OCAMLC -c src/arp_daemon.ml -o _build/arp_daemon.cmo

echo "Step 3: Linking bytecode executable..."
$OCAMLC -custom unix.cma _build/network_stubs.o _build/network_io.cmo _build/arp_bridge.cmo _build/arp_daemon.cmo -o _build/arp_daemon.byte

echo ""
echo "Build complete!"
echo "Bytecode executable: _build/arp_daemon.byte"
echo ""
echo "To run (requires root):"
echo "  sudo ./_build/arp_daemon.byte -i eth0"
