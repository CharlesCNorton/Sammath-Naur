################################################################################
# Makefile for Formally Verified ARP Daemon
################################################################################

# OCaml compiler paths (adjust for your Cygwin installation)
OCAMLC_PATH = C:/Users/cnort/AppData/Roaming/npm/node_modules/esy/node_modules/@prometheansacrifice/esy-bash/.cygwin/bin
OCAMLC = $(OCAMLC_PATH)/ocamlc.opt.exe
OCAMLOPT = $(OCAMLC_PATH)/ocamlopt.opt.exe
OCAMLDEP = $(OCAMLC_PATH)/ocamldep.opt.exe

# Compiler flags
OCAMLFLAGS = -g -w +A-4-40-42-44-45-48
OCAMLOPTFLAGS = -g -w +A-4-40-42-44-45-48

# Library paths
# Using local SDK copy
PCAP_SDK = npcap-sdk
PCAP_INCLUDE = -I$(PCAP_SDK)/Include
PCAP_LIB = -L$(PCAP_SDK)/Lib/x64 -lwpcap -lPacket -lws2_32 -liphlpapi

# Build targets
SOURCES = pcap.ml arp.ml arp_daemon.ml
INTERFACES = pcap.mli arp.mli
C_STUBS = pcap_stubs.c
C_OBJECTS = pcap_stubs.o
TARGET = arp_daemon.exe
LIST_DEVICES = list_devices.exe

.PHONY: all clean test extract

all: $(TARGET) $(LIST_DEVICES)

# Extract verified ARP code from Coq
extract:
	@echo "Extracting verified ARP implementation from Coq..."
	"C:/Coq-Platform~8.19~2024.10/bin/coqc.exe" RFC826.v
	@echo "Extraction complete!"

# Compile C stubs to object file
pcap_stubs.o: pcap_stubs.c
	@echo "Compiling C stubs..."
	gcc -c -O2 pcap_stubs.c $(PCAP_INCLUDE) -o pcap_stubs.o

# Compile OCaml interfaces
%.cmi: %.mli
	$(OCAMLC) $(OCAMLFLAGS) -c $<

# Compile OCaml implementations
%.cmo: %.ml %.cmi
	$(OCAMLC) $(OCAMLFLAGS) -c $<

%.cmx: %.ml
	$(OCAMLOPT) $(OCAMLOPTFLAGS) -c $<

# Build bytecode version
$(TARGET:.exe=.byte): pcap.cmo arp.cmo arp_daemon.cmo pcap_stubs.o
	@echo "Building bytecode executable..."
	$(OCAMLC) $(OCAMLFLAGS) -custom -o $@ \
		unix.cma pcap.cmo arp.cmo arp_daemon.cmo \
		pcap_stubs.o $(PCAP_LIB)

# Build native version (recommended for production)
$(TARGET): pcap.cmx arp.cmx arp_daemon.cmx pcap_stubs.o
	@echo "Building native executable..."
	$(OCAMLOPT) $(OCAMLOPTFLAGS) -o $@ \
		unix.cmxa nums.cmxa pcap.cmx arp.cmx arp_daemon.cmx \
		pcap_stubs.o $(PCAP_LIB)

# Build network device listing utility
$(LIST_DEVICES): pcap.cmx list_devices.ml pcap_stubs.o
	@echo "Building device listing utility..."
	$(OCAMLOPT) $(OCAMLOPTFLAGS) -o $@ \
		unix.cmxa pcap.cmx list_devices.ml \
		pcap_stubs.o $(PCAP_LIB)
	@echo ""
	@echo "═══════════════════════════════════════════════════════════"
	@echo "  Build successful!"
	@echo "═══════════════════════════════════════════════════════════"
	@echo "  Main executable: $(TARGET)"
	@echo "  Device lister:   $(LIST_DEVICES)"
	@echo ""
	@echo "  To list network interfaces:"
	@echo "    $(LIST_DEVICES)"
	@echo ""
	@echo "  To run ARP daemon:"
	@echo "    $(TARGET) <interface> <mac> <ip>"
	@echo ""
	@echo "  Example:"
	@echo "    $(TARGET) \"\\Device\\NPF_{GUID}\" AA:BB:CC:DD:EE:FF 192.168.1.100"
	@echo ""
	@echo "  Requirements:"
	@echo "    • Npcap installed (https://npcap.com)"
	@echo "    • Administrator/root privileges"
	@echo "═══════════════════════════════════════════════════════════"

# Dependencies
.depend: $(SOURCES) $(INTERFACES)
	$(OCAMLDEP) $(SOURCES) $(INTERFACES) > .depend

-include .depend

# Clean build artifacts
clean:
	rm -f *.cmi *.cmo *.cmx *.o *.cma *.cmxa *.a $(TARGET) $(TARGET:.exe=.byte) $(LIST_DEVICES)
	rm -f .depend

# Test compilation only
test: all
	@echo "Build test successful!"

# Helper: List network interfaces (requires separate utility)
list-interfaces:
	@echo "Detecting network interfaces..."
	@echo "(This requires building the device listing utility)"
	@echo ""
	@echo "On Windows, use:"
	@echo "  getmac /v /fo list"
	@echo "  or ipconfig /all"

# Development: Quick build for testing
dev: extract
	$(MAKE) $(TARGET)
