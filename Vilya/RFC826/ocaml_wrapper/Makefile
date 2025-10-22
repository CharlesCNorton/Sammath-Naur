OCAMLC = ocamlc.opt.exe
OCAMLOPT = ocamlopt.opt.exe
OCAMLDEP = ocamldep.opt.exe
GCC = gcc

OCAML_BIN = C:/Users/cnort/AppData/Roaming/npm/node_modules/esy/node_modules/@prometheansacrifice/esy-bash/.cygwin/bin
OCAMLC_FULL = $(OCAML_BIN)/$(OCAMLC)
OCAMLOPT_FULL = $(OCAML_BIN)/$(OCAMLOPT)
OCAMLDEP_FULL = $(OCAML_BIN)/$(OCAMLDEP)

COQC = "C:/Coq-Platform~8.19~2024.10/bin/coqc.exe"

OCAML_INCLUDE = $(shell $(OCAMLC_FULL) -where)
CFLAGS = -I$(OCAML_INCLUDE) -fPIC -Wall -Wextra -O2
OCAMLFLAGS = -w +a-4-42-44-48 -warn-error -a
OCAMLOPTFLAGS = $(OCAMLFLAGS) -O3 -inline 100

SRC_DIR = src
STUB_DIR = stubs
BUILD_DIR = _build
TARGET = arp_daemon

C_STUBS = $(STUB_DIR)/network_stubs.c
C_OBJS = $(BUILD_DIR)/network_stubs.o

ML_SOURCES = \
	$(SRC_DIR)/network_io.ml \
	$(SRC_DIR)/arp_bridge.ml \
	$(SRC_DIR)/arp_daemon.ml

MLI_SOURCES = $(ML_SOURCES:.ml=.mli)

CMO_OBJS = $(ML_SOURCES:$(SRC_DIR)/%.ml=$(BUILD_DIR)/%.cmo)
CMX_OBJS = $(ML_SOURCES:$(SRC_DIR)/%.ml=$(BUILD_DIR)/%.cmx)

.PHONY: all clean bytecode native extract test install help dirs

all: dirs native

help:
	@echo "ARP Daemon Build System"
	@echo "======================="
	@echo ""
	@echo "Targets:"
	@echo "  all       - Build native code executable (default)"
	@echo "  bytecode  - Build bytecode executable"
	@echo "  native    - Build native code executable"
	@echo "  extract   - Extract OCaml code from Coq proofs"
	@echo "  clean     - Remove build artifacts"
	@echo "  test      - Run test suite"
	@echo "  install   - Install daemon to /usr/local/bin"
	@echo ""
	@echo "Usage:"
	@echo "  make         # Build native executable"
	@echo "  make extract # Extract from Coq first"
	@echo "  make test    # Run tests"

dirs:
	@mkdir -p $(BUILD_DIR)

$(BUILD_DIR)/network_stubs.o: $(C_STUBS) | dirs
	@echo "Compiling C stubs..."
	$(GCC) $(CFLAGS) -c $(C_STUBS) -o $(BUILD_DIR)/network_stubs.o

$(BUILD_DIR)/%.cmi: $(SRC_DIR)/%.mli | dirs
	@echo "Compiling interface $<..."
	$(OCAMLC_FULL) $(OCAMLFLAGS) -c $< -o $@

$(BUILD_DIR)/%.cmo: $(SRC_DIR)/%.ml | dirs
	@echo "Compiling bytecode $<..."
	$(OCAMLC_FULL) $(OCAMLFLAGS) -c $< -o $@

$(BUILD_DIR)/%.cmx: $(SRC_DIR)/%.ml | dirs
	@echo "Compiling native $<..."
	$(OCAMLOPT_FULL) $(OCAMLOPTFLAGS) -c $< -o $@

bytecode: $(C_OBJS) $(CMO_OBJS)
	@echo "Linking bytecode executable..."
	$(OCAMLC_FULL) $(OCAMLFLAGS) -custom unix.cma \
		$(C_OBJS) $(CMO_OBJS) -o $(BUILD_DIR)/$(TARGET).byte

native: $(C_OBJS) $(CMX_OBJS)
	@echo "Linking native executable..."
	$(OCAMLOPT_FULL) $(OCAMLOPTFLAGS) unix.cmxa \
		$(C_OBJS) $(CMX_OBJS) -o $(BUILD_DIR)/$(TARGET)

extract:
	@echo "Extracting OCaml from Coq proofs..."
	cd .. && $(COQC) RFC826.v
	@if [ -f ../arp.ml ]; then \
		echo "Extraction successful: arp.ml created"; \
		echo "Note: Integration with extracted code requires additional work"; \
	else \
		echo "Warning: Extraction did not produce arp.ml"; \
	fi

deps:
	@echo "Generating dependencies..."
	$(OCAMLDEP_FULL) $(ML_SOURCES) > .depend

test: native
	@echo "Running test suite..."
	@echo "Note: Tests require root privileges for raw sockets"
	@if [ $$(id -u) -ne 0 ]; then \
		echo "Error: Tests must be run as root"; \
		exit 1; \
	fi
	@echo "Test mode - monitoring ARP traffic..."
	$(BUILD_DIR)/$(TARGET) --test -i eth0

install: native
	@echo "Installing $(TARGET)..."
	@if [ $$(id -u) -ne 0 ]; then \
		echo "Error: Installation requires root privileges"; \
		exit 1; \
	fi
	install -m 755 $(BUILD_DIR)/$(TARGET) /usr/local/bin/$(TARGET)
	@echo "Installed to /usr/local/bin/$(TARGET)"

clean:
	@echo "Cleaning build artifacts..."
	rm -rf $(BUILD_DIR)
	rm -f .depend
	rm -f ../arp.ml ../arp.mli

-include .depend
