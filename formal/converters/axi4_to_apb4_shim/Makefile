REPO_ROOT := $(shell git rev-parse --show-toplevel)
SV2V      ?= sv2v

INC := -I$(REPO_ROOT)/rtl/amba/includes

PKGS :=

DEPS := $(REPO_ROOT)/rtl/common/counter_bin.sv \
        $(REPO_ROOT)/rtl/common/fifo_control.sv \
        $(REPO_ROOT)/rtl/amba/gaxi/gaxi_fifo_sync.sv \
        $(REPO_ROOT)/rtl/amba/gaxi/gaxi_skid_buffer.sv \
        $(REPO_ROOT)/rtl/amba/shared/axi_gen_addr.sv \
        $(REPO_ROOT)/rtl/cdc/cdc_2_phase_handshake.sv \
        $(REPO_ROOT)/rtl/cdc/cdc_4_phase_handshake.sv \
        $(REPO_ROOT)/rtl/amba/apb4/apb4_master.sv \
        $(REPO_ROOT)/rtl/amba/apb4/apb4_master_stub.sv \
        $(REPO_ROOT)/rtl/amba/axi4/stubs/axi4_slave_rd_stub.sv \
        $(REPO_ROOT)/rtl/amba/axi4/stubs/axi4_slave_wr_stub.sv \
        $(REPO_ROOT)/rtl/amba/axi4/stubs/axi4_slave_stub.sv \
        $(REPO_ROOT)/projects/components/utility-ip/converters/rtl/axi4_to_apb4_convert.sv

DUT := $(REPO_ROOT)/projects/components/utility-ip/converters/rtl/axi4_to_apb4_shim.sv

.PHONY: prove cover all clean

all: prove cover

prove: axi4_to_apb4_shim_flat.v
	sby -f axi4_to_apb4_shim.sby prove

cover: axi4_to_apb4_shim_flat.v
	sby -f axi4_to_apb4_shim.sby cover

axi4_to_apb4_shim_flat.v: $(DUT) $(DEPS)
	$(SV2V) $(INC) $(PKGS) $(DEPS) $(DUT) > $@

clean:
	rm -rf *_flat.v *_prove *_cover

.PHONY: prove cover clean

# tooling TASK-026: regenerate-and-diff self-detection for the committed flat.
# House pattern from formal/common/counter_freq_invariant; consumed by
# bin/formal_status.py --check-flats (mechanism a) and the pre-commit gate.
# Comparison squeezes whitespace, matching the token normalization the
# checker uses (committed flats may be post-formatter).
.PHONY: check-flat .check_flat_tmp
check-flat: .check_flat_tmp
	@if [ "$$(tr -s '[:space:]' ' ' < .check_flat_tmp)" = "$$(tr -s '[:space:]' ' ' < axi4_to_apb4_shim_flat.v)" ]; then \
		rm -f .check_flat_tmp; \
		echo "flat file is current"; \
	else \
		rm -f .check_flat_tmp; \
		echo "STALE: axi4_to_apb4_shim_flat.v does not match the RTL."; \
		echo "Regenerate with: make axi4_to_apb4_shim_flat.v"; \
		exit 1; \
	fi

.check_flat_tmp: $(DUT) $(DEPS)
	$(SV2V) $(INC) $(PKGS) $(DEPS) $(DUT) > $@

clean:
	rm -rf *_flat.v *_prove *_cover

.PHONY: prove cover clean
