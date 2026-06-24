#==============================================================================
# flows-idma-bridge — OOC area characterization of PULP iDMA, for apples-to-
# apples comparison against STREAM (see ../reports/area/README.md).
#==============================================================================
# Targets:
#   make setup     clone iDMA + deps (pinned), fetch bender, install py deps
#   make gen       generate iDMA RTL + assemble filelists
#   make area      OOC-synth backend + desc64 frontend + axi mux; print summary
#   make clean     remove build/ and reports/
#==============================================================================
SELF_DIR := $(patsubst %/,%,$(dir $(abspath $(lastword $(MAKEFILE_LIST)))))
VIVADO   ?= vivado
VBATCH    = $(VIVADO) -mode batch -notrace
TCL       = $(SELF_DIR)/tcl/synth_area_idma.tcl
FL        = $(SELF_DIR)/flists
INC       = $(FL)/incdirs.f

# iDMA config pinned to match STREAM's FPGA datapath.
BE_GEN  = DataWidth=128 AddrWidth=32 UserWidth=1 AxiIdWidth=4 NumAxInFlight=8 TFLenWidth=32

.PHONY: setup gen area area-backend area-desc64 area-mux clean

setup:
	$(SELF_DIR)/bin/setup.sh

gen:
	$(SELF_DIR)/bin/gen.sh

area: gen area-backend area-desc64 area-mux
	@echo ""; echo "=== iDMA OOC area (xc7a100t) ==="; \
	for t in backend_rw_axi_dw128 desc64_dw128 axi_mux_8to1_dw128; do \
	  f=$(SELF_DIR)/reports/idma_area_$$t.txt; \
	  [ -f $$f ] && printf "%-26s LUTs=%s FF=%s BRAM=%s\n" "$$t" \
	    "$$(grep -m1 'Slice LUTs' $$f | awk -F'|' '{gsub(/ /,"",$$3);print $$3}')" \
	    "$$(grep -m1 'Slice Registers' $$f | awk -F'|' '{gsub(/ /,"",$$3);print $$3}')" \
	    "$$(grep -m1 'Block RAM Tile' $$f | awk -F'|' '{gsub(/ /,"",$$3);print $$3}')"; \
	done

area-backend:
	cd $(SELF_DIR) && IDMA_TOP=idma_backend_synth_rw_axi IDMA_TAG=backend_rw_axi_dw128 \
	  IDMA_FLISTS="$(FL)/deps.f $(FL)/idma_backend.f" IDMA_INCDIRS=$(INC) \
	  IDMA_GENERICS="$(BE_GEN)" $(VBATCH) -source $(TCL)

area-desc64:
	cd $(SELF_DIR) && IDMA_TOP=idma_desc64_synth IDMA_TAG=desc64_dw128 \
	  IDMA_FLISTS="$(FL)/deps.f $(FL)/idma_desc64.f" IDMA_INCDIRS=$(INC) \
	  $(VBATCH) -source $(TCL)

area-mux:
	cd $(SELF_DIR) && IDMA_TOP=axi_mux_intf IDMA_TAG=axi_mux_8to1_dw128 \
	  IDMA_FLISTS="$(FL)/deps.f $(FL)/axi_mux.f" IDMA_INCDIRS=$(INC) \
	  IDMA_GENERICS="NO_SLV_PORTS=8 AXI_ADDR_WIDTH=32 AXI_DATA_WIDTH=128 SLV_AXI_ID_WIDTH=4 MST_AXI_ID_WIDTH=7 AXI_USER_WIDTH=1" \
	  $(VBATCH) -source $(TCL)

clean:
	rm -rf $(SELF_DIR)/build $(SELF_DIR)/reports/*.txt
