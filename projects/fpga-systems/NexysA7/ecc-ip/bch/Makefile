#==============================================================================
# bch on the Nexys A7 -- small-profile entry point
#==============================================================================
# The harness lives in ONE place: projects/fpga-systems/Genesys2/ecc-ip/bch
# builds both boards' images (the Genesys 2 full-size profile and the A7
# small profile share RTL, DV, host programs, and campaign sequences).
# This directory owns nothing of its own; it exists so the NexysA7 area is
# self-describing -- every target forwards there with the small-profile
# knobs preset (BCH_TARGET=nexys_a7_100t BCH_PROFILE=small -> BCH(248,224)
# t=3 shortened from 255 over GF(2^8), 50 MHz fabric divide, BUILD_ID
# "BCHS"). See README.md here and docs/UART_HARNESS.md in the harness.

SELF_DIR := $(patsubst %/,%,$(dir $(abspath $(lastword $(MAKEFILE_LIST)))))
RDS_ROOT := $(if $(REPO_ROOT),$(REPO_ROOT),$(shell git rev-parse --show-toplevel))
HARNESS  := $(RDS_ROOT)/projects/fpga-systems/Genesys2/ecc-ip/bch

.DEFAULT_GOAL := help
.PHONY: help
help:
	@echo "bch on the Nexys A7 -- small-profile entry point"
	@echo ""
	@echo "  Harness + docs: $(HARNESS)"
	@echo "  Every target forwards there with BCH_TARGET=nexys_a7_100t BCH_PROFILE=small."
	@echo ""
	@echo "  make bitstream                 build fpga/bitstream/bch_loop_small.bit"
	@echo "  make program                   JTAG it onto the A7 (board_lock enforced)"
	@echo "  make run SEQUENCES=\"init smoke\"   drive the board over UART"
	@echo "  make lint | sim | timing       same gates as the harness"
	@echo ""
	@echo "  Geometry proven from the board: init reports BCH(248,224) t=3 m=8,"
	@echo "  BUILD_ID BCHS. Campaign evidence: stable/results/ in the harness tree."

# Any other target (bitstream, program, run, lint, sim, ...) belongs to the
# harness. Command-line variables (e.g. SEQUENCES="init smoke") propagate to
# the sub-make through MAKEFLAGS on their own.
%:
	@$(MAKE) --no-print-directory -C $(HARNESS) BCH_TARGET=nexys_a7_100t BCH_PROFILE=small $@

Makefile: ;
%.mk: ;
