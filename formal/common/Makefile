# ==============================================================================
# Formal Verification - Common Building Blocks
# ==============================================================================
# Usage:
#   make prove-all      Prove all safety properties
#   make cover-all      Run all cover traces
#   make all            Prove + cover everything
#   make clean          Remove generated artifacts
# ==============================================================================

SHELL := /bin/bash

.DEFAULT_GOAL := help

# All module directories with proofs
MODULES = \
	arbiter_round_robin_simple \
	arbiter_round_robin \
	arbiter_round_robin_weighted \
	arbiter_priority_encoder \
	counter_bin \
	counter_bingray \
	counter_johnson \
	bin2gray \
	gray2bin \
	grayj2bin \
	glitch_free_n_dff_arn \
	fifo_sync \
	fifo_async \
	gaxi_skid_buffer \
	axi_gen_addr \
	dataint_crc_xor_shift \
	dataint_crc_xor_shift_cascade \
	dataint_ecc_hamming

.PHONY: help
help:
	@echo "================================================================================"
	@echo "Formal Verification - Common Building Blocks ($(words $(MODULES)) modules)"
	@echo "================================================================================"
	@echo ""
	@echo "ALL:"
	@echo "  make prove-all             Prove ALL modules"
	@echo "  make cover-all             Cover ALL modules"
	@echo "  make all                   Prove + cover everything"
	@echo ""
	@echo "PER-MODULE (prove-X / cover-X):"
	@echo "  Arbiters:    arbiter-simple, arbiter-rr, arbiter-rrw, arbiter-pe"
	@echo "  Counters:    counter, counter-gray, counter-johnson"
	@echo "  Gray code:   bin2gray, gray2bin, grayj2bin"
	@echo "  CDC:         glitch-free"
	@echo "  FIFOs:       fifo, fifo-async, gaxi-skid"
	@echo "  AXI:         axi-gen-addr"
	@echo "  Integrity:   crc-xor, crc-cascade, ecc"
	@echo ""
	@echo "  make clean                 Remove all artifacts"
	@echo "================================================================================"

# --- Helper macro ---
define MODULE_TARGETS
.PHONY: prove-$(2)
prove-$(2):
	@echo "=== Proving $(1) ==="
	cd $(1) && sby -f $(3) prove

.PHONY: cover-$(2)
cover-$(2):
	@echo "=== Cover $(1) ==="
	cd $(1) && sby -f $(3) cover
endef

# --- Per-module targets ---
$(eval $(call MODULE_TARGETS,arbiter_round_robin_simple,arbiter-simple,arbiter_round_robin_simple.sby))
$(eval $(call MODULE_TARGETS,arbiter_round_robin,arbiter-rr,arbiter_round_robin.sby))
$(eval $(call MODULE_TARGETS,arbiter_round_robin_weighted,arbiter-rrw,arbiter_round_robin_weighted.sby))
$(eval $(call MODULE_TARGETS,arbiter_priority_encoder,arbiter-pe,arbiter_priority_encoder.sby))
$(eval $(call MODULE_TARGETS,counter_bin,counter,counter_bin.sby))
$(eval $(call MODULE_TARGETS,counter_bingray,counter-gray,counter_bingray.sby))
$(eval $(call MODULE_TARGETS,counter_johnson,counter-johnson,counter_johnson.sby))
$(eval $(call MODULE_TARGETS,bin2gray,bin2gray,bin2gray.sby))
$(eval $(call MODULE_TARGETS,gray2bin,gray2bin,gray2bin.sby))
$(eval $(call MODULE_TARGETS,grayj2bin,grayj2bin,grayj2bin.sby))
$(eval $(call MODULE_TARGETS,glitch_free_n_dff_arn,glitch-free,glitch_free_n_dff_arn.sby))
$(eval $(call MODULE_TARGETS,fifo_sync,fifo,fifo_sync.sby))
$(eval $(call MODULE_TARGETS,fifo_async,fifo-async,fifo_async.sby))
$(eval $(call MODULE_TARGETS,gaxi_skid_buffer,gaxi-skid,gaxi_skid_buffer.sby))
$(eval $(call MODULE_TARGETS,axi_gen_addr,axi-gen-addr,axi_gen_addr.sby))
$(eval $(call MODULE_TARGETS,dataint_crc_xor_shift,crc-xor,dataint_crc_xor_shift.sby))
$(eval $(call MODULE_TARGETS,dataint_crc_xor_shift_cascade,crc-cascade,dataint_crc_xor_shift_cascade.sby))
$(eval $(call MODULE_TARGETS,dataint_ecc_hamming,ecc,ecc_hamming.sby))

# Legacy aliases
.PHONY: prove-arbiter cover-arbiter prove-counter cover-counter prove-fifo cover-fifo
prove-arbiter: prove-arbiter-simple
cover-arbiter: cover-arbiter-simple

# --- Aggregates ---
PROVE_ALL = prove-arbiter-simple prove-arbiter-rr prove-arbiter-rrw prove-arbiter-pe \
            prove-counter prove-counter-gray prove-counter-johnson \
            prove-bin2gray prove-gray2bin prove-grayj2bin \
            prove-glitch-free \
            prove-fifo prove-fifo-async prove-gaxi-skid \
            prove-axi-gen-addr \
            prove-crc-xor prove-crc-cascade prove-ecc

COVER_ALL = cover-arbiter-simple cover-arbiter-rr cover-arbiter-rrw cover-arbiter-pe \
            cover-counter cover-counter-gray cover-counter-johnson \
            cover-bin2gray cover-gray2bin cover-grayj2bin \
            cover-glitch-free \
            cover-fifo cover-fifo-async cover-gaxi-skid \
            cover-axi-gen-addr \
            cover-crc-xor cover-crc-cascade cover-ecc

.PHONY: prove-all
prove-all: $(PROVE_ALL)
	@echo "=== All $(words $(PROVE_ALL)) proofs complete ==="

.PHONY: cover-all
cover-all: $(COVER_ALL)
	@echo "=== All $(words $(COVER_ALL)) covers complete ==="

.PHONY: all
all: prove-all cover-all

.PHONY: clean
clean:
	@for m in $(MODULES); do \
		rm -rf $$m/$${m}_prove $$m/$${m}_cover 2>/dev/null; \
	done
	rm -rf dataint_ecc_hamming/ecc_hamming_prove dataint_ecc_hamming/ecc_hamming_cover
