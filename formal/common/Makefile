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
	counter_bin_load \
	counter_bingray \
	counter_freq_invariant \
	counter_johnson \
	counter_load_clear \
	bin2gray \
	gray2bin \
	grayj2bin \
	glitch_free_n_dff_arn \
	fifo_control \
	fifo_sync \
	fifo_sync_multi \
	fifo_async \
	gaxi_skid_buffer \
	axi_gen_addr \
	dataint_crc_xor_shift \
	dataint_crc_xor_shift_cascade \
	dataint_ecc_hamming \
	cam_tag \
	clock_divider \
	clock_gate_ctrl \
	count_leading_zeros \
	dataint_parity \
	decoder \
	encoder \
	encoder_priority_enable \
	find_first_set \
	find_last_set \
	gaxi_drop_fifo_sync \
	gaxi_fifo_async \
	gaxi_fifo_sync \
	gaxi_regslice \
	gaxi_skid_buffer_async \
	gaxi_skid_buffer_dbldrn \
	gaxi_skid_buffer_struct \
	icg \
	monbus_arbiter

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
	@echo "  Counters:    counter, counter-load, counter-gray, counter-freq,"
	@echo "               counter-johnson, counter-lc"
	@echo "  Gray code:   bin2gray, gray2bin, grayj2bin"
	@echo "  CDC:         glitch-free"
	@echo "  FIFOs:       fifo-ctrl, fifo, fifo-multi, fifo-async, gaxi-skid,"
	@echo "               gaxi-drop-fifo, gaxi-fifo-async, gaxi-fifo-sync,"
	@echo "               gaxi-regslice, gaxi-skid-async, gaxi-skid-dbldrn,"
	@echo "               gaxi-skid-struct"
	@echo "  AXI:         axi-gen-addr, monbus-arbiter"
	@echo "  Integrity:   crc-xor, crc-cascade, ecc, parity"
	@echo "  Logic:       cam-tag, clz, decoder, encoder, encoder-pe, ffs, fls"
	@echo "  Clock:       clk-div, clk-gate, icg"
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
$(eval $(call MODULE_TARGETS,counter_bin_load,counter-load,counter_bin_load.sby))
$(eval $(call MODULE_TARGETS,counter_bingray,counter-gray,counter_bingray.sby))
$(eval $(call MODULE_TARGETS,counter_freq_invariant,counter-freq,counter_freq_invariant.sby))
$(eval $(call MODULE_TARGETS,counter_johnson,counter-johnson,counter_johnson.sby))
$(eval $(call MODULE_TARGETS,counter_load_clear,counter-lc,counter_load_clear.sby))
$(eval $(call MODULE_TARGETS,bin2gray,bin2gray,bin2gray.sby))
$(eval $(call MODULE_TARGETS,gray2bin,gray2bin,gray2bin.sby))
$(eval $(call MODULE_TARGETS,grayj2bin,grayj2bin,grayj2bin.sby))
$(eval $(call MODULE_TARGETS,glitch_free_n_dff_arn,glitch-free,glitch_free_n_dff_arn.sby))
$(eval $(call MODULE_TARGETS,fifo_control,fifo-ctrl,fifo_control.sby))
$(eval $(call MODULE_TARGETS,fifo_sync,fifo,fifo_sync.sby))
$(eval $(call MODULE_TARGETS,fifo_sync_multi,fifo-multi,fifo_sync_multi.sby))
$(eval $(call MODULE_TARGETS,fifo_async,fifo-async,fifo_async.sby))
$(eval $(call MODULE_TARGETS,gaxi_skid_buffer,gaxi-skid,gaxi_skid_buffer.sby))
$(eval $(call MODULE_TARGETS,axi_gen_addr,axi-gen-addr,axi_gen_addr.sby))
$(eval $(call MODULE_TARGETS,dataint_crc_xor_shift,crc-xor,dataint_crc_xor_shift.sby))
$(eval $(call MODULE_TARGETS,dataint_crc_xor_shift_cascade,crc-cascade,dataint_crc_xor_shift_cascade.sby))
$(eval $(call MODULE_TARGETS,dataint_ecc_hamming,ecc,ecc_hamming.sby))
$(eval $(call MODULE_TARGETS,cam_tag,cam-tag,cam_tag.sby))
$(eval $(call MODULE_TARGETS,clock_divider,clk-div,clock_divider.sby))
$(eval $(call MODULE_TARGETS,clock_gate_ctrl,clk-gate,clock_gate_ctrl.sby))
$(eval $(call MODULE_TARGETS,count_leading_zeros,clz,count_leading_zeros.sby))
$(eval $(call MODULE_TARGETS,dataint_parity,parity,dataint_parity.sby))
$(eval $(call MODULE_TARGETS,decoder,decoder,decoder.sby))
$(eval $(call MODULE_TARGETS,encoder,encoder,encoder.sby))
$(eval $(call MODULE_TARGETS,encoder_priority_enable,encoder-pe,encoder_priority_enable.sby))
$(eval $(call MODULE_TARGETS,find_first_set,ffs,find_first_set.sby))
$(eval $(call MODULE_TARGETS,find_last_set,fls,find_last_set.sby))
$(eval $(call MODULE_TARGETS,gaxi_drop_fifo_sync,gaxi-drop-fifo,gaxi_drop_fifo_sync.sby))
$(eval $(call MODULE_TARGETS,gaxi_fifo_async,gaxi-fifo-async,gaxi_fifo_async.sby))
$(eval $(call MODULE_TARGETS,gaxi_fifo_sync,gaxi-fifo-sync,gaxi_fifo_sync.sby))
$(eval $(call MODULE_TARGETS,gaxi_regslice,gaxi-regslice,gaxi_regslice.sby))
$(eval $(call MODULE_TARGETS,gaxi_skid_buffer_async,gaxi-skid-async,gaxi_skid_buffer_async.sby))
$(eval $(call MODULE_TARGETS,gaxi_skid_buffer_dbldrn,gaxi-skid-dbldrn,gaxi_skid_buffer_dbldrn.sby))
$(eval $(call MODULE_TARGETS,gaxi_skid_buffer_struct,gaxi-skid-struct,gaxi_skid_buffer_struct.sby))
$(eval $(call MODULE_TARGETS,icg,icg,icg.sby))
$(eval $(call MODULE_TARGETS,monbus_arbiter,monbus-arbiter,monbus_arbiter.sby))

# Legacy aliases
.PHONY: prove-arbiter cover-arbiter prove-counter cover-counter prove-fifo cover-fifo
prove-arbiter: prove-arbiter-simple
cover-arbiter: cover-arbiter-simple

# --- Aggregates ---
PROVE_ALL = prove-arbiter-simple prove-arbiter-rr prove-arbiter-rrw prove-arbiter-pe \
            prove-counter prove-counter-load prove-counter-gray prove-counter-freq \
            prove-counter-johnson prove-counter-lc \
            prove-bin2gray prove-gray2bin prove-grayj2bin \
            prove-glitch-free \
            prove-fifo-ctrl prove-fifo prove-fifo-multi prove-fifo-async prove-gaxi-skid \
            prove-axi-gen-addr \
            prove-crc-xor prove-crc-cascade prove-ecc \
            prove-cam-tag \
            prove-clk-div prove-clk-gate prove-icg \
            prove-clz prove-parity \
            prove-decoder prove-encoder prove-encoder-pe \
            prove-ffs prove-fls \
            prove-gaxi-drop-fifo prove-gaxi-fifo-async prove-gaxi-fifo-sync \
            prove-gaxi-regslice prove-gaxi-skid-async prove-gaxi-skid-dbldrn \
            prove-gaxi-skid-struct \
            prove-monbus-arbiter

COVER_ALL = cover-arbiter-simple cover-arbiter-rr cover-arbiter-rrw cover-arbiter-pe \
            cover-counter cover-counter-load cover-counter-gray cover-counter-freq \
            cover-counter-johnson cover-counter-lc \
            cover-bin2gray cover-gray2bin cover-grayj2bin \
            cover-glitch-free \
            cover-fifo-ctrl cover-fifo cover-fifo-multi cover-fifo-async cover-gaxi-skid \
            cover-axi-gen-addr \
            cover-crc-xor cover-crc-cascade cover-ecc \
            cover-cam-tag \
            cover-clk-div cover-clk-gate cover-icg \
            cover-clz cover-parity \
            cover-decoder cover-encoder cover-encoder-pe \
            cover-ffs cover-fls \
            cover-gaxi-drop-fifo cover-gaxi-fifo-async cover-gaxi-fifo-sync \
            cover-gaxi-regslice cover-gaxi-skid-async cover-gaxi-skid-dbldrn \
            cover-gaxi-skid-struct \
            cover-monbus-arbiter

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
