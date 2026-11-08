# mc_bank_queue vs gaxi_age_fifo_sync (age off): lockstep equivalence of every output (MC-010 row 2)
REPO_ROOT ?= $(shell git rev-parse --show-toplevel)
SV2V      ?= sv2v
FLAT            := bank_queue_flat.v
FLAT_FILELIST   := $(REPO_ROOT)/projects/components/mem-ctrl-ip/common-ip/rtl/filelists/fub/mc_bank_queue.f \
                   $(REPO_ROOT)/rtl/amba/filelists/gaxi_age_fifo_sync.f
include $(REPO_ROOT)/make/formal_flat.mk

.PHONY: prove peek3 small cover all clean
all: prove peek3 small cover
prove: bank_queue_flat.v
	sby -f bank_queue.sby prove
peek3: bank_queue_flat.v
	sby -f bank_queue.sby peek3
small: bank_queue_flat.v
	sby -f bank_queue.sby small
cover: bank_queue_flat.v
	sby -f bank_queue.sby cover
clean:
	rm -rf *_flat.v .flat_build bank_queue_prove bank_queue_peek3 bank_queue_small bank_queue_cover
