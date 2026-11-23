REPO_ROOT ?= $(shell git rev-parse --show-toplevel)
SV2V ?= sv2v
FLAT := monitor_trans_cam_flat.v
FLAT_FILELIST := $(REPO_ROOT)/rtl/amba/filelists/monitor_trans_cam.f
include $(REPO_ROOT)/make/formal_flat.mk

.PHONY: prove clean
prove: monitor_trans_cam_flat.v monitor_trans_cam_gold_flat.v
	sby -f monitor_trans_cam.sby prove

monitor_trans_cam_gold_flat.v: monitor_trans_cam_gold.sv
	$(SV2V) -I$(REPO_ROOT)/rtl/amba/includes $< | cat > $@.tmp
	mv $@.tmp $@

clean:
	rm -rf monitor_trans_cam_flat.v monitor_trans_cam_gold_flat.v monitor_trans_cam_prove
