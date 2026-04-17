# sv2v preprocessing for counter_freq_invariant
# Yosys can't parse SV function return statements
REPO_ROOT := $(shell git rev-parse --show-toplevel)
SV2V := sv2v
INC := -I$(REPO_ROOT)/rtl/amba/includes

SRCS := $(REPO_ROOT)/rtl/common/counter_load_clear.sv \
        $(REPO_ROOT)/rtl/common/counter_freq_invariant.sv

.PHONY: prove cover clean

counter_freq_invariant_flat.v: $(SRCS)
	$(SV2V) $(INC) $(SRCS) > $@

prove: counter_freq_invariant_flat.v
	sby -f counter_freq_invariant.sby prove

cover: counter_freq_invariant_flat.v
	sby -f counter_freq_invariant.sby cover

clean:
	rm -rf *_flat.v *_prove *_cover
