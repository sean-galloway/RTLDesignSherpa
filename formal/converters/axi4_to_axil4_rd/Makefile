REPO_ROOT := $(shell git rev-parse --show-toplevel)
INCLUDES := $(REPO_ROOT)/rtl/amba/includes

prove:
	sby -f axi4_to_axil4_rd.sby prove

cover:
	sby -f axi4_to_axil4_rd.sby cover

clean:
	rm -rf *_prove *_cover

.PHONY: prove cover clean
