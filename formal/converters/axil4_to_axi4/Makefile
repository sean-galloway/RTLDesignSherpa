REPO_ROOT := $(shell git rev-parse --show-toplevel)
INCLUDES := $(REPO_ROOT)/rtl/amba/includes

prove:
	sby -f axil4_to_axi4.sby prove

cover:
	sby -f axil4_to_axi4.sby cover

clean:
	rm -rf *_prove *_cover

.PHONY: prove cover clean
