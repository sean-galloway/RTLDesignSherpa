# Reference-cache rig (cache-ip common-ip TASK-003): harness AXIL tests.
# Usage: make clean-all && make run-all-{gate,func,full}-parallel
AREA        := ref-g2
RDS_ROOT    := $(if $(REPO_ROOT),$(REPO_ROOT),$(shell git rev-parse --show-toplevel))
include $(RDS_ROOT)/make/tests.mk
