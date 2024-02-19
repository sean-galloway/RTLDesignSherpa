CWD=$(shell pwd)
COCOTB_REDUCED_LOG_FMT = True
SIM ?= icarus
VERILOG_INCLUDE_DIRS = $(REPO_ROOT)/rtl/common
VERILOG_SOURCES =\
					$(REPO_ROOT)/rtl/common/counter_bin.sv \
					$(REPO_ROOT)/rtl/common/fifo_control.sv \
					$(REPO_ROOT)/rtl/common/fifo_sync.sv \
					$(REPO_ROOT)/rtl/common/find_first_set.sv \
					$(REPO_ROOT)/rtl/common/find_last_set.sv \
					$(REPO_ROOT)/rtl/common/leading_one_trailing_one.sv \
					$(REPO_ROOT)/rtl/common/arbiter_round_robin.sv \
					$(REPO_ROOT)/rtl/common/pwm.sv \
					round_robin_wrapper.sv
DUT = round_robin_wrapper
MODULE = testbench
TOPLEVEL = $(DUT)

COMPILE_ARGS += -P $(DUT).N=4

TOPLEVEL_LANG := verilog
COCOTB_HDL_TIMEUNIT=1ns
COCOTB_HDL_TIMEPRECISION=1ps
include $(shell cocotb-config --makefiles)/Makefile.sim
include ../cleanall.mk
WAVES=1
export SEED=1234
