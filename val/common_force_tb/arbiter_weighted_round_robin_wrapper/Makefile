CWD=$(shell pwd)
COCOTB_REDUCED_LOG_FMT = True
SIM ?= icarus
VERILOG_INCLUDE_DIRS = $(CWD)/../../../rtl/common
VERILOG_SOURCES =\
					$(CWD)/../../../rtl/common/counter_bin.sv \
					$(CWD)/../../../rtl/common/fifo_sync.sv \
					$(CWD)/../../../rtl/common/arbiter_fixed_priority.sv \
					$(CWD)/../../../rtl/common/arbiter_round_robin_subinst.sv \
					$(CWD)/../../../rtl/common/arbiter_weighted_round_robin.sv \
					$(CWD)/../../../rtl/common/pwm.sv \
					$(CWD)/weighted_round_robin_wrapper.sv
DUT = weighted_round_robin_wrapper
MODULE = testbench
TOPLEVEL = $(DUT)

COMPILE_ARGS += -P $(DUT).N=4

TOPLEVEL_LANG := verilog
COCOTB_HDL_TIMEUNIT=1ns
COCOTB_HDL_TIMEPRECISION=1ps
include $(shell cocotb-config --makefiles)/Makefile.sim
include ../cleanall.mk
WAVES=1