CWD=$(shell pwd)
COCOTB_REDUCED_LOG_FMT = True
SIM ?= icarus
VERILOG_INCLUDE_DIRS = $(CWD)/../../../rtl/common
VERILOG_SOURCES =\
					../../../rtl/common/find_first_set.sv \
					../../../rtl/common/find_last_set.sv \
					../../../rtl/common/leading_one_trailing_one.sv \
					../../../rtl/common/arbiter_round_robin.sv 
DUT = arbiter_round_robin
MODULE = testbench
TOPLEVEL = $(DUT)

COMPILE_ARGS += -P $(DUT).CLIENTS=6

TOPLEVEL_LANG := verilog
COCOTB_HDL_TIMEUNIT=1ns
COCOTB_HDL_TIMEPRECISION=1ps
include $(shell cocotb-config --makefiles)/Makefile.sim
include ../cleanall.mk
WAVES=1