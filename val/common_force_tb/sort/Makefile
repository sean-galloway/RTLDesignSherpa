CWD=$(shell pwd)
COCOTB_REDUCED_LOG_FMT = True
SIM ?= icarus
VERILOG_INCLUDE_DIRS = $(CWD)/../../../rtl/common
VERILOG_SOURCES =\
					../../../rtl/common/sort.sv
DUT = sort
MODULE = testbench
TOPLEVEL = $(DUT)

COMPILE_ARGS += -P $(DUT).NUM_VALS=10
COMPILE_ARGS += -P $(DUT).SIZE=16

TOPLEVEL_LANG := verilog
COCOTB_HDL_TIMEUNIT=1ns
COCOTB_HDL_TIMEPRECISION=1ps
include $(shell cocotb-config --makefiles)/Makefile.sim
include ../cleanall.mk
WAVES=1
