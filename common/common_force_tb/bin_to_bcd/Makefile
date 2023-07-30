CWD=$(shell pwd)
COCOTB_REDUCED_LOG_FMT = True
SIM ?= icarus
VERILOG_INCLUDE_DIRS = $(CWD)/../../../common
VERILOG_SOURCES =\
					../../../common/bin_to_bcd.sv
DUT = bin_to_bcd
MODULE = testbench
TOPLEVEL = $(DUT)

COMPILE_ARGS += -P $(DUT).WIDTH=14 -P $(DUT).DIGITS=5

TOPLEVEL_LANG := verilog
COCOTB_HDL_TIMEUNIT=1ns
COCOTB_HDL_TIMEPRECISION=1ps
include $(shell cocotb-config --makefiles)/Makefile.sim
include ../cleanall.mk
WAVES=1
