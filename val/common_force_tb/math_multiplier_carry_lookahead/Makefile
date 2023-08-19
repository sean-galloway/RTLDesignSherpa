CWD=$(shell pwd)
COCOTB_REDUCED_LOG_FMT = True
SIM ?= icarus
VERILOG_INCLUDE_DIRS = $(CWD)/../../../rtl/common
VERILOG_SOURCES = \
					$(CWD)/../../../rtl/common/math_multiplier_carry_lookahead.sv 

DUT = math_multiplier_carry_lookahead
MODULE = testbench
TOPLEVEL = $(DUT)

COMPILE_ARGS += -P $(DUT).N=8
#COMPILE_ARGS += -DDEBUG


TOPLEVEL_LANG := verilog
COCOTB_HDL_TIMEUNIT=1ns
COCOTB_HDL_TIMEPRECISION=1ps
include $(shell cocotb-config --makefiles)/Makefile.sim
include ../cleanall.mk
WAVES=1