CWD=$(shell pwd)
COCOTB_REDUCED_LOG_FMT = True
SIM ?= icarus
VERILOG_INCLUDE_DIRS = $(CWD)/../../../rtl/common
VERILOG_SOURCES = \
					$(CWD)/../../../rtl/common/math_adder_half.sv \
					$(CWD)/../../../rtl/common/math_adder_full.sv \
					$(CWD)/../../../rtl/common/math_adder_carry_save.sv \
					$(CWD)/../../../rtl/common/math_multiplier_dadda_tree_16.sv 

DUT = math_multiplier_dadda_tree_16
MODULE = testbench
TOPLEVEL = $(DUT)

#COMPILE_ARGS += -P $(DUT).N=32
#COMPILE_ARGS += -DDEBUG


TOPLEVEL_LANG := verilog
COCOTB_HDL_TIMEUNIT=1ns
COCOTB_HDL_TIMEPRECISION=1ps
include $(shell cocotb-config --makefiles)/Makefile.sim
include ../cleanall.mk
WAVES=1