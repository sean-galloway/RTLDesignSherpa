CWD=$(shell pwd)
COCOTB_REDUCED_LOG_FMT = True
SIM ?= icarus
SIM_ARGS=-v -l log.txt

VERILOG_INCLUDE_DIRS = $(CWD)/../../../rtl/common
VERILOG_SOURCES = \
					$(CWD)/../../../rtl/common/find_first_set.sv \
					$(CWD)/../../../rtl/common/find_last_set.sv \
					$(CWD)/../../../rtl/common/leading_one_trailing_one.sv \
					$(CWD)/../../../rtl/common/counter_bin.sv \
					$(CWD)/../../../rtl/common/counter_johnson.sv \
					$(CWD)/../../../rtl/common/grayj2bin.sv \
					$(CWD)/../../../rtl/common/glitch_free_n_dff_arn.sv \
					$(CWD)/../../../rtl/common/async_any_even_fifo.sv

DUT = async_any_even_fifo
MODULE = testbench
TOPLEVEL = $(DUT)

COMPILE_ARGS += -P $(DUT).DEPTH=10
COMPILE_ARGS += -P $(DUT).DATA_WIDTH=8
COMPILE_ARGS += -P $(DUT).ALMOST_WR_MARGIN=2
COMPILE_ARGS += -P $(DUT).ALMOST_RD_MARGIN=2

TOPLEVEL_LANG := verilog
COCOTB_HDL_TIMEUNIT=1ns
COCOTB_HDL_TIMEPRECISION=1ps
include $(shell cocotb-config --makefiles)/Makefile.sim
include ../cleanall.mk
WAVES=1