CWD=$(shell pwd)
COCOTB_REDUCED_LOG_FMT = True
SIM ?= icarus
SIM_ARGS=-v

VERILOG_INCLUDE_DIRS = $(CWD)/../../../rtl/common
VERILOG_SOURCES = \
					$(CWD)/../../../rtl/common/counter_bin.sv \
					$(CWD)/../../../rtl/common/counter_gray.sv \
					$(CWD)/../../../rtl/common/gray2bin.sv \
					$(CWD)/../../../rtl/common/glitch_free_n_dff_arn.sv \
					$(CWD)/../../../rtl/common/async_fifo.sv

DUT = async_fifo
MODULE = testbench
TOPLEVEL = $(DUT)

COMPILE_ARGS += -P $(DUT).DEPTH=8
COMPILE_ARGS += -P $(DUT).DATA_WIDTH=8
COMPILE_ARGS += -P $(DUT).ALMOST_WR_MARGIN=2
COMPILE_ARGS += -P $(DUT).ALMOST_RD_MARGIN=2

TOPLEVEL_LANG := verilog
COCOTB_HDL_TIMEUNIT=1ns
COCOTB_HDL_TIMEPRECISION=1ps
include $(shell cocotb-config --makefiles)/Makefile.sim
include ../cleanall.mk
WAVES=1