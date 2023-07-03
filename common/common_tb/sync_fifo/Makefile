CWD=$(shell pwd)
COCOTB_REDUCED_LOG_FMT = True
SIM ?= icarus
# VHDL_SOURCES =$(CWD)/../tinyalu_hdl/vhdl/single_cycle_add_and_xor.vhd \
              $(CWD)/../tinyalu_hdl/vhdl/three_cycle_mult.vhd \
              $(CWD)/../tinyalu_hdl/vhdl/tinyalu.vhd
VERILOG_INCLUDE_DIRS = $(CWD)/../common
VERILOG_SOURCES =$(CWD)/../common/sync_fifo.sv
MODULE := testbench
TOPLEVEL := sync_fifo
TOPLEVEL_LANG := verilog
COCOTB_HDL_TIMEUNIT=1us
COCOTB_HDL_TIMEPRECISION=1us
include $(shell cocotb-config --makefiles)/Makefile.sim
include ../cleanall.mk
