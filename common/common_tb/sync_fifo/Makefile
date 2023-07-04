CWD=$(shell pwd)
COCOTB_REDUCED_LOG_FMT = True
SIM ?= icarus
VERILOG_INCLUDE_DIRS = $(CWD)/../../../common
VERILOG_SOURCES =$(CWD)/../../../common/sync_fifo.sv
MODULE := testbench
TOPLEVEL := sync_fifo
TOPLEVEL_LANG := verilog
COCOTB_HDL_TIMEUNIT=1ns
COCOTB_HDL_TIMEPRECISION=1ns
include $(shell cocotb-config --makefiles)/Makefile.sim
include ../cleanall.mk
