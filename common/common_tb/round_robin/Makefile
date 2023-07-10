CWD=$(shell pwd)
COCOTB_REDUCED_LOG_FMT = True
SIM ?= icarus
VERILOG_INCLUDE_DIRS = $(CWD)/../../../common
VERILOG_SOURCES =\
					$(CWD)/../../../common/sync_fifo.sv \
					$(CWD)/../../../common/round_robin_arbiter.sv \
					$(CWD)/../../../common/pwm.sv \
					$(CWD)/../../../common/load_clear_counter.sv \
					$(CWD)/../../../common/priority_encoder_enable.sv \
					$(CWD)/round_robin_wrapper.sv
DUT = round_robin_wrapper
MODULE = testbench
TOPLEVEL = $(DUT)

COMPILE_ARGS += -P $(DUT).N=4

TOPLEVEL_LANG := verilog
COCOTB_HDL_TIMEUNIT=1ns
COCOTB_HDL_TIMEPRECISION=1ps
include $(shell cocotb-config --makefiles)/Makefile.sim
include ../cleanall.mk
WAVES=1