CWD=$(shell pwd)
COCOTB_REDUCED_LOG_FMT = True
SIM ?= icarus
VERILOG_INCLUDE_DIRS = $(CWD)/../../../common
VERILOG_SOURCES =\
					../../../common/sync_fifo.sv \
					../../../common/leading_one_trailing_one.sv \
					../../../common/rrb_arb.sv \
					../../../common/fixed_prio_arb.sv \
					../../../common/weighted_round_robin.sv \
					../../../common/round_robin_arbiter.sv \
					../../../common/pwm.sv \
					../../../common/load_clear_counter.sv \
					../../../common/priority_encoder_enable.sv \
					round_robin_wrapper.sv
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