CWD=$(shell pwd)
COCOTB_REDUCED_LOG_FMT = True
SIM ?= icarus
VERILOG_INCLUDE_DIRS = $(REPO_ROOT)/rtl/common
VERILOG_SOURCES =\
					$(REPO_ROOT)/rtl/common/crc.sv
DUT = CRC_Component
MODULE = testbench
TOPLEVEL = $(DUT)

COMPILE_ARGS += -P $(DUT).crc_width=8
COMPILE_ARGS += -P $(DUT).polynomial="8'h07"
COMPILE_ARGS += -P $(DUT).polynomial_initial="8'h00"
COMPILE_ARGS += -P $(DUT).reflected_input=0
COMPILE_ARGS += -P $(DUT).reflected_output=0
COMPILE_ARGS += -P $(DUT).xor_output="8'h00"

TOPLEVEL_LANG := verilog
COCOTB_HDL_TIMEUNIT=1ns
COCOTB_HDL_TIMEPRECISION=1ps
include $(shell cocotb-config --makefiles)/Makefile.sim
include ../cleanall.mk
WAVES=1
export SEED=1234
