CWD=$(shell pwd)
COCOTB_REDUCED_LOG_FMT = True
SIM ?= icarus
VERILOG_INCLUDE_DIRS = $(REPO_ROOT)/rtl/common
VERILOG_SOURCES =\
					$(REPO_ROOT)/rtl/common/dataint_crc_xor_shift.sv \
					$(REPO_ROOT)/rtl/common/dataint_crc_xor_shift_cascade.sv \
					$(REPO_ROOT)/rtl/common/dataint_crc.sv
DUT = dataint_crc
MODULE = testbench
TOPLEVEL = $(DUT)

COMPILE_ARGS += -P $(DUT).DATA_WIDTH=8
COMPILE_ARGS += -P $(DUT).CRC_WIDTH=8
COMPILE_ARGS += -P $(DUT).CRC_POLY="8'h07"
COMPILE_ARGS += -P $(DUT).CRC_POLY_INITIAL="8'h00"
COMPILE_ARGS += -P $(DUT).REFLECTED_INPUT=0
COMPILE_ARGS += -P $(DUT).REFLECTED_OUTPUT=0
COMPILE_ARGS += -P $(DUT).XOR_OUTPUT="32'h00"

TOPLEVEL_LANG := verilog
COCOTB_HDL_TIMEUNIT=1ns
COCOTB_HDL_TIMEPRECISION=1ps
include $(shell cocotb-config --makefiles)/Makefile.sim
include ../cleanall.mk
WAVES=1
export SEED=1234
