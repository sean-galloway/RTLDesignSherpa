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
COMPILE_ARGS += -P $(DUT).CRC_WIDTH=64
COMPILE_ARGS += -P $(DUT).POLY="64'hAD93D23594C935A9"
COMPILE_ARGS += -P $(DUT).POLY_INIT="64'h00000000000000"
COMPILE_ARGS += -P $(DUT).REFIN=1
COMPILE_ARGS += -P $(DUT).REFOUT=1
COMPILE_ARGS += -P $(DUT).XOROUT="64'h00000000000000"

TOPLEVEL_LANG := verilog
COCOTB_HDL_TIMEUNIT=1ns
COCOTB_HDL_TIMEPRECISION=1ps
include $(shell cocotb-config --makefiles)/Makefile.sim
include ../cleanall.mk
WAVES=1
export SEED=1234
