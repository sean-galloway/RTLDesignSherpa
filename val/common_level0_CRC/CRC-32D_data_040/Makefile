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

COMPILE_ARGS += -P $(DUT).DATA_WIDTH=40
COMPILE_ARGS += -P $(DUT).CRC_WIDTH=32
COMPILE_ARGS += -P $(DUT).POLY="32'hA833982B"
COMPILE_ARGS += -P $(DUT).POLY_INIT="32'hFFFFFFFF"
COMPILE_ARGS += -P $(DUT).REFIN=1
COMPILE_ARGS += -P $(DUT).REFOUT=1
COMPILE_ARGS += -P $(DUT).XOROUT="32'hFFFFFFFF"

TOPLEVEL_LANG := verilog
COCOTB_HDL_TIMEUNIT=1ns
COCOTB_HDL_TIMEPRECISION=1ps
include $(shell cocotb-config --makefiles)/Makefile.sim
include ../cleanall.mk
WAVES=1
export SEED=1234
