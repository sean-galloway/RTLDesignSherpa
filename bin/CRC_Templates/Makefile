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

COMPILE_ARGS += -P $(DUT).DATA_WIDTH=<data_width>
COMPILE_ARGS += -P $(DUT).CRC_WIDTH=<crc_width>
COMPILE_ARGS += -P $(DUT).POLY=<poly>
COMPILE_ARGS += -P $(DUT).POLY_INIT=<poly_init>
COMPILE_ARGS += -P $(DUT).REFIN=<reflect_in>
COMPILE_ARGS += -P $(DUT).REFOUT=<reflect_out>
COMPILE_ARGS += -P $(DUT).XOROUT=<xor_out>

TOPLEVEL_LANG := verilog
COCOTB_HDL_TIMEUNIT=1ns
COCOTB_HDL_TIMEPRECISION=1ps
include $(shell cocotb-config --makefiles)/Makefile.sim
include ../cleanall.mk
WAVES=1
export SEED=1234
