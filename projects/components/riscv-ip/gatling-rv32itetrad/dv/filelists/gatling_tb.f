# SPDX-License-Identifier: MIT
# DV filelist for gatling-rv32itetrad: the TB tops on top of the RTL closure.
# RTL sources come in through the RTL master filelist (gatling_all.f); only
# TBs live here.
-f $GATLING_ROOT/rtl/filelists/gatling_all.f
$GATLING_ROOT/dv/tb/gatling_tb_top.sv
$GATLING_ROOT/dv/tb/gatling_bram_tb_top.sv
