# Filelist for axil5_opt_slave
# Location: rtl/amba/filelists/axil5_opt_slave.f
#
# TEST COLLATERAL. axil5_opt_slave exists so the AXI5-Lite BFMs have a DUT
# whose ports actually carry USER/TRACE/LOOP/MPAM/MECID/NSAID/POISON/LOCK;
# do not instantiate it in a design.
#
# Self-contained: behavioural memory, no skid buffers, no common/ blocks. The
# only dependency is the reset macro header, from the include path below.

+incdir+$REPO_ROOT/rtl/amba/includes

$REPO_ROOT/rtl/amba/axil5/test-modules/axil5_opt_slave.sv
