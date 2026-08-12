# APBX Crossbar 2to2 Mixed File List
# Location: projects/components/apbx-xbar/rtl/filelists/core/apbx_xbar_2to2_mixed.f
# Purpose: Mixed-version crossbar (m0=APB4, m1=APB5, s0=APB5, s1=APB4)
#
# APB5 ports use the apb5_slave / apb5_master boundary IP; their
# closures come in via the amba-owned filelists.

-f $REPO_ROOT/projects/components/apbx-xbar/rtl/filelists/core/apbx_xbar_common.f
-f $REPO_ROOT/rtl/amba/filelists/apb5_slave.f
-f $REPO_ROOT/rtl/amba/filelists/apb5_master.f

$REPO_ROOT/projects/components/apbx-xbar/rtl/apbx_xbar_2to2_mixed.sv
