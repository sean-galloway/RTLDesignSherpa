# Filelist for monbus_burst_writer
# Location: rtl/amba/filelists/monbus_burst_writer.f
#
# The continuous FSM-free burst writer lifted out of monbus_group_core
# (2026-10-23) so monbus_group_core_1wr can run one per address window.

-f $REPO_ROOT/rtl/amba/filelists/reset_defs.f
+incdir+$REPO_ROOT/rtl/amba/includes
-f $REPO_ROOT/rtl/math/filelists/math_adder_carry_save_nbit.f
-f $REPO_ROOT/rtl/math/filelists/math_mod_3_compress.f
$REPO_ROOT/rtl/amba/ocelus/monbus_burst_writer.sv
