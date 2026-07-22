# Filelist for monbus_arbiter_grant_hold_dut
# Location: val/amba/filelists/monbus_arbiter_grant_hold_dut.f
#
# Test-only top for val/amba/test_monbus_arbiter_grant_hold.py.
#
# This wrapper used to be appended directly to
# rtl/amba/filelists/monbus_arbiter.f, which meant every consumer that
# -f included the monbus_arbiter component dragged a val/ testbench top
# into its design. A component filelist declares that component's
# closure and nothing else, so the test-only top lives here instead.

-f $REPO_ROOT/rtl/amba/filelists/monbus_arbiter.f

$REPO_ROOT/val/amba/monbus_arbiter_grant_hold_dut.sv
