# APB Crossbar Thin File List
# Location: projects/components/apb_xbar/rtl/filelists/core/apb_xbar_thin.f
# Purpose: Parametric "thin" APB crossbar (arbitrary MxN via parameters)
#
# Unlike apb_xbar_{M}to{N}.sv, which bin/apb_xbar_generator.py emits per
# configuration, apb_xbar_thin is a single hand-written parametric crossbar.
# Consumers: formal/apb_xbar/apb_xbar_thin/ and rtl/integ_amba/examples/.

# Include common dependencies
-f $REPO_ROOT/projects/components/apb_xbar/rtl/filelists/core/apb_xbar_common.f

# Thin crossbar module
$REPO_ROOT/projects/components/apb_xbar/rtl/apb_xbar_thin.sv
