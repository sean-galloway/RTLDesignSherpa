# APB Crossbar Thin File List
# Location: projects/components/apb4_xbar/rtl/filelists/core/apb4_xbar_thin.f
# Purpose: Parametric "thin" APB crossbar (arbitrary MxN via parameters)
#
# Unlike apb4_xbar_{M}to{N}.sv, which bin/apb4_xbar_generator.py emits per
# configuration, apb4_xbar_thin is a single hand-written parametric crossbar.
# Consumers: formal/apb4_xbar/apb4_xbar_thin/ and rtl/integ_amba/examples/.

# Include common dependencies
-f $REPO_ROOT/projects/components/apb4_xbar/rtl/filelists/core/apb4_xbar_common.f

# Thin crossbar module
$REPO_ROOT/projects/components/apb4_xbar/rtl/apb4_xbar_thin.sv
