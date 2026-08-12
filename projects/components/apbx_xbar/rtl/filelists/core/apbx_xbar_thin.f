# APB Crossbar Thin File List
# Location: projects/components/apbx_xbar/rtl/filelists/core/apbx_xbar_thin.f
# Purpose: Parametric "thin" APB crossbar (arbitrary MxN via parameters)
#
# Unlike apbx_xbar_{M}to{N}.sv, which bin/apbx_xbar_generator.py emits per
# configuration, apbx_xbar_thin is a single hand-written parametric crossbar.
# Consumers: formal/apbx_xbar/apbx_xbar_thin/ and rtl/integ_amba/examples/.

# Include common dependencies
-f $REPO_ROOT/projects/components/apbx_xbar/rtl/filelists/core/apbx_xbar_common.f

# The thin core's arbiter is the WEIGHTED round-robin (the generated
# MtoN variants use the plain one via apbx_xbar_common.f) -- this was a
# closure gap: consumers had to know to add it by hand.
-f $REPO_ROOT/rtl/common/filelists/arbiter_round_robin_weighted.f

# Thin crossbar module
$REPO_ROOT/projects/components/apbx_xbar/rtl/apbx_xbar_thin.sv
