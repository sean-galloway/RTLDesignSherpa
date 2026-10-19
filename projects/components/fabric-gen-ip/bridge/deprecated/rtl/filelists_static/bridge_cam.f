# Filelist for bridge_cam
# Location: projects/components/fabric-gen-ip/bridge/deprecated/rtl/filelists_static/bridge_cam.f
#
# DEPRECATED 2026-10-18 (bridge W12): no generated bridge instantiates
# bridge_cam; shared slaves route responses by the ID's master-index bits.
# Kept with its test and formal harness, out of every regression.
#
# WHY THIS DIRECTORY EXISTS
#   projects/components/fabric-gen-ip/bridge/rtl/filelists/ is owned by bridge_generator.py:
#   every .f in it is emitted by `make regen` and anything hand-written there is
#   destroyed on the next regeneration (and would be swept by a `make clean`
#   that clears the generated filelist directory).
#
#   bridge_cam is different. It is fixed IP, not generated: a parameterized
#   transaction-ID CAM that the generator *instantiates* (see
#   bin/bridge_pkg/generators/slave_adapter_generator.py) the same way it
#   instantiates gaxi_skid_buffer. It has its own formal proof
#   (formal/bridge/bridge_cam/) and its own testbench and test.
#
#   Hand-written filelists for hand-written bridge RTL therefore live here, so
#   the generated and non-generated halves never share a directory.

+incdir+$REPO_ROOT/rtl/amba/includes

-f $REPO_ROOT/rtl/amba/filelists/reset_defs.f

$BRIDGE_ROOT/deprecated/rtl/bridge_cam.sv
