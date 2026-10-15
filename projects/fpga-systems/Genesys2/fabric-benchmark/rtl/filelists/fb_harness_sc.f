# fb_harness, leg sc: the common harness plus the SmartConnect leg wrapper; the
# block design itself (fpga/ip/build) is added by the Vivado flow -- no sim.
-f $REPO_ROOT/projects/fpga-systems/Genesys2/fabric-benchmark/rtl/filelists/fb_harness_common.f
-f $REPO_ROOT/projects/fpga-systems/Genesys2/fabric-benchmark/rtl/filelists/fb_data_fabric_sc.f
