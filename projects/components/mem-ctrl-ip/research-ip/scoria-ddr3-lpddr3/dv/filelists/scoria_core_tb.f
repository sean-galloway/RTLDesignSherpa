# Filelist for scoria_core_tb (the cocotb DV wrapper around scoria_core).
#
# The DUT closure comes from the component's OWN filelist -- never hand-list
# rtl/common or rtl/amba sources here; they rot when a component's internal
# deps change.
-f $REPO_ROOT/projects/components/mem-ctrl-ip/research-ip/scoria-ddr3-lpddr3/rtl/filelists/top/scoria_core.f
$REPO_ROOT/projects/components/mem-ctrl-ip/research-ip/scoria-ddr3-lpddr3/dv/tb/scoria_core_tb.sv
