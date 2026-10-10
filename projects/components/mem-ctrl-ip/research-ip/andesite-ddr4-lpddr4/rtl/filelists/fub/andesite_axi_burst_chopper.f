# Filelist for andesite_axi_burst_chopper
#
# FSM-free AXI address-channel chopper: one host AW/AR becomes N sub-commands
# of at most AXI_BEATS_PER_BURST beats each. It had no filelist of its own --
# it rode inside andesite_wr_splitter.f, which is where the splitter instantiates
# it -- so it could not be elaborated alone for a unit test. That list now
# pulls this one rather than naming the source twice.
+incdir+$REPO_ROOT/projects/components/mem-ctrl-ip/research-ip/andesite-ddr4-lpddr4/rtl/includes
+incdir+$REPO_ROOT/rtl/amba/includes
$REPO_ROOT/rtl/amba/includes/reset_defs.svh
$REPO_ROOT/projects/components/mem-ctrl-ip/research-ip/andesite-ddr4-lpddr4/rtl/fub/andesite_axi_burst_chopper.sv
