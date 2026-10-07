# LINT filelist for scoria_char_harness.
#
# The harness instantiates Xilinx primitives through the shared framework
# (led_status_driver uses BUFG for its slow-clock domain), and Verilator cannot
# elaborate them -- `--lint-only` on the synthesis list reports MODMISSING and
# says nothing about this design. Same split build-litedram makes for the
# generated core: lint reads a stub, Vivado reads the real primitive library.
#
# The stubs are SHARED (one file, repo-wide) and must never reach a synthesis
# filelist -- a stubbed BUFG that survives into a build is a clock that is not
# actually buffered.
-f $REPO_ROOT/projects/components/utility-ip/misc/rtl/filelists/verilator_xilinx_stubs.f
-f $REPO_ROOT/projects/fpga-systems/Genesys2/mem-ctrl-ip/scoria/rtl/filelists/scoria_char_harness.f
