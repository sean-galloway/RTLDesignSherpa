# Filelist for monbus_tally_axil -- the monbus packet BINNING engine.
#
# It had no filelist and no component test: it existed only inside
# stream_harness.f, so the only way to exercise a block sized for 100,000+
# packets was a ~21 minute full-system build that pushed six through it.
# With this closure it builds standalone in seconds.
#
# -f the OWNING area's filelists; never hand-list amba sources here. The
# first version of this file listed six rtl/amba/ sources directly, which
# fails `filelist_registry.py --audit` -- and because that gate audits the
# whole tree, it blocked commits for another session working in an unrelated
# area. See vault/handbook/design/filelists.md.

-f $REPO_ROOT/rtl/amba/filelists/monitor_pkgs.f
-f $REPO_ROOT/rtl/amba/filelists/monbus_pkt_tally.f

$REPO_ROOT/projects/fpga-systems/Genesys2/stream/rtl/monbus_tally_axil.sv
