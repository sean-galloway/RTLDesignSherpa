# monbus_pkt_tally -- CAM-routed packet histogram.
#
# Moved out of rtl/amba/ to sit with the observers it serves. monbus_cam stays
# in amba because the compressor, the monbus groups and monbus_cam_pipe all use
# it; monbus_legal_cam came along because the tally is its only consumer.
#
# The CAM is pulled by -f rather than hand-listed: a hand-listed amba source is
# a second copy of that area's dependency list, and it goes stale silently.
-f $REPO_ROOT/rtl/amba/filelists/monbus_cam.f
$REPO_ROOT/projects/components/misc/rtl/monbus_legal_cam.sv
$REPO_ROOT/projects/components/misc/rtl/monbus_pkt_tally.sv
