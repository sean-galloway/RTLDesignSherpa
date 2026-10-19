# Forwarding filelist -- DELETE when the Genesys 2 bridges are regenerated.
# Location: projects/components/fabric-gen-ip/bridge/rtl/filelists_static/bridge_cam.f
#
# bridge_cam moved to deprecated/ on 2026-10-18 (no generated bridge uses it
# since bridge W12). The Genesys 2 STREAM and fabric-benchmark bridges were
# generated before that and still -f this path; regenerating them drops the
# reference, and then this file goes.

-f $REPO_ROOT/projects/components/fabric-gen-ip/bridge/deprecated/rtl/filelists_static/bridge_cam.f
