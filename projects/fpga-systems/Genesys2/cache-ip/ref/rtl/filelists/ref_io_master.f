# ref_io_master: the reference rig's doorbell master on onyx's ACE-Lite IO
# port (onyx TASK-001 step 7). Consumer: ref_genesys2_top.f (REF_CACHE_SEL
# 4 / 5 instantiate it).
-f $REPO_ROOT/rtl/amba/filelists/reset_defs.f
$REF_FRAMEWORK_ROOT/rtl/ref_io_master.sv
