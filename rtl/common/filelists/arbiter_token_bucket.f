# Filelist for arbiter_token_bucket module
# Location: rtl/common/filelists/arbiter_token_bucket.f
#
# Free-standing per-client request shaper - composes with any arbiter in the
# family but depends on NONE of them (that independence is the design point).

# Include directories
+incdir+$REPO_ROOT/rtl/amba/includes

# Header files with macros (MUST be compiled first)
$REPO_ROOT/rtl/amba/includes/reset_defs.svh

# arbiter_token_bucket module
$REPO_ROOT/rtl/common/arbiter_token_bucket.sv
