# monbus_tally_axil moved to projects/components/misc/rtl/ to sit with the
# observers it serves, and its control registers are now a generated regblock
# (tally_regs.rdl) rather than hardcoded localparam offsets. This file stays as
# a redirect so nothing that referenced it by this path silently drops a source
# -- a filelist that resolves to nothing looks exactly like a clean build.
-f $REPO_ROOT/projects/components/misc/rtl/filelists/monbus_tally_axil.f
