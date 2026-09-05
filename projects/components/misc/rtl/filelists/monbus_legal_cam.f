# Filelist for monbus_legal_cam
# Location: projects/components/misc/rtl/filelists/monbus_legal_cam.f
#
# Legal-set match CAM for the profile-mode packet tally: a CSR-loaded set of
# legal message identities (agent/protocol/type/event) -> dense bin index on a
# hit, miss reported so the caller routes it to a single UNEXPECTED bin.

+incdir+$REPO_ROOT/rtl/amba/includes

$REPO_ROOT/projects/components/misc/rtl/monbus_legal_cam.sv
