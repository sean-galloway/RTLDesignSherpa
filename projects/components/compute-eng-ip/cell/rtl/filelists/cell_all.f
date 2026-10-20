# Master filelist for the cell RTL area (lint closure).
# The cell's own modules plus its dependencies: the delta node it instantiates
# and the alu-infer block (owned by the sibling alu-infer area) that slice 3+
# will instantiate. All reached transitively through cell_top.f.

-f $REPO_ROOT/projects/components/compute-eng-ip/cell/rtl/filelists/cell_top.f
