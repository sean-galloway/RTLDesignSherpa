# Filelist for the Reed-Solomon AXI4 job engines
# Location: projects/components/ecc-ip/reed-solomon/rtl/filelists/rs_axi4_engines.f
#
# The two halves of the AXI4 boundary (PRD D9): a read engine that turns a
# source address plus a beat count into the cores' symbol stream, and a write
# engine that drains that stream into a destination region.
#
# Neither depends on anything outside itself -- the AXI4 channels are driven
# directly, and a top that wants registered channels adds axi4_master_rd /
# axi4_master_wr around them. That is why this list pulls in no amba filelist.

$REPO_ROOT/projects/components/ecc-ip/reed-solomon/rtl/axi4/rs_axi4_read_engine.sv
$REPO_ROOT/projects/components/ecc-ip/reed-solomon/rtl/axi4/rs_axi4_write_engine.sv
