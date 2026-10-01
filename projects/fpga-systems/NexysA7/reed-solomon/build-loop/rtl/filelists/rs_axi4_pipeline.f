# Filelist for rs_axi4_pipeline
# Location: projects/fpga-systems/NexysA7/reed-solomon/build-loop/rtl/filelists/rs_axi4_pipeline.f
#
# The harness's AXI4 datapath: both codec tops plus the bare engines, the
# injector, and four sdpram memories. Pulled in by rs_loop_top.f only when the
# harness is built with IFACE = "AXI4".

-f $REPO_ROOT/projects/components/ecc-ip/reed-solomon/rtl/filelists/rs_encoder_axi4.f
-f $REPO_ROOT/projects/components/ecc-ip/reed-solomon/rtl/filelists/rs_decoder_axi4.f
-f $REPO_ROOT/projects/components/ecc-ip/reed-solomon/rtl/filelists/rs_error_injector.f
-f $REPO_ROOT/rtl/amba/filelists/sdpram_slave_axi4_axi4.f

$REPO_ROOT/projects/fpga-systems/NexysA7/reed-solomon/build-loop/rtl/rs_axi4_pipeline.sv
