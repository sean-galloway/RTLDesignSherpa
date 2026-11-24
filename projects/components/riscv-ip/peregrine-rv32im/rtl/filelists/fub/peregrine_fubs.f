# Aggregate FUB filelist for peregrine-rv32im
# Location: projects/components/riscv-ip/peregrine-rv32im/rtl/filelists/fub/peregrine_fubs.f

# reset_defs.svh -- ALWAYS_FF_RST/RST_ASSERTED macros.
-f $REPO_ROOT/rtl/amba/filelists/reset_defs.f

# peregrine package (imports rv32i_pkg)
-f $PEREGRINE_ROOT/rtl/filelists/peregrine_pkg.f

# Pipeline register FUBs
$PEREGRINE_ROOT/rtl/fub/peregrine_if_id.sv
$PEREGRINE_ROOT/rtl/fub/peregrine_id_ex.sv
$PEREGRINE_ROOT/rtl/fub/peregrine_ex_mem.sv
$PEREGRINE_ROOT/rtl/fub/peregrine_mem_wb.sv

# Forwarding / hazard unit
$PEREGRINE_ROOT/rtl/fub/peregrine_hazard.sv

# Machine-mode CSR file and trap state
$PEREGRINE_ROOT/rtl/fub/peregrine_csr.sv

# Iterative multiply/divide unit (M extension)
-f $PEREGRINE_ROOT/rtl/filelists/fub/peregrine_mdu.f
