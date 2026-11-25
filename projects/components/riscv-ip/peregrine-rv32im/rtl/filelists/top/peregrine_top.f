# Filelist for peregrine_top (the cached build, TASK-001 stage 4)
# Location: projects/components/riscv-ip/peregrine-rv32im/rtl/filelists/top/peregrine_top.f

-f $PEREGRINE_ROOT/rtl/filelists/top/peregrine_core.f
-f $PEREGRINE_ROOT/rtl/filelists/fub/peregrine_icache.f
-f $PEREGRINE_ROOT/rtl/filelists/fub/peregrine_clint.f
-f $PEREGRINE_ROOT/rtl/filelists/fub/peregrine_uc_axi.f
-f $PEREGRINE_ROOT/rtl/filelists/fub/peregrine_axi4_arb.f

# D$: amber (cache-ip/amber-mesi-l1), its own complete closure
-f $AMBER_ROOT/rtl/filelists/amber_top.f

$PEREGRINE_ROOT/rtl/top/peregrine_top.sv
