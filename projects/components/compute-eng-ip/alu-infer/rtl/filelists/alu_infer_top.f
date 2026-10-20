# Filelist for alu_infer_top module.
# Location: projects/components/compute-eng-ip/alu-infer/rtl/filelists/alu_infer_top.f

# Include directories
+incdir+$REPO_ROOT/rtl/amba/includes

# Header files with macros (MUST be compiled first)
$REPO_ROOT/rtl/amba/includes/reset_defs.svh

# Math library dependencies instantiated by alu_infer_rows
-f $REPO_ROOT/rtl/math/filelists/math_bf16_adder.f
-f $REPO_ROOT/rtl/math/filelists/math_bf16_multiplier.f
-f $REPO_ROOT/rtl/math/filelists/math_bf16_fma.f
-f $REPO_ROOT/rtl/math/filelists/math_bf16_min.f
-f $REPO_ROOT/rtl/math/filelists/math_bf16_max.f
-f $REPO_ROOT/rtl/math/filelists/math_bf16_comparator.f
-f $REPO_ROOT/rtl/math/filelists/math_bf16_relu.f
-f $REPO_ROOT/rtl/math/filelists/math_fp32_to_bf16.f

# ALU-INFER RTL
$REPO_ROOT/projects/components/compute-eng-ip/alu-infer/rtl/alu_infer_acc.sv
$REPO_ROOT/projects/components/compute-eng-ip/alu-infer/rtl/alu_infer_pipe.sv
$REPO_ROOT/projects/components/compute-eng-ip/alu-infer/rtl/alu_infer_rows.sv
$REPO_ROOT/projects/components/compute-eng-ip/alu-infer/rtl/alu_infer_top.sv
