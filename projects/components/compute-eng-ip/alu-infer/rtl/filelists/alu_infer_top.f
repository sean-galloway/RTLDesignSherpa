# Filelist for alu_infer_top module.
# Location: projects/components/compute-eng-ip/alu-infer/rtl/filelists/alu_infer_top.f

# Include directories
+incdir+$REPO_ROOT/rtl/amba/includes
+incdir+$REPO_ROOT/projects/components/compute-eng-ip/alu-infer/rtl/includes

# Header files with macros (MUST be compiled first)
$REPO_ROOT/rtl/amba/includes/reset_defs.svh

# Package (MUST be compiled before the modules that import it)
$REPO_ROOT/projects/components/compute-eng-ip/alu-infer/rtl/includes/alu_infer_pkg.sv

# Math library dependencies instantiated by the row families
-f $REPO_ROOT/rtl/math/filelists/math_bf16_adder.f
-f $REPO_ROOT/rtl/math/filelists/math_bf16_comparator.f
-f $REPO_ROOT/rtl/math/filelists/math_bf16_exp2.f
-f $REPO_ROOT/rtl/math/filelists/math_bf16_fma.f
-f $REPO_ROOT/rtl/math/filelists/math_bf16_gelu.f
-f $REPO_ROOT/rtl/math/filelists/math_bf16_leaky_relu.f
-f $REPO_ROOT/rtl/math/filelists/math_bf16_log2.f
-f $REPO_ROOT/rtl/math/filelists/math_bf16_log2_scale.f
-f $REPO_ROOT/rtl/math/filelists/math_bf16_max.f
-f $REPO_ROOT/rtl/math/filelists/math_bf16_min.f
-f $REPO_ROOT/rtl/math/filelists/math_bf16_multiplier.f
-f $REPO_ROOT/rtl/math/filelists/math_bf16_reciprocal.f
-f $REPO_ROOT/rtl/math/filelists/math_bf16_relu.f
-f $REPO_ROOT/rtl/math/filelists/math_bf16_scale_to_int8.f
-f $REPO_ROOT/rtl/math/filelists/math_bf16_sigmoid.f
-f $REPO_ROOT/rtl/math/filelists/math_bf16_silu.f
-f $REPO_ROOT/rtl/math/filelists/math_bf16_tanh.f
-f $REPO_ROOT/rtl/math/filelists/math_bf16_to_fp16.f
-f $REPO_ROOT/rtl/math/filelists/math_bf16_to_fp32.f
-f $REPO_ROOT/rtl/math/filelists/math_bf16_to_fp8_e4m3.f
-f $REPO_ROOT/rtl/math/filelists/math_bf16_to_fp8_e5m2.f
-f $REPO_ROOT/rtl/math/filelists/math_fp16_to_bf16.f
-f $REPO_ROOT/rtl/math/filelists/math_fp32_comparator.f
-f $REPO_ROOT/rtl/math/filelists/math_fp32_gelu.f
-f $REPO_ROOT/rtl/math/filelists/math_fp32_leaky_relu.f
-f $REPO_ROOT/rtl/math/filelists/math_fp32_max.f
-f $REPO_ROOT/rtl/math/filelists/math_fp32_min.f
-f $REPO_ROOT/rtl/math/filelists/math_fp32_relu.f
-f $REPO_ROOT/rtl/math/filelists/math_fp32_sigmoid.f
-f $REPO_ROOT/rtl/math/filelists/math_fp32_silu.f
-f $REPO_ROOT/rtl/math/filelists/math_fp32_tanh.f
-f $REPO_ROOT/rtl/math/filelists/math_fp32_to_bf16.f
-f $REPO_ROOT/rtl/math/filelists/math_fp32_to_fp8_e4m3.f
-f $REPO_ROOT/rtl/math/filelists/math_fp8_e4m3_adder.f
-f $REPO_ROOT/rtl/math/filelists/math_fp8_e4m3_comparator.f
-f $REPO_ROOT/rtl/math/filelists/math_fp8_e4m3_gelu.f
-f $REPO_ROOT/rtl/math/filelists/math_fp8_e4m3_leaky_relu.f
-f $REPO_ROOT/rtl/math/filelists/math_fp8_e4m3_max.f
-f $REPO_ROOT/rtl/math/filelists/math_fp8_e4m3_min.f
-f $REPO_ROOT/rtl/math/filelists/math_fp8_e4m3_multiplier.f
-f $REPO_ROOT/rtl/math/filelists/math_fp8_e4m3_relu.f
-f $REPO_ROOT/rtl/math/filelists/math_fp8_e4m3_sigmoid.f
-f $REPO_ROOT/rtl/math/filelists/math_fp8_e4m3_silu.f
-f $REPO_ROOT/rtl/math/filelists/math_fp8_e4m3_tanh.f
-f $REPO_ROOT/rtl/math/filelists/math_fp8_e4m3_to_bf16.f
-f $REPO_ROOT/rtl/math/filelists/math_fp8_e4m3_to_fp32.f
-f $REPO_ROOT/rtl/math/filelists/math_fp8_e5m2_to_bf16.f
-f $REPO_ROOT/rtl/math/filelists/math_ieee754_2008_fp32_adder.f
-f $REPO_ROOT/rtl/math/filelists/math_ieee754_2008_fp32_fma.f
-f $REPO_ROOT/rtl/math/filelists/math_ieee754_2008_fp32_multiplier.f
-f $REPO_ROOT/rtl/math/filelists/math_int_to_bf16.f

# ALU-INFER RTL
$REPO_ROOT/projects/components/compute-eng-ip/alu-infer/rtl/alu_infer_delay.sv
$REPO_ROOT/projects/components/compute-eng-ip/alu-infer/rtl/alu_infer_decode.sv
$REPO_ROOT/projects/components/compute-eng-ip/alu-infer/rtl/alu_infer_bf16_rows.sv
$REPO_ROOT/projects/components/compute-eng-ip/alu-infer/rtl/alu_infer_int8_rows.sv
$REPO_ROOT/projects/components/compute-eng-ip/alu-infer/rtl/alu_infer_fp32_rows.sv
$REPO_ROOT/projects/components/compute-eng-ip/alu-infer/rtl/alu_infer_fp8_rows.sv
$REPO_ROOT/projects/components/compute-eng-ip/alu-infer/rtl/alu_infer_act_rows.sv
$REPO_ROOT/projects/components/compute-eng-ip/alu-infer/rtl/alu_infer_pwl.sv
$REPO_ROOT/projects/components/compute-eng-ip/alu-infer/rtl/alu_infer_cvt.sv
$REPO_ROOT/projects/components/compute-eng-ip/alu-infer/rtl/alu_infer_acc.sv
$REPO_ROOT/projects/components/compute-eng-ip/alu-infer/rtl/alu_infer_pipe.sv
$REPO_ROOT/projects/components/compute-eng-ip/alu-infer/rtl/alu_infer_rows.sv
$REPO_ROOT/projects/components/compute-eng-ip/alu-infer/rtl/alu_infer_top.sv
