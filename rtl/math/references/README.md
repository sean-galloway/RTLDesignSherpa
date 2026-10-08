<!-- RTL Design Sherpa Documentation Header -->
<table>
<tr>
<td width="80">
  <a href="https://github.com/sean-galloway/RTLDesignSherpa">
    <img src="https://raw.githubusercontent.com/sean-galloway/RTLDesignSherpa/main/docs/logos/Logo_200px.png" alt="RTL Design Sherpa" width="70">
  </a>
</td>
<td>
  <strong>RTL Design Sherpa</strong> · <em>Learning Hardware Design Through Practice</em><br>
  <sub>
    <a href="https://github.com/sean-galloway/RTLDesignSherpa">GitHub</a> ·
    <a href="https://github.com/sean-galloway/RTLDesignSherpa/blob/main/docs/DOCUMENTATION_INDEX.md">Documentation Index</a> ·
    <a href="https://github.com/sean-galloway/RTLDesignSherpa/blob/main/LICENSE">MIT License</a>
  </sub>
</td>
</tr>
</table>

---

<!-- End Header -->

# Peer-Paper Reference Archive for `rtl/math`

Seminal peer-reviewed (and, where noted, canonical non-peer) references for every
design technique implemented across the `rtl/math` SystemVerilog suite
(174 modules). The archive exists so that anyone reading or extending the RTL can
go straight to the original source of each algorithm rather than a textbook
retelling.

## Acquisition Policy

Only legitimately open-access copies are archived:

- arXiv preprints and open conference/journal versions
- Author or lab homepages (e.g. Jean-Michel Muller's page, Stanford AI Lab, U. Toronto)
- University course/lab mirrors that host licensed reprints (e.g. the Oklobdzija
  computer-arithmetic collection at UC Davis, which hosts the official reprints
  from Swartzlander's *Computer Arithmetic* volumes, and IEEE's own Milestones wiki)
- Institutional repositories (MIT DSpace) and preservation archives (Internet Archive)
- Standards bodies (Open Compute Project specification)

Every downloaded PDF was opened and its first page verified to be the cited
paper — HTML error pages and mislabeled files were rejected. Papers that exist
only behind a paywall are listed as **citation only** with a DOI link; nothing
was obtained from sketchy sources.

File naming: `<Technique>__<FirstAuthor><Year>.pdf`.

## Technique → Module(s) → Reference Index

### Integer adders, multipliers, and compressors

| Technique | Module(s) in `rtl/math` | Reference | Local PDF |
|-----------|--------------------------|-----------|-----------|
| Wallace tree partial-product reduction | `math_multiplier_wallace_tree_{008,016,032}.sv`, `math_multiplier_wallace_tree_csa_{008,016,032}.sv` | C. S. Wallace, "A Suggestion for a Fast Multiplier," *IEEE Trans. Electronic Computers* EC-13(1):14–17, Feb. 1964. DOI: [10.1109/PGEC.1964.263830](https://doi.org/10.1109/PGEC.1964.263830) | `WallaceTreeMultiplier__Wallace1964.pdf` |
| Dadda tree partial-product reduction | `math_multiplier_dadda_tree_{008,016,032}.sv` | L. Dadda, "Some Schemes for Parallel Multipliers," *Alta Frequenza* 34(5):349–356, May 1965. | `DaddaTreeMultiplier__Dadda1965.pdf` |
| Parallel counters / 4:2 compressors | `math_compressor_4to2.sv`, `math_multiplier_dadda_4to2_{008,011,024}.sv` | L. Dadda, "On Parallel Digital Multipliers," *Alta Frequenza* 45(10):574–580, 1976 (generalized parallel counters, the basis of (4:2) compressor trees). | `ParallelCountersCompressors__Dadda1976.pdf` |
| Carry-save adder arrays and basic multiplier cells | `math_multiplier_carry_save.sv`, `math_multiplier_basic_cell.sv`, `math_adder_carry_save.sv`, `math_adder_carry_save_nbit.sv` | Same origin as the Wallace/Dadda reduction scheme above (carry-save summation is the enabling construct of both papers). | see Wallace 1964 / Dadda 1965 |
| Carry-lookahead addition | `math_subtractor_carry_lookahead.sv`, `math_adder_pg_chain.sv` (PG-chain carry lookahead; group PG cells in the Brent-Kung family), `math_adder_brent_kung_grouppg_{008,016,032,064}.sv` | A. Weinberger, J. L. Smith, "A Logic for High-Speed Addition," *Nat. Bur. Standards Circular 591*, pp. 3–12, 1958 (the original carry-lookahead formulation). | `CarryLookaheadAddition__Weinberger1958.pdf` |
| Brent-Kung parallel-prefix adder | `math_adder_brent_kung_{008,016,032,064}.sv`, `math_adder_brent_kung_bitwisepg.sv`, `math_adder_brent_kung_black.sv`, `math_adder_brent_kung_gray.sv`, `math_adder_brent_kung_pg.sv`, `math_adder_brent_kung_sum.sv` | R. P. Brent, H. T. Kung, "A Regular Layout for Parallel Adders," *IEEE Trans. Computers* C-31(3):260–264, Mar. 1982. DOI: [10.1109/TC.1982.1675982](https://doi.org/10.1109/TC.1982.1675982) | `BrentKungPrefixAdder__Brent1982.pdf` |
| Han-Carlson parallel-prefix adder | `math_adder_han_carlson_{016,022,032,044,048,072}.sv` | T. Han, D. A. Carlson, "Fast Area-Efficient VLSI Adders," *Proc. 8th IEEE Symp. Computer Arithmetic (ARITH-8)*, pp. 49–56, 1987. DOI: [10.1109/ARITH.1987.6158699](https://doi.org/10.1109/ARITH.1987.6158699) | `HanCarlsonPrefixAdder__Han1987.pdf` |
| Kogge-Stone parallel-prefix adder (and prefix operator cells) | `math_prefix_cell.sv` (black cell), `math_prefix_cell_gray.sv` (gray cell), `math_adder_pg_chain.sv` | P. M. Kogge, H. S. Stone, "A Parallel Algorithm for the Efficient Solution of a General Class of Recurrence Equations," *IEEE Trans. Computers* C-22(8):786–793, Aug. 1973. DOI: [10.1109/TC.1973.5009159](https://doi.org/10.1109/TC.1973.5009159) | `KoggeStonePrefixAdder__Kogge1973.pdf` |

: Integer adder, multiplier, and compressor references

### Floating-point arithmetic core

| Technique | Module(s) in `rtl/math` | Reference | Status |
|-----------|--------------------------|-----------|--------|
| FP addition: alignment, normalization, leading-zero count | All FP adders: `math_bf16_adder.sv`, `math_ieee754_2008_fp16_adder.sv`, `math_ieee754_2008_fp32_adder.sv`, `math_fp8_e4m3_adder.sv`, `math_fp8_e5m2_adder.sv` (normalization uses the shared `count_leading_zeros` in `rtl/common`) | S. F. Anderson, J. G. Earle, R. E. Goldschmidt, D. M. Powers, "The IBM System/360 Model 91: Floating-Point Execution Unit," *IBM J. Res. & Develop.* 11(1):34–53, Jan. 1967. DOI: [10.1147/rd.111.0034](https://doi.org/10.1147/rd.111.0034) — first exposition of the swap/align/add/normalize FP pipeline used here. | citation only (IBM JRD paywalled on IEEE Xplore) |
| Leading-zero anticipation/count for normalization | post-add normalization in every FP adder (via `count_leading_zeros`) | E. Hokenek, R. K. Montoye, "Leading-Zero Anticipator (LZA) in the IBM RISC System/6000 Floating-Point Execution Unit," *IBM J. Res. & Develop.* 34(1):71–77, 1990. DOI: [10.1147/rd.341.0071](https://doi.org/10.1147/rd.341.0071) — the seminal LZC/LZA normalization reference (this library uses post-add leading-zero count, the LZA concept minus the anticipator circuit). | citation only (IBM JRD paywalled) |
| Guard/round/sticky computation and round-to-nearest-even | `math_bf16_mantissa_mult.sv`, `math_ieee754_2008_fp16_mantissa_mult.sv`, `math_ieee754_2008_fp32_mantissa_mult.sv`, `math_fp8_e4m3_mantissa_mult.sv`, `math_fp8_e5m2_mantissa_mult.sv`, and all multiplier/adder outputs with `ow_guard_bit/ow_round_bit/ow_sticky_bit` | *IEEE Standard for Floating-Point Arithmetic*, IEEE Std 754-2008, Aug. 2008. DOI: [10.1109/IEEESTD.2008.4610935](https://doi.org/10.1109/IEEESTD.2008.4610935) (the standard that defines RNE and the GRS rounding pipeline). | citation only (standard, paywalled; official page: [standards.ieee.org](https://standards.ieee.org/standard/754-2008.html)) |
| Flush-to-zero vs. gradual underflow (subnormal support) | `SUBNORMAL_SUPPORT` parameter in `math_ieee754_2008_fp32_adder.sv`, `math_ieee754_2008_fp32_divider.sv`, `math_ieee754_2008_fp32_sqrt.sv`, `math_ieee754_2008_fp32_fma.sv`, `math_ieee754_2008_fp32_multiplier.sv`, `math_ieee754_2008_fp16_adder.sv` | J. W. Demmel, "Underflow and the Reliability of Numerical Software," *SIAM J. Sci. Stat. Comput.* 5(4):887–919, 1984. DOI: [10.1137/0905062](https://doi.org/10.1137/0905062) — the definitive treatment of gradual underflow vs. flush-to-zero; the RTL parameter toggles exactly the behavior analyzed here. *IEEE Std 754-2008* (above) specifies the gradual-underflow requirement. | citation only (SIAM paywalled) |
| Fused multiply-add (aligned single rounding) | `math_bf16_fma.sv`, `math_fp8_e4m3_fma.sv`, `math_fp8_e5m2_fma.sv`, `math_ieee754_2008_fp16_fma.sv`, `math_ieee754_2008_fp32_fma.sv` | T. Lang, J. D. Bruguera, "Floating-Point Fused Multiply-Add with Reduced Latency for Floating-Point Addition," *Proc. 17th IEEE Symp. Computer Arithmetic (ARITH-17)*, pp. 42–51, 2005. DOI: [10.1109/ARITH.2005.22](https://doi.org/10.1109/ARITH.2005.22). Companion architecture paper: E. Quinnell, E. E. Swartzlander Jr., C. Lemonds, "Floating-Point Fused Multiply-Add Architectures," *Proc. 41st Asilomar Conf. Signals, Systems and Computers*, pp. 331–337, 2007 (citation only, IEEE paywalled; note the venue is Asilomar, not DAC as sometimes mis-cited). | `FMAReducedLatency__Lang2005.pdf` |
| Goldschmidt multiplicative division | `math_bf16_goldschmidt_div.sv`, `math_ieee754_2008_fp32_divider.sv` (divider header: "Goldschmidt-class multiplicative divide with exact-residual RNE") | R. E. Goldschmidt, "Applications of Division by Convergence," M.S. thesis, MIT, Dept. of Electrical Engineering, June 1964. Handle: [1721.1/11113](https://dspace.mit.edu/handle/1721.1/11113). Note: the origin of this algorithm is Goldschmidt's MIT thesis / Lincoln Laboratory work, so the thesis *is* the primary source (a tech-report-grade origin is acceptable here as there is no later journal version). The classic journal survey of the family is M. J. Flynn, "On Division by Functional Iteration," *IEEE Trans. Computers* C-19(8):702–706, 1970. | `GoldschmidtDivision__Goldschmidt1964.pdf`, `FunctionalIterationDivision__Flynn1970.pdf` |
| Newton-Raphson reciprocal / reciprocal-square-root refinement | `math_bf16_newton_raphson_recip.sv`, `math_bf16_reciprocal.sv`, `math_bf16_fast_reciprocal.sv`, `math_ieee754_2008_fp32_sqrt.sv` (NR reciprocal-sqrt) | P. W. Markstein, "Computation of Elementary Functions on the IBM RISC System/6000 Processor," *IBM J. Res. & Develop.* 34(1):111–119, 1990. DOI: [10.1147/rd.341.0111](https://doi.org/10.1147/rd.341.0111) — Newton-based divide/square-root with correct final rounding as shipped in the RS/6000. The multiplicative-iteration family is surveyed in Flynn 1970 (PDF above). | citation only (IBM JRD paywalled) |
| Table-based reciprocation / initial seed LUTs with small multipliers | LUT seeding inside `math_bf16_newton_raphson_recip.sv`, `math_bf16_reciprocal.sv`, `math_bf16_fast_reciprocal.sv`, `math_bf16_goldschmidt_div.sv`, and the generator `bin/rtl_generators/ieee754/fp32_sqrt.py` | M. D. Ercegovac, T. Lang, J.-M. Muller, A. Tisserand, "Reciprocation, Square Root, Inverse Square Root, and Some Elementary Functions Using Small Multipliers," *IEEE Trans. Computers* 49(7):628–637, 2000. DOI: [10.1109/12.863031](https://doi.org/10.1109/12.863031) — the seminal small-table + small-multiplier method on which these LUT-seeded refinements rest. | `SmallMultiplierReciprocal__Ercegovac2000.pdf` |
| LUT seed-table construction (exact-integer bucket-center) | `bin/rtl_generators/ieee754/fp32_sqrt.py` (`_build_reciprocal_sqrt_lut`, 7-bit index / 12-bit entry, entries chosen by exact `\|c²B − 2^46\|` minimization with an integer `isqrt`) | No peer paper — this bucket-center, integer-exact seed construction is original to this repository. Defensible basis for the surrounding method: Markstein 1990 and Ercegovac et al. 2000 (above). | no paper (repo-original; see citations above) |
| Exact-residual final rounding (division / isqrt-based root rounding) | `math_ieee754_2008_fp32_divider.sv` ("exact-residual RNE"), `math_ieee754_2008_fp32_sqrt.sv` (residual `rem = W − y0²` rounded by exact integer sqrt comparison) | P. W. Markstein, 1990 (above) — exact remainder check to deliver the correctly rounded quotient/root without an extra refinement step. | citation only (IBM JRD paywalled) |

: Floating-point arithmetic references

### Transcendentals, quant formats, and conversions

| Technique | Module(s) in `rtl/math` | Reference | Status |
|-----------|--------------------------|-----------|--------|
| exp2/log2 by table + evaluation (LUT approximation) | `math_bf16_exp2.sv`, `math_bf16_log2.sv` (direct LUT over the fractional significand), `math_bf16_log2_scale.sv` (exponent extraction + LUT) | The seminal table-driven elementary-function method family: P. T. P. Tang, "Table-Driven Implementation of the Exponential Function in IEEE Floating-Point Arithmetic," *ACM TOMS* 15(2):144–157, 1989, DOI: [10.1145/63522.214389](https://doi.org/10.1145/63522.214389); and P. T. P. Tang, "Table-Driven Implementation of the Logarithm Function in IEEE Floating-Point Arithmetic," *ACM TOMS* 16(4):378–400, 1990, DOI: [10.1145/98267.98294](https://doi.org/10.1145/98267.98294). These BF16 modules use the degenerate pure-LUT case of Tang's table(+polynomial) scheme. | citation only (ACM paywalled) |
| Power-of-two quantization scale (log2-scale / shift-only quantization) | `math_bf16_log2_scale.sv`, `math_bf16_scale_to_int8.sv` | No dedicated peer paper — computing `2^⌊log2(max)⌋` as the per-tensor scale is standard exponent extraction. Quantization pipeline context: B. Jacob et al., "Quantization and Training of Neural Networks for Efficient Integer-Arithmetic-Only Inference," *Proc. IEEE CVPR*, 2018 (below). | see `Int8Quantization__Jacob2018.pdf` |
| INT8 quantization (fused multiply + convert with saturation) | `math_bf16_scale_to_int8.sv`, `math_bf16_to_int.sv`, `math_int_to_bf16.sv` | B. Jacob, S. Kligys, B. Chen, M. Zhu, M. Tang, A. Howard, H. Adam, D. Kalenichenko, "Quantization and Training of Neural Networks for Efficient Integer-Arithmetic-Only Inference," *Proc. IEEE CVPR*, pp. 2704–2713, 2018. arXiv: [1712.05877](https://arxiv.org/abs/1712.05877) | `Int8Quantization__Jacob2018.pdf` |
| FP8 (e4m3 / e5m2) formats and conversions | `math_fp8_e4m3_*`, `math_fp8_e5m2_*` families, and every `*_to_fp8_*` converter | P. Micikevicius, D. Stosic, P. Judd, J. Kamalu, S. Oberman, M. Shoeybi, M. Siu, H. Wu, N. Burgess, S. Ha, R. Grisenthwaite, "FP8 Formats for Deep Learning," arXiv: [2209.05433](https://arxiv.org/abs/2209.05433), 2022. Canonical interchange-format definition: *OCP 8-bit Floating Point Specification (OFP8) Rev 1.0*, Open Compute Project, 2023, [opencompute.org](https://www.opencompute.org/documents/ocp-8-bit-floating-point-specification-ofp8-revision-1-0-2023-12-01-pdf-1) (industry specification, not a peer paper — archived as the format's defining document). | `FP8Formats__Micikevicius2022.pdf`, `OFP8Specification__OCP2023.pdf` |
| BF16 format | `math_bf16_*` family; `math_bf16_to_fp32/fp16`, `math_fp32_to_bf16`, `math_fp16_to_bf16` | No peer-reviewed BF16 definition exists. Canonical source: S. Wang, P. Kanwar, "BFloat16: The Secret to High Performance on Cloud TPUs," Google Cloud blog, Aug. 2019, [cloud.google.com](https://cloud.google.com/blog/products/ai-machine-learning/bfloat16-the-secret-to-high-performance-on-cloud-tpus) (non-peer; cited as the format's defining document). | citation only (non-peer blog, canonical) |
| FP16/FP32 conversions (round-to-nearest-even cvt) | `math_bf16_to_fp16.sv`, `math_fp16_to_fp32.sv`, `math_fp32_to_fp16.sv`, `math_fp32_to_bf16.sv`, `math_bf16_to_fp32.sv`, `math_fp16_to_bf16.sv`, `math_fp8_*_to_*`, `math_bf16_to_fp8_*` | Rounding semantics per *IEEE Std 754-2008* (above). | citation only |

: Transcendental and conversion-format references

### Deep-learning activation functions

Generated by `bin/rtl_generators/ieee754/fp_activations.py` into `math_{bf16,fp16,fp32,fp8_e4m3,fp8_e5m2}_{sigmoid,tanh,gelu,silu,relu,leaky_relu,softmax_8}.sv`. References are the original ML papers defining each function (these RTL modules implement piecewise/LUT approximations of the definitions).

| Activation | Module(s) | Reference | Local PDF |
|------------|-----------|-----------|-----------|
| ReLU | `*_relu.sv` | V. Nair, G. E. Hinton, "Rectified Linear Units Improve Restricted Boltzmann Machines," *Proc. 27th ICML*, pp. 807–814, 2010. | `ReLU__Nair2010.pdf` |
| Leaky ReLU | `*_leaky_relu.sv` | A. L. Maas, A. Y. Hannun, A. Y. Ng, "Rectifier Nonlinearities Improve Neural Network Acoustic Models," *Proc. ICML Workshop on Deep Learning for Audio, Speech and Language Processing*, 2013. | `LeakyReLU__Maas2013.pdf` |
| GELU | `*_gelu.sv` (sigmoid approximation `x·σ(1.702x)` per the module header) | D. Hendrycks, K. Gimpel, "Gaussian Error Linear Units (GELUs)," arXiv: [1606.08415](https://arxiv.org/abs/1606.08415), 2016. | `GELU__Hendrycks2016.pdf` |
| SiLU / Swish | `*_silu.sv` | P. Ramachandran, B. Zoph, Q. V. Le, "Searching for Activation Functions" (Swish), arXiv: [1710.05941](https://arxiv.org/abs/1710.05941), 2017; S. Elfwing, E. Uchibe, K. Doya, "Sigmoid-Weighted Linear Units for Neural Network Function Approximation in Reinforcement Learning" (SiLU name), *Neural Networks* 107:3–11, 2018, arXiv: [1702.03118](https://arxiv.org/abs/1702.03118). | `Swish__Ramachandran2017.pdf`, `SiLU__Elfwing2018.pdf` |
| Sigmoid | `*_sigmoid.sv` | D. E. Rumelhart, G. E. Hinton, R. J. Williams, "Learning Representations by Back-Propagating Errors," *Nature* 323:533–536, 1986, DOI: [10.1038/323533a0](https://doi.org/10.1038/323533a0) — the paper that made the logistic sigmoid the standard hidden-unit nonlinearity; the function itself is the classical logistic function. | citation only (Nature paywalled) |
| Tanh | `*_tanh.sv` | Same lineage as sigmoid (Rumelhart et al. 1986, citation only); tanh is the classical hyperbolic tangent activation. | citation only |
| Softmax (max-subtract, exp, reduce, normalize) | `*_softmax_8.sv` | M. Milakov, N. Gimelshein, "Online Normalizer Calculation for Softmax," arXiv: [1805.02867](https://arxiv.org/abs/1805.02867), 2018 — the online/rescaling softmax formulation that motivates streaming max+sum reduction trees. | `OnlineSoftmax__Milakov2018.pdf` |

: Activation function references

### Reduction, comparison, and utility logic

| Technique | Module(s) in `rtl/math` | Reference | Status |
|-----------|--------------------------|-----------|--------|
| Min/max comparator reduction trees | `math_{bf16,fp16,fp32,fp8_e4m3,fp8_e5m2}_{min,max,min_tree_8,max_tree_8}.sv`, `*_comparator.sv` | No seminal peer paper — tournament (comparator-tree) reduction is a standard construct in every computer-arithmetic text; no defensible single origin exists. | no paper (standard technique) |
| Clamp (saturating bounds) | `math_{bf16,fp16,fp32,fp8_e4m3,fp8_e5m2}_clamp.sv` | No seminal peer paper — clamping/saturating arithmetic is standard; the saturation behavior in the INT8 path follows Jacob et al. 2018 (above). | no paper (standard technique) |
| mod-3 via base-4 digit-sum with carry-save compressors | `math_mod_3_compress.sv` (3:2 compressor tree over 2-bit digit groups, congruent mod 3 since 4^k ≡ 1) | H. L. Garner, "The Residue Number System," *IRE Trans. Electronic Computers* EC-8(2):140–147, 1959, DOI: [10.1109/TEC.1959.5219515](https://doi.org/10.1109/TEC.1959.5219515) — the seminal residue-arithmetic reference establishing mod-3 residue checking. | citation only (IEEE paywalled) |
| Half/full adders, ripple-carry add/subtract | `math_adder_half.sv`, `math_adder_full{,_nbit}.sv`, `math_addsub_full_nbit.sv`, `math_adder_ripple_carry.sv`, `math_subtractor_half/full{,_nbit}.sv`, `math_subtractor_ripple_carry.sv` | No seminal peer paper — these are the pre-1960 textbook primitives that the papers above build on; the carry-propagation theory originates with Weinberger & Smith 1958 (PDF above). | no paper (standard technique) |

: Utility-logic references

## Notes

- **Goldschmidt provenance.** The Goldschmidt divider's origin is Robert Goldschmidt's 1964 MIT M.S. thesis (done in the MIT Lincoln Laboratory environment). There is no journal version; the thesis is the primary source and is archived here from MIT DSpace. Flynn 1970 is the standard peer-reviewed survey of the multiplicative-iteration division family (Goldschmidt and Newton-Raphson).
- **Newton-Raphson.** The method itself predates peer review (Newton, 1669). The peer citations here (Markstein 1990; Ercegovac et al. 2000) are the seminal *hardware* treatments: initial table lookup, multiplicative refinement, and exact final rounding.
- **LZC vs. LZA.** The FP adders normalize with a post-add leading-zero **count** (LZC) rather than a leading-zero **anticipator** (LZA). Hokenek & Montoye 1990 is cited as the seminal normalization reference for the concept; the RTL deliberately uses the simpler LZC variant.
- **Tang vs. these LUTs.** The BF16 `exp2`/`log2` modules implement the pure table-lookup degenerate case of Tang's table-driven scheme (no polynomial correction term). Tang 1989/1990 remain the correct seminal citations for table-driven exp/log evaluation.
- **Citation-only entries** were verified against publisher records and the Nelson H. F. Beebe floating-point bibliography (University of Utah) but could not be obtained from any legitimate open source at archive time; follow the DOI links for the paywalled versions.

*Archive compiled 2026-10-07. 20 PDFs, ~18 MB.*
