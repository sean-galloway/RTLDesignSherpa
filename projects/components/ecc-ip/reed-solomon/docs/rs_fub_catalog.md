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

# Reed-Solomon Codec -- FUB Catalog

**What this is:** every functional unit block in the codec, bottom-up. Level 0
is code that instantiates nothing. Each higher level instantiates only blocks
from the levels below it, and each entry lists ALL of them with counts. Counts
are for the reference profile RS(255,239): t = 8, m = 8, one symbol per beat
(`SYMBOLS_PER_BEAT = 1`); the formula in t, m and S is given where a count
scales. `(repo)` marks a block that already exists in the tree and is reused
as is; everything else is new RTL for this component. Nothing here is written
yet (2026-09-29); this page is the build plan and, later, the check that the
tree matches it.

Decisions this catalog assumes (PRD section 3): riBM solver (D11),
`SYMBOL_WIDTH` a parameter with `DATA_WIDTH` a multiple of it (D1),
`ENABLE_SCRAMBLER` (D12), valid/ready core with optional AXIS/AXI4 adapters
(D9). Erasure support (D5) is marked optional throughout.

---

## Level 0 -- leaves: pure code, no instances

| Block | What it does | Parameters | Notes |
|---|---|---|---|
| `gf_pkg` | The field, as a package of constant functions over (m, PRIM_POLY): multiply, multiply-by-x, alpha^k, power, inverse, log, and a primitivity check. Nothing is tabulated in the package; each module builds the `localparam` it needs (reduction constants, a constant-multiply matrix, log / antilog) by calling these at elaboration. One package serves every profile, so there is no generator and no Rule 0 exposure. The generator polynomial and first root `b` join when the encoder lands. | m, PRIM_POLY as function arguments | `rtl/gf/gf_pkg.sv`; a package, not a module; every GF block imports it |
| `gf_mul_const` | Multiply a symbol by a fixed field element: an XOR network, since a constant multiply in GF(2^m) is a linear map over GF(2). Column i of the m x m matrix is x^i * CONST mod p(x), built at elaboration. Synthesises to m XOR trees. | m, PRIM_POLY, CONST | `rtl/gf/gf_mul_const.sv`; the workhorse: encoder taps, syndrome roots, Chien steps |
| `gf_mul` | Full m x m -> m multiply (Mastrovito form): AND array for the (2m-1)-bit polynomial product, then the high m-1 bits folded back through the constants x^k mod p(x) as an XOR network. | m, PRIM_POLY | `rtl/gf/gf_mul.sv`; combinational, one level of AND then two log2(m)-deep XOR stages |
| `gf_inv` | Multiplicative inverse by table: log then negate then antilog, both tables built at elaboration from `gf_pkg`. inv(0) = 0 with `ow_zero` raised. One per decoder; used only in Forney. | m (2..12), PRIM_POLY | `rtl/gf/gf_inv.sv`; 2^m x m ROM twice; Itoh-Tsujii (which would need `gf_mul`) is the swap above m = 12 |
| `counter_bin` (repo, `rtl/common`) | Binary counter with a programmable terminal count and a wrap flag. | WIDTH, MAX | positions, iterations, block counts everywhere below |
| `gaxi_skid_buffer` (repo, `rtl/amba/gaxi`) | Two-entry (2..8) valid/ready decoupling buffer. | DATA_WIDTH, DEPTH | between any two stages that may stall each other |
| `fifo_control` (repo, `rtl/common`) | Read/write pointer, full/empty/almost flags for a synchronous FIFO. | ADDR_WIDTH, DEPTH, margins, REGISTERED | inside `gaxi_fifo_sync` |
| `shifter_beat_pack` (repo, `rtl/common`) | Packs narrow beats into a wide beat. | widths | inside `symbol_pack` |
| `shifter_lfsr_galois` (repo, `rtl/common`) | Galois-form binary LFSR with parameterised taps and seed. | WIDTH, taps, seed | the scrambler's engine |
| `counter_freq_invariant` (repo, `rtl/common`) | Tick generator independent of clock frequency. | | inside `axis_monitor_lite` |
| `rs_regs` (generated) | PeakRDL regblock: profile, enables, job registers (AXI4 ends), counters, interrupt. Generated code, instantiates nothing. | from the `.rdl` | `bin/peakrdl_generate.py`; `hwif_in` / `hwif_out` structs |

## Level 1 -- instantiate Level 0 only

| Block | What it does | Instantiates |
|---|---|---|
| `gf_syndrome_cell` | One Horner accumulator taking a beat per step: S unrolled steps s <= s * alpha^(b+i) ^ symbol (constant root, so one XOR network), the state after `i_count` of them kept -- a partial last beat costs a mux; i_first zeroes the state first, so no clear cycle. `ow_next` is the combinational next value. `rtl/gf/gf_syndrome_cell.sv`. | the root multiply as `gf_mul_fn` on a constant, S per cell |
| `ribm_pe` | One riBM cell: Delta_i <= gamma * Delta_{i+1} ^ delta * Theta_i; Theta_i <= swap ? Delta_{i+1} : Theta_i; i_load presets both. No feedback across the array, so the critical path is one multiply and one XOR at any t. `rtl/gf/ribm_pe.sv`. | `gf_mul` x2 |
| `euclid_pe` | Not a separate module: the Euclid solver's per-coefficient cross-multiply (two `gf_mul` and an XOR per R/Q coefficient, the same per lam~/mu~ coefficient) is generate loops inside `key_equation_solver_euclid`. | -- |
| `chien_cell` | One Chien register: `c_j <= c_j * alpha^(-j)` per position; the sum of all cells is Lambda(alpha^-i). | `gf_mul_const` x1 (CONST = alpha^(-j)) |
| `gf_lfsr_encoder` | The systematic encoder: a 2t-stage LFSR over GF(2^m) with generator-polynomial taps, g(x) built at elaboration from `gf_pkg` (t, first root b). One `i_step` applies `i_count` (1..S) symbol steps, unrolled, the constant tap multiplies folding to one XOR network; `i_shift` drains S parity symbols per cycle (lane 0 first) with zero feedback, leaving the register clear after ceil(2t/S) shifts -- no separate clear. `rtl/gf/gf_lfsr_encoder.sv`. | 2t tap multiplies per unrolled step as `gf_mul_fn` on constants, 2tS in all |
| `forney_evaluator` | The error value in each of S lanes: e = X^(1-b-off) Omega(X^-1) / Lambda'(X^-1), off = 2t with riBM's evaluator (the HIGH half of S*Lambda) or 0 with Euclid's textbook Omega -- `OMEGA_HIGH_HALF` selects, the core sets it from `KES_ALGO`, `dv/tbclasses/rs_model.py` proves both. Omega walks t Chien-style cells with the X^-(b+off) factor folded into their constants, stepped by alpha^((i+off)S) per beat; lane u sums them times alpha^((i+off)u); the odd-index sum from `chien_search` is X^-1 Lambda', so one inverse and one multiply per lane finish it. S inverses is the price of a correction in every lane of a beat in one cycle. `rtl/forney_evaluator.sv`. | `gf_mul_const` x2t (t load, t step), tS lane constants as `gf_mul_fn`, `gf_inv` xS, `gf_mul` xS |
| `erasure_locator` (optional, D5) | Builds the erasure-locator polynomial from the erasure flags and position counter, one multiply per flagged position, for the solver to start from. | `gf_mul` x t = 8, `counter_bin` x1 |
| `symbol_unpack` | Slices a `DATA_WIDTH` beat into `S = DATA_WIDTH / SYMBOL_WIDTH` symbols and tracks the position within the block; carries `last` through. | `counter_bin` x1 |
| `symbol_pack` | Re-assembles S symbols into a beat and emits `last` on the block's final symbol. | `shifter_beat_pack` x1, `counter_bin` x1 |
| `parity_mux` | Encoder output select: the k data symbols pass through, then the 2t parity symbols are appended; drives `last` on the final parity symbol. | `counter_bin` x1 |
| `corrector` | Inline in `rs_decoder_core`: the output stage XORs the stored Forney value into the stored received symbol when the position was a root AND the block's verdict is not uncorrectable. | -- |
| `rs_status_counters` | The per-block verdict is inline in `rs_decoder_core` (a status skid entry per block); the running counters belong to the register block of the standalone tops, not the core. | -- |
| `line_randomizer` (optional, D12) | The standard's scrambler / pseudo-randomizer: XORs a binary LFSR sequence onto the symbol stream, re-seeded at each block start. Present only when `ENABLE_SCRAMBLER = 1`. | `shifter_lfsr_galois` x1 |
| `gaxi_fifo_sync` (repo) | Synchronous FIFO, mux read by default (`REGISTERED = 1` for a registered read). | `fifo_control` x1, `counter_bin` x2 |
| `axis4_slave` / `axis4_master` (repo) | AXI-Stream boundary wrappers with skid. | `gaxi_skid_buffer` x1 each |
| `axi4_master_rd` / `axi4_master_wr` (repo) | AXI4 master timing wrappers. | `gaxi_skid_buffer` x2 / x3 |
| `axis_monitor_lite` (repo) | Lite AXI-Stream monitor onto monbus. | `counter_freq_invariant` x1 |

## Level 2 -- instantiate Levels 0-1

| Block | What it does | Instantiates |
|---|---|---|
| `syndrome_unit` | The 2t syndromes S_i = r(alpha^(b+i)) packed S_0 low, and an all-zero flag; stepped once per received symbol with i_first on a block's first. `rtl/syndrome_unit.sv`. | `gf_syndrome_cell` x2t |
| `key_equation_solver_ribm` | 3t+1 `ribm_pe` cells loaded with S_0..S_{2t-1}, zeros, and a 1 at 3t; 2t iterations under gamma / k / swap control; then Lambda_0..Lambda_2t at cells t..3t (the top t are the degree check: nonzero means more than t errors), the evaluator at cells 0..t-1, the degree and a degree-error flag. o_done exactly 2t cycles after i_start. Bit-exact against `rs_model.py`. `rtl/key_equation_solver_ribm.sv`. | `ribm_pe` x(3t+1) = 25 |
| `key_equation_solver_euclid` | Inversionless extended Euclid with every polynomial top-aligned: R, Q in 2t+1 symbols with nominal degrees, lam~ = Lambda x^(2t-degR) and mu~ = Mu x^(2t-degQ) in 2t+3 symbols, so the cross-multiply (Q[2t] R ^ R[2t] Q, times x) needs no shifter; a cycle either normalises a zero top (R or Q) or cross-multiplies, swapping roles when degR < degQ; stops when degR < t and un-shifts Lambda (2t+1 coefficients, top t = degree check) and the TEXTBOOK Omega. t+1 .. 2t cycles plus one (2t+1 seen at t <= 2 when a leading syndrome is zero). Bit-exact against `rs_model.py::euclid`; decodes identically to riBM. `rtl/key_equation_solver_euclid.sv`. | `gf_mul` x(2(2t+1) + 2(2t+3)) = 8t + 8 = 72 |
| `chien_search` | t+1 cells holding one beat of S positions: cell i loaded with Lambda_i alpha^(-i(n-1)) (position 0, shortening absorbed), stepped by alpha^(iS) per beat, and lane u evaluating sum_i c_i alpha^(iu); o_root[u] when a lane's sum is zero and o_odd_sum[u] = X^-1 Lambda'(X^-1) for Forney. `rtl/chien_search.sv`. | `gf_mul_const` x2(t+1) (load and step per cell) + (t+1)S lane constants as `gf_mul_fn` |
| `block_buffer` | Realised as a `gaxi_fifo_sync` instance inside `rs_decoder_core` (see that row); no separate module at S = 1. | -- |
| `axis4_slave_monlite` / `axis4_master_monlite` (repo) | The AXIS wrappers with the lite monitor attached. | `axis4_slave` (or `_master`) x1, `axis_monitor_lite` x1 |

## Level 3 -- the deliverables: cores with valid/ready at both ends (PRD D9)

| Block | What it does | Instantiates |
|---|---|---|
| `rs_encoder_core` | k data symbols in, n symbols out, systematic, S symbols per beat (`DATA_WIDTH / SYMBOL_WIDTH`). `in_valid/ready/data/keep/last` -> `out_valid/ready/data/keep/last` + `frame_err`. Data beats pass through with their keep; the LFSR advances by the beat's symbol count; parity follows in ceil(2t/S) beats, the last partial when S does not divide 2t -- so the output may hold a partial beat at the end of the data and another at the end of the parity, and contiguous repacking is the adapters' job. Measured: one beat per cycle plus the ceil(2t/S) parity gap. `rtl/rs_encoder_core.sv`. | `gf_lfsr_encoder` x1, `gaxi_skid_buffer` x1 (output); the parity select and count check are inline; `line_randomizer` x0/1 (D12) |
| `rs_decoder_core` | n symbols in, k corrected data symbols out, S per beat, with the verdict on every beat of the block (`out_last` on the beat holding the k-th symbol, its keep marking the data lanes only). Three stages joined by descriptor skids: receive (block FIFO of beats + syndromes; a descriptor per block on `in_last`, or on FIFO-depth overrun so a runaway stream cannot deadlock; a partial beat before the last is a framing error), solve (bypass for clean or mis-framed blocks, else the selected solver), correct (C1: Chien + Forney over S lanes per cycle reading the FIFO into a pipeline register; C2: from that register the second syndrome unit over the corrected stream and `{rx, correction, hit}` per lane into the output FIFO; C3: the verdict, one cycle later, from the re-check's REGISTERED all-zero output so the S-fold Horner chain ends at a flop -- that split is what closed 100 MHz on the Artix-7 and costs one cycle per block). A block is released only with its verdict and the correction is applied at the output unless the block is uncorrectable, so an uncorrectable block leaves as it arrived. Measured: n/S + 1 cycles per block sustained at S = 4 and 8. `rtl/rs_decoder_core.sv`. `KES_ALGO` selects riBM or Euclid; the Forney evaluator-form constant follows it and nothing else changes. | `syndrome_unit` x2 (receive, re-check), `key_equation_solver_ribm` OR `_euclid` x1, `chien_search` x1, `forney_evaluator` x1, `gaxi_fifo_sync` x2 (block: 2^ceil(log2((n+2t)/S+8)) beats x (S + Sm); output: 2^ceil(log2(2 ceil(k/S)+8)) beats x (1 + 2S + 2Sm)), `gaxi_skid_buffer` x3 (two descriptor stages, status); the corrector, status and length logic are inline |

| `error_injector` (test stimulus, replaced-by-shared-module) | Corrupts a coded valid/ready stream between encoder and decoder under host control: exact count per block at uniformly random distinct positions (selection sampling), a burst, a symbol error rate, or random burst clusters. Random nonzero error values; per-block and total statistics. A three-stage pipeline (accept + LFSR snapshot; the 16 x 16 products in DSPs; the decisions) because the first cut's combinational chain was 41 logic levels into the decoder's syndrome unit. Errors must be injected AFTER the encoder, which is why this is its own block and not a generator mode. `INJ_CFG.mark` (TASK-002, with `ERASURE_SUPPORT = 1`) adds `out_erasure[S-1:0]`: the per-lane hit mask riding beside the corrupted beat, so a downstream decoder is TOLD which symbols were corrupted and its correction bound doubles (f <= 2t, all flagged); unmarked runs leave it at zero and stay errors-only. Shared module: `projects/components/utility-ip/misc/rtl/error_injector.sv`; first used by the Nexys A7 loop harness. | S inline xorshift32 generators (a one-bit-per-step LFSR clustered the rate mode's hits) |

## Level 4 -- optional standalone adapters and tops (PRD D9, `INTAKE_IF` / `OUTLET_IF` != NONE)

| Block | What it does | Instantiates |
|---|---|---|
| `rs_axi_read_engine` | A job (source address, byte count) becomes AXI4 read bursts capped at `cfg_xfer_beats`; returned beats come out as the core's input stream with `last` every n symbols; done strobe per job. Modelled on STREAM's `axi_read_engine`, reduced to one job and a FIFO. | `axi4_master_rd` x1, `gaxi_fifo_sync` x1 (landing buffer), `counter_bin` x2 (beats in burst, symbols in block); `dma_address_gen` (repo, `utility-ip/misc`) x0/1 if strided jobs are wanted |
| `rs_axi_write_engine` | Drains the core's output stream into AXI4 write bursts at the job's destination, one block per n (decoder: k) symbols; done strobe carries bytes written and the block status. Modelled on STREAM's `axi_write_engine`. | `axi4_master_wr` x1, `gaxi_fifo_sync` x1 (drain buffer), `counter_bin` x2 |
| `rs_job_ctrl` | Sequences jobs from `rs_regs` (source / destination / count / kick) or from a descriptor stream; hands the write engine each block's destination before its first symbol arrives. | `gaxi_skid_buffer` x1 (descriptor port); FSM code |
| `rs_encoder` | Standalone encoder: the core with an adapter at each end. | `rs_encoder_core` x1; intake: `axis4_slave` or `axis4_slave_monlite` or `rs_axi_read_engine` x1; outlet: `axis4_master` or `axis4_master_monlite` or `rs_axi_write_engine` x1; `rs_job_ctrl` x0/1 (any AXI4 end); `rs_regs` x1 with the converters' APB-to-cpuif path (`utility-ip/converters`, as `stream_config_block` attaches its regblock) |
| `rs_decoder` | Standalone decoder, same pattern. | `rs_decoder_core` x1 + the same adapter set |

---

## Bill of materials, reference profile (both cores, `SYMBOLS_PER_BEAT = 1`)

| Primitive | Encoder core | Decoder core | Formula |
|---|---:|---:|---|
| `gf_mul_const` | 16 | 33 | encoder 2t; decoder 2t (syndromes) + t+1 (Chien) + t (Forney) |
| `gf_mul` | 0 | 52 riBM / 66 Euclid | decoder 2(3t+1) riBM = 50, or 4(2t) Euclid = 64; + 2 (Forney); + t with erasures |
| `gf_inv` | 0 | 1 | Forney |
| symbol registers in GF datapaths | 16 | 75 riBM / 89 Euclid | encoder LFSR 2t; decoder syndromes 2t + Chien t+1 + solver: riBM 2(3t+1) = 50, Euclid 4(2t) = 64 |
| `counter_bin` | 3 | 8 riBM / 10 Euclid | encoder unpack, parity mux, pack; decoder unpack, solver, Chien, erasure (opt), corrector, status x3, pack (block_buffer adds 2 more inside its FIFO) |
| `gaxi_skid_buffer` | 2 | 3 | stage boundaries |
| `gaxi_fifo_sync` | 0 | 1 (512 x 9) | block buffer |
| `shifter_lfsr_galois` | 0/1 | 0/1 | `ENABLE_SCRAMBLER` |

With `SYMBOLS_PER_BEAT = S > 1` (PRD D6) the syndrome cells and Chien cells
are replicated S times (or fed S symbols per cycle with S-fold Horner
steps), the encoder LFSR takes S symbols per cycle, and the block buffer
width grows by S; the solver does not scale with S.

Latency, decoder, one symbol per cycle: n cycles to absorb the block (the
syndromes finish with it), 2t solver iterations, then n cycles of Chien while
the buffer drains through the corrector -- about 2n + 2t + pipeline, of which
the second n overlaps the next block's arrival. Throughput is therefore one
block per n cycles once pipelined, with the block buffer sized for that
overlap.

## The two solvers, side by side (`KES_ALGO`)

Only three rows above differ between them: the Level 1 PE, the Level 2 solver
and the decoder core's generate. Syndromes, Chien, Forney, the buffer and the
corrector are identical and do not know which solver produced Lambda.

| | riBM (default) | modified Euclidean |
|---|---|---|
| Array length | 3t + 1 PEs | 2t PEs |
| GF multipliers | 2 per PE = 6t + 2 (50) | 4 per PE = 8t (64) |
| Iterations | 2t | 2t (at most; can stop early when deg R < t) |
| Critical path per step | one multiply + one XOR, no feedback across the array | cross-multiply + degree compare feeding the swap decision -- longer, and the reason riBM is the default |
| Control | discrepancy select, gamma update | two degree counters and the swap rule (the degree-computationless variant of Baek and Sunwoo removes the counters at the cost of a wider PE) |
| Output | Lambda, Omega | Lambda, Omega, scaled by a common factor |
| Readability | dense; the reformulation is not obvious from the textbook BM | the textbook algorithm, recognisable step by step |

Both are verified against the same golden model on the same blocks, and the
equivalence check is direct: identical Chien root sets and identical Forney
values for every corrected block.

## Where the reuse stops

- `cam_tag` (repo): not used. Chien delivers positions in order; a CAM would
  only matter for out-of-order multi-block decoding, which is out of scope.
- `math_multiplier_*`, `math_adder_*` (repo): not used. GF(2^m) has no
  carries; `gf_mul` is an AND/XOR array shaped like those trees but is its
  own module.
- `dataint_ecc_hamming_*` (repo): interface precedent only (data in, code
  out, error flags); nothing instantiated.
