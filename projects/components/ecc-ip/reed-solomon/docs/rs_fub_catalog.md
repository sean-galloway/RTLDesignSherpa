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
| `gf_syndrome_cell` | One Horner evaluator: `S <= S * alpha^(b+i) + symbol` on every received symbol; after n symbols holds syndrome S_i. | `gf_mul_const` x1 (CONST = alpha^(b+i)) |
| `ribm_pe` | One processing element of the reformulated inversionless Berlekamp-Massey systolic array: two registers, two GF multiplies (discrepancy x error-locator term, gamma x auxiliary term), a subtract (XOR) and the swap mux driven by the control flags. Used when `KES_ALGO = "RIBM"`. | `gf_mul` x2 |
| `euclid_pe` | One processing element of the modified (inversionless) Euclidean systolic array: holds one coefficient of the remainder pair (R, Q) and of the quotient-accumulator pair (L, U); each step cross-multiplies by the two leading coefficients (`a*R_i + b*Q_i`, same for L/U), shifts, and swaps the pair when the degree compare says so. Used when `KES_ALGO = "EUCLID"`. | `gf_mul` x4 (two per polynomial pair) |
| `chien_cell` | One Chien register: `c_j <= c_j * alpha^(-j)` per position; the sum of all cells is Lambda(alpha^-i). | `gf_mul_const` x1 (CONST = alpha^(-j)) |
| `gf_lfsr_encoder` | The systematic encoder: a 2t-stage LFSR over GF(2^m) with generator-polynomial taps, g(x) built at elaboration from `gf_pkg` (t, first root b). k `i_step`s shift the data through; 2t `i_shift`s then drain the parity from the top register with zero feedback, which leaves the register clear for the next block -- no separate clear. `rtl/gf/gf_lfsr_encoder.sv`. | `gf_mul_const` x2t = 16 (one per generator coefficient) |
| `forney_evaluator` | Error magnitude at a located position: Omega(X^-1) / Lambda'(X^-1), times the first-root correction. Omega is evaluated by Horner (t cells), Lambda' comes from the odd Chien cells (shared, not duplicated), one inverse per error. | `gf_mul_const` x t = 8, `gf_mul` x2, `gf_inv` x1 |
| `erasure_locator` (optional, D5) | Builds the erasure-locator polynomial from the erasure flags and position counter, one multiply per flagged position, for the solver to start from. | `gf_mul` x t = 8, `counter_bin` x1 |
| `symbol_unpack` | Slices a `DATA_WIDTH` beat into `S = DATA_WIDTH / SYMBOL_WIDTH` symbols and tracks the position within the block; carries `last` through. | `counter_bin` x1 |
| `symbol_pack` | Re-assembles S symbols into a beat and emits `last` on the block's final symbol. | `shifter_beat_pack` x1, `counter_bin` x1 |
| `parity_mux` | Encoder output select: the k data symbols pass through, then the 2t parity symbols are appended; drives `last` on the final parity symbol. | `counter_bin` x1 |
| `corrector` | XORs the Forney value into the symbol leaving the block buffer when Chien flags its position; counts corrections; propagates `last`. | `counter_bin` x1 |
| `rs_status_counters` | Per-block ok / corrected-n / uncorrectable, running totals, the uncorrectable flag on the output status; feeds `rs_regs.hwif_in`. | `counter_bin` x3 |
| `line_randomizer` (optional, D12) | The standard's scrambler / pseudo-randomizer: XORs a binary LFSR sequence onto the symbol stream, re-seeded at each block start. Present only when `ENABLE_SCRAMBLER = 1`. | `shifter_lfsr_galois` x1 |
| `gaxi_fifo_sync` (repo) | Synchronous FIFO, mux read by default (`REGISTERED = 1` for a registered read). | `fifo_control` x1, `counter_bin` x2 |
| `axis4_slave` / `axis4_master` (repo) | AXI-Stream boundary wrappers with skid. | `gaxi_skid_buffer` x1 each |
| `axi4_master_rd` / `axi4_master_wr` (repo) | AXI4 master timing wrappers. | `gaxi_skid_buffer` x2 / x3 |
| `axis_monitor_lite` (repo) | Lite AXI-Stream monitor onto monbus. | `counter_freq_invariant` x1 |

## Level 2 -- instantiate Levels 0-1

| Block | What it does | Instantiates |
|---|---|---|
| `syndrome_unit` | All 2t syndromes at once, one cell per root, updated per received symbol; the all-zero test that lets an error-free block bypass the solver. | `gf_syndrome_cell` x2t = 16 |
| `key_equation_solver_ribm` | The riBM array (`KES_ALGO = "RIBM"`, the default -- PRD D11): 3t + 1 processing elements stepped 2t times under one control FSM (discrepancy select, gamma update, degree tracking). Produces Lambda(x) and Omega(x); flags degree > t as uncorrectable. | `ribm_pe` x(3t+1) = 25, `counter_bin` x1 (iteration) |
| `key_equation_solver_euclid` | The modified Euclidean array (`KES_ALGO = "EUCLID"`): Sugiyama's algorithm in the inversionless, cross-multiplying form of Shao et al. Starts from R = x^2t, Q = S(x), runs 2t iterations of the systolic array, tracks the two degrees, stops when deg R < t. Produces the same Lambda(x) and Omega(x) as riBM up to a common nonzero scale factor (harmless: Forney takes their ratio and Chien finds roots); flags deg Lambda > t as uncorrectable. Same ports as the riBM solver, so the core swaps one for the other with a generate. | `euclid_pe` x2t = 16, `counter_bin` x3 (iteration, deg R, deg Q) |
| `chien_search` | Evaluates Lambda at every position, one per cycle, and flags the roots; also exports the odd-cell sum (Lambda') for Forney. | `chien_cell` x(t+1) = 9, `counter_bin` x1 (position) |
| `block_buffer` | Holds the received block while the syndromes, solver and Chien run; read in lock-step with `chien_search` so the corrector meets each symbol at its position. Depth = n + 2t + pipeline, rounded up (512 for n = 255). | `gaxi_fifo_sync` x1 (DATA_WIDTH = S x (m + 1 erasure bit)) |
| `axis4_slave_monlite` / `axis4_master_monlite` (repo) | The AXIS wrappers with the lite monitor attached. | `axis4_slave` (or `_master`) x1, `axis_monitor_lite` x1 |

## Level 3 -- the deliverables: cores with valid/ready at both ends (PRD D9)

| Block | What it does | Instantiates |
|---|---|---|
| `rs_encoder_core` | k data symbols in, n symbols out, systematic. `in_valid/ready/data/keep/last` -> `out_valid/ready/data/keep/last` + `frame_err`. Drops into a consumer's write or transmit path. `rtl/rs_encoder_core.sv`: at `SYMBOLS_PER_BEAT = 1` (the only value elaborating today) the unpack and pack are wires and the parity select is inside the core, so the instance list is the LFSR and one output skid; the rows below join when S > 1 lands. | `gf_lfsr_encoder` x1, `gaxi_skid_buffer` x1 (output); planned for S > 1: `symbol_unpack` x1, `parity_mux` x1, `symbol_pack` x1, a second skid; `line_randomizer` x0/1 (D12) |
| `rs_decoder_core` | n symbols in (erasure bits optional), k corrected symbols out with a per-block status valid on `last`. Drops into a consumer's read or receive path. `KES_ALGO` selects the solver; nothing else in the core changes between the two. | `symbol_unpack` x1, `block_buffer` x1, `syndrome_unit` x1, `erasure_locator` x0/1 (D5), `key_equation_solver_ribm` OR `key_equation_solver_euclid` x1 (generate on `KES_ALGO`), `chien_search` x1, `forney_evaluator` x1, `corrector` x1, `rs_status_counters` x1, `symbol_pack` x1, `gaxi_skid_buffer` x3 (after unpack, solver-to-Chien handoff, before pack), `line_randomizer` x0/1 (D12) |

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
