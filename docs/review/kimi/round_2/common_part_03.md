# Review: common_part_03 (19 docs, 19 modules + dependencies)

Verification method: for every numeric/structural claim I re-derived it from the RTL in `RTL.sv` (port lists, parameter lists, generate logic, counter/rotation arithmetic, flag equations). Truth tables for CLZ/CTZ/parity/ECC were spot-recomputed; FIFO flag equations were compared term-by-term with `fifo_control.sv`.

---

## Findings

### F1 — Phantom parameter `ALGO_NAME`; four examples will not compile
**[CONFIRMED]**
- File: `docs/markdown/RTLCommon/dataint_crc.md`
- Says: module declaration shows `parameter string ALGO_NAME = "DEADF1F0"`; parameter table row `| ALGO_NAME | string | "DEADF1F0" | Algorithm identifier for documentation |`; used in four examples (`.ALGO_NAME("CRC32_IEEE")`, `.ALGO_NAME("CRC16_CCITT")`, `.ALGO_NAME("CRC64_ECMA")`, `.ALGO_NAME($sformatf("STAGE_%0d", stage))`).
- Actually: `rtl/common/dataint_crc.sv` declares exactly four parameters — `DATA_WIDTH`, `CRC_WIDTH`, `REFIN`, `REFOUT`. There is no `ALGO_NAME`. Overriding a non-existent parameter is an elaboration error in every tool.
- Impact: a reader copying any of the four configuration examples gets a compile failure; the CRC-32/16/64 "standards compatibility" recipes are unusable as written.

### F2 — fifo_control.md documents the *buggy* cast as the fix
**[CONFIRMED]**
- File: `docs/markdown/RTLCommon/fifo_control.md`
- Says: all three occupancy formulas use `AW'(D)` (and `AW'(AFT)` / `AW'(AET)`), and the "Width Casting Fix" section states: "The `AW'(D)` casting ensures all operands have matching bit widths, preventing synthesis warnings."
- Actually: `rtl/common/fifo_control.sv` uses `(AW+1)'(D)`, `(AW+1)'(AFT)`, `(AW+1)'(AET)`, with widened `logic [AW:0] w_almost_full_count`, and its own comment states: `// For depth=16, AW=4: AW'(16) = 4'b0000 (wrong!), (AW+1)'(16) = 5'b10000 (correct!)`. Recomputation for DEPTH=16, wrapped case wr=2, rd=14: correct occupancy = 16−14+2 = 4; the documented formula computes 0−14+2 (garbage). So the doc presents the pre-fix code and calls it the fix.
- Impact: anyone reimplementing or reviewing against the doc reintroduces a real truncation bug in almost-full/almost-empty/count at wraparound. (The doc also omits that `count` is registered when `REGISTERED==1`: RTL `assign count = (REGISTERED == 1) ? r_count : w_count;`.)

### F3 — fifo_sync.md documents parameter `INSTANCE_NAME` and simulation checks that do not exist
**[CONFIRMED]**
- File: `docs/markdown/RTLCommon/fifo_sync.md`
- Says: parameter list includes "**`INSTANCE_NAME`** - Debug identifier (default: "DEADF1F0")" and an "Error Detection / Built-in simulation checks" block containing `$display("Error: %s write while fifo full, %t", INSTANCE_NAME, $time);`.
- Actually: `rtl/common/fifo_sync.sv` parameters are `MEM_STYLE, REGISTERED, DATA_WIDTH, DEPTH, ALMOST_WR_MARGIN, ALMOST_RD_MARGIN` — no `INSTANCE_NAME`, and the module body contains no `$display`/overflow checks at all (it ends at `assign rd_data = w_rd_data;`).
- Impact: a reader setting `.INSTANCE_NAME(...)` gets an elaboration error; a reader relying on the documented overflow warnings gets silence.

### F4 — fifo_async.md "Error Detection Features" do not exist in the RTL
**[CONFIRMED]**
- File: `docs/markdown/RTLCommon/fifo_async.md`
- Says: a "Simulation-only error checking" `always_ff` block printing `"Error: %s write while fifo full, %t", INSTANCE_NAME, $time`.
- Actually: `rtl/common/fifo_async.sv` has no `INSTANCE_NAME` parameter and no runtime `$display` checks anywhere in the body (the only message is the elaboration-time `$error` for non-power-of-2 DEPTH in Gray mode, which is a different, real feature).
- Impact: same as F3 — documented safety telemetry is absent.

### F5 — counter_ring.md rotation direction prose contradicts the RTL (and its own tables)
**[CONFIRMED]**
- File: `docs/markdown/RTLCommon/counter_ring.md`
- Says: "Mathematical Representation: `ring_out[i] = ring_out[i-1] for i = 1 to WIDTH-1; ring_out[0] = ring_out[WIDTH-1]`"; "**Feedback**: MSB connects back to LSB (no inversion)"; "MSB becomes new LSB".
- Actually: RTL is `ring_out <= {ring_out[0], ring_out[WIDTH-1:1]};` → new[i] = old[i+1] (bits move toward the LSB; the LSB wraps to the MSB). Recomputation from reset `0001`: RTL gives `1000` — which matches the doc's own state tables (`0001→1000→0100→0010→0001`) — while the doc's formula gives `0010`, contradicting both the RTL and the doc's tables. The correct statements are "LSB connects back to MSB" and "LSB becomes new MSB".
- Impact: a reader implementing from the formulas builds the opposite rotation; the page contradicts itself between prose and tables.

### F6 — debounce.md release-detection timing is wrong and self-contradictory
**[CONFIRMED]**
- File: `docs/markdown/RTLCommon/debounce.md`
- Says: "**Release detection**: `DEBOUNCE_DELAY` ticks after button releases" and "**Asymmetric**: Same delay for both press and release".
- Actually: the output is `w_debounced_signals[i] = &r_shift_regs[i]` — an AND reduce. On release, the first `0` shifted in (one `long_tick`) clears the AND, so `button_out` falls after ~1 tick + 1 clk, not after `DEBOUNCE_DELAY` ticks. Only the *press* path needs `DEBOUNCE_DELAY` consecutive matching samples. The behavior is asymmetric, but in exactly the way the doc denies, and the "Asymmetric: same delay" sentence contradicts itself.
- Impact: a reader expects symmetric 40 ms (default) debounce; release actually propagates ~4× faster and is not debounced beyond one sample.

### F7 — fifo_async.md points readers to the retired `fifo_async_div2`
**[CONFIRMED]**
- File: `docs/markdown/RTLCommon/fifo_async.md`
- Says: "When to Use vs. Alternatives … **Use async_div2 when**: Need non-power-of-2 depth".
- Actually: no `fifo_async_div2` exists in the RTL; the same page's Related Modules section already says USE_JOHNSON=1 "replaces the retired fifo_async_div2". Non-power-of-2 depths are handled by `fifo_async #(.USE_JOHNSON(1))` (RTL: `PTRW = (USE_JOHNSON != 0) ? JCW : (AW + 1)` with `counter_johnson`/`johnson2bin`).
- Impact: internal contradiction; a reader searches for a module that no longer exists instead of using the parameter.

### F8 — dataint_crc.md "Basic CRC Calculation" example can never produce a CRC
**[CONFIRMED]**
- File: `docs/markdown/RTLCommon/dataint_crc.md`
- Says: the basic example ties `.load_crc_start(data_valid)` and `.load_from_cascade(1'b0)` and reads out `crc_result`.
- Actually: in `dataint_crc.sv`, data reaches the accumulator *only* via `else if (load_from_cascade) r_crc_value <= w_selected_cascade_output;`. With `load_from_cascade` tied to 0, every `data_valid` pulse just reloads `POLY_INIT`; `crc` becomes `reflect(POLY_INIT)^XOROUT` (for the CRC-32 values shown: `32'hFFFFFFFF ^ 32'hFFFFFFFF = 0`) and stays there. The example outputs a constant, not a CRC of `input_data`.
- Impact: the page's primary usage example is functionally broken; a reader wires it up and gets a constant zero.

### F9 — dataint_crc.md "CRC-64 (ECMA-182)" recipe contradicts the RTL header and the standard
**[CONFIRMED]**
- File: `docs/markdown/RTLCommon/dataint_crc.md`
- Says: CRC-64 (ECMA-182) with `.REFIN(1), .REFOUT(1), .POLY_INIT(64'h0), .XOROUT(64'hFFFFFFFFFFFFFFFF)`.
- Actually: the RTL's own header table lists `CRC-64-ECMA | 0x42F0E… | INIT 0x00… | REFIN 0 | REFOUT 0 | XOROUT 0x00…`, which matches the published CRC-64/ECMA-182 (non-reflected, init 0, xorout 0). The doc's recipe (reflected, init 0, xorout all-ones) matches neither the RTL comment nor ECMA-182, nor CRC-64/XZ (which is reflected but init all-ones).
- Impact: a reader copying the "ECMA-182" configuration gets a check value that no ECMA-182 implementation will reproduce.

### F10 — decoder.md core-logic snippet contains a driver that isn't in the RTL
**[CONFIRMED]**
- File: `docs/markdown/RTLCommon/decoder.md`
- Says: the "Core Logic" block begins with `assign data = 0;  // Initialize all outputs to 0` before the per-bit generate loop, and "Design Notes" claims "Output initialization ensures clean power-up behavior".
- Actually: `rtl/common/decoder.sv` contains only the generate loop (`assign data[i] = (encoded == i) ? 1'b1 : 1'b0;`) — no `assign data = 0;` anywhere. As written, the snippet puts two continuous drivers on every bit of `data` (X in 4-state simulation where they differ, MULTIDRIVEN errors in lint/synthesis).
- Impact: code example misrepresents the RTL and would misbehave if pasted; the "clean power-up" claim is about logic that doesn't exist (the module is purely combinational).

### F11 — ECC docs claim DEBUG output the RTL never produces
**[CONFIRMED]**
- Files: `docs/markdown/RTLCommon/dataint_ecc_hamming_decode_secded.md`, `dataint_ecc_hamming_encode_secded.md`
- Says (decoder): "When `DEBUG != 0`: Displays parity calculations, Shows syndrome values, Reports error detection details". Says (encoder): "When `DEBUG != 0`: Function calls display bit position calculations, Covered bits masks are displayed".
- Actually: the decoder's only DEBUG reference is an empty `initial begin if (DEBUG != 0) begin // Debug initialization if needed end end` with no `$display` anywhere in the module; the encoder never references `DEBUG` outside its parameter declaration. No debug output exists in either.
- Impact: low (simulation-only convenience), but a reader enabling DEBUG gets nothing.

### F12 — cascade_sel documented as one-hot; example drives 8'hFF
**[CONFIRMED, minor]**
- File: `docs/markdown/RTLCommon/dataint_crc.md`
- Says: port table "cascade_sel | CHUNKS | One-hot cascade stage selection"; basic example uses `.cascade_sel(8'hFF),  // Use all chunks`.
- Actually: the select loop `for (int i = 0; i < CH; i++) if (cascade_sel[i]) w_selected_cascade_output = w_cascade[i];` gives highest-set-bit priority, so `8'hFF` happens to select `w_cascade[7]` (the correct final stage) — but it is not one-hot as documented, and the streaming example on the same page does use one-hot. Functionally harmless here, internally inconsistent.
- Impact: minor confusion about the legal encoding.

### F13 — fifo_async.md / fifo_sync.md parameter tables omit real parameters
**[CONFIRMED, gap]**
- Files: `docs/markdown/RTLCommon/fifo_async.md`, `fifo_sync.md`
- Says: fifo_async lists `REGISTERED, DATA_WIDTH, DEPTH, N_FLOP_CROSS, ALMOST_WR_MARGIN, ALMOST_RD_MARGIN`; fifo_sync adds only `INSTANCE_NAME` (which doesn't exist, F3).
- Actually: both RTL modules have `parameter fifo_mem_t MEM_STYLE = FIFO_AUTO` (selecting SRL/BRAM/AUTO memory with different read-latency behavior — the BRAM branch forces registered read even at `REGISTERED=0`), and `fifo_async` additionally has `parameter int USE_JOHNSON = 0` enabling arbitrary (non-power-of-2) depths. Neither appears in the parameter tables; USE_JOHNSON is mentioned only in passing under Related Modules, and MEM_STYLE nowhere.
- Impact: readers can't discover two functional parameters — including the only way to get non-power-of-2 depth and the memory-style control — from the module's own page; the "Restricted to power-of-2 depths only" headline is misleading without the USE_JOHNSON context.

### F14 — FIFO memory-write snippets drop the overflow guard
**[CONFIRMED, minor]**
- Files: `docs/markdown/RTLCommon/fifo_async.md`, `fifo_sync.md`
- Says: both show the memory write as `if (write) begin r_mem[r_wr_addr] <= wr_data; end` (unguarded).
- Actually: RTL in all memory branches of both modules is `if (write && !wr_full)`. The guard is what prevents a write-while-full from corrupting the oldest unread entry.
- Impact: a reader reimplementing from the snippet loses overflow protection; also note the doc's array is named `r_mem` vs RTL `mem` (cosmetic).

### F15 — fifo_sync_multi(_sigmap).md source paths don't match the ground truth
**[SUSPECTED]**
- Files: `docs/markdown/RTLCommon/fifo_sync_multi.md`, `fifo_sync_multi_sigmap.md`
- Says: "**Location:** `rtl/common/`" and References "- `rtl/common/testcode/fifo_sync_multi.sv`" (resp. `fifo_sync_multi_sigmap.sv`).
- Actually: the provided RTL banner for both modules is `formal/common/fifo_sync_multi[_sigmap]/.../src/fifo_sync_multi[_sigmap].sv`. A `rtl/common/testcode/` copy may exist but is not in the material I can check. (The modules' logic itself — concatenation orders `{wr_addr, wr_ctrl, wr_data1, wr_data0}` / `{wr_siga, wr_sigb, wr_sigd, wr_sigc}` and field mappings — matches the docs exactly.)
- Impact: readers following the path may not find the file.

---

## POSSIBLE RTL BUGS / RTL-side issues noticed

1. **Stale RTL header comments (explains F3/F4).** The `fifo_sync.sv` and `fifo_async.sv` header comments themselves advertise "Built-in overflow/underflow detection (simulation only)" and "Write when full is IGNORED (… warning in sim)", but neither module body contains any such `$display` check. The doc errors appear to be faithful transcriptions of stale RTL comments. Not a functional bug, but the RTL comments are wrong.
2. **ECC modules use body localparams in ANSI port widths (portability, SUSPECTED).** `dataint_ecc_hamming_encode_secded` declares `output logic [TotalWidth-1:0] encoded_data` and the decoder `input logic [WIDTH+ParityBits:0] hamming_data`, where `TotalWidth`/`ParityBits` are `localparam`s declared *after* the port list in the module body. Strictly, these identifiers are not in scope for the ANSI header (the LRM-blessed route is the parameter port list); several tools accept it as an extension. It evidently passes the project's own Verilator lint, so treat as a portability wart, not a functional bug.
3. **Not a bug, but worth knowing:** the `fifo_async`/`fifo_sync` `FIFO_BRAM` branch always registers the read path, so `REGISTERED=0` silently behaves as registered in that configuration. The RTL comments say so; the docs don't mention MEM_STYLE at all (F13).

---

## Overall accuracy

The bulk of this part is solid. I verified and found **no errors** in: `count_leading_zeros` and `count_trailing_zeros` (scan direction, output width `$clog2(WIDTH)+1`, every table entry recomputed — e.g. `8'b00110000` → clz 2 / ctz 4), `dataint_checksum`, `dataint_crc_xor_shift(_cascade)` (bit-ordering and stage chaining match), `dataint_parity` (chunk-boundary math for both the even 32/4 and the uneven 30/4 examples recomputed and correct), the Hamming SECDED encode/decode *algorithms* (parity-position, covered-bits, syndrome, and error-classification tables all match the RTL; the 8/13/22-bit width examples are correct), `encoder` and `encoder_priority_enable` (truth tables recomputed), `fifo_control` architecture description apart from F2, and both `fifo_sync_multi*` pages (packing orders exactly right). The defects are concentrated where the docs were written against an older RTL: phantom identifier parameters (`ALGO_NAME`, `INSTANCE_NAME`), advertised simulation checks that were removed, a retired module reference, and the fifo_control cast that regressed to the pre-fix version. F1, F2, F3/F4, F5, and F8 are the ones most likely to waste a reader's time and should be fixed before announcement.