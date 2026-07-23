# Review: common_part_03 (19 docs)

I checked every parameter table, port list, code block, truth table, and numeric example in the 19 pages against the corresponding RTL in `RTL.sv`, recomputing counter sequences, CLZ/CTZ values, Hamming parity-bit counts, chunk boundaries, and FIFO flag arithmetic. Findings are ordered by value.

---

## Findings

```
[CONFIRMED] dataint_crc.md documents a parameter ALGO_NAME that does not exist; four examples will not compile
  File:     docs/markdown/RTLCommon/dataint_crc.md
  Says:     "parameter string ALGO_NAME = "DEADF1F0",  // Algorithm identifier" (module declaration block,
            and "User-Settable Parameters" table), plus examples ".ALGO_NAME("CRC32_IEEE")",
            ".ALGO_NAME("CRC16_CCITT")", ".ALGO_NAME("CRC64_ECMA")",
            ".ALGO_NAME($sformatf("STAGE_%0d", stage))"
  Actually: rtl/common/dataint_crc.sv declares exactly four parameters:
            `parameter int DATA_WIDTH = 64, CRC_WIDTH = 64, REFIN = 1, REFOUT = 1`. No ALGO_NAME.
  Impact:   Any instantiation copied from this page fails elaboration with an unknown-parameter error.
```

```
[CONFIRMED] fifo_sync.md documents a parameter INSTANCE_NAME and simulation error checks that do not exist
  File:     docs/markdown/RTLCommon/fifo_sync.md
  Says:     "- **`INSTANCE_NAME`** - Debug identifier (default: "DEADF1F0")" and
            "Built-in simulation checks: always_ff ... $display("Error: %s write while fifo full, %t",
            INSTANCE_NAME, $time); ..."
  Actually: rtl/common/fifo_sync.sv parameters are MEM_STYLE, REGISTERED, DATA_WIDTH, DEPTH,
            ALMOST_WR_MARGIN, ALMOST_RD_MARGIN. There is no INSTANCE_NAME and no $display anywhere
            in the module.
  Impact:   Setting the documented parameter fails elaboration; the promised overflow/underflow
            simulation warnings do not exist.
```

```
[CONFIRMED] fifo_async.md "Error Detection Features" section shows simulation checks that do not exist
  File:     docs/markdown/RTLCommon/fifo_async.md
  Says:     "## Error Detection Features  ```systemverilog
            always_ff @(posedge wr_clk) begin
                if (!wr_rst_n && (write && wr_full) == 1'b1) begin
                    $display("Error: %s write while fifo full, %t", INSTANCE_NAME, $time); ..."
  Actually: rtl/common/fifo_async.sv contains no such always_ff block and has no INSTANCE_NAME
            parameter.
  Impact:   A documented safety feature is absent from the RTL.
```

```
[CONFIRMED] fifo_async.md omits the USE_JOHNSON and MEM_STYLE parameters and claims a power-of-2-only restriction the RTL lifts
  File:     docs/markdown/RTLCommon/fifo_async.md
  Says:     "**Restricted to power-of-2 depths only** due to Gray code pointer implementation.";
            "Use async_div2 when: Need non-power-of-2 depth";
            Parameters section lists only REGISTERED, DATA_WIDTH, DEPTH, N_FLOP_CROSS, and margins.
  Actually: rtl/common/fifo_async.sv has `parameter int USE_JOHNSON = 0` (1 = arbitrary depth via
            counter_johnson + johnson2bin; a generate-time $error rejects non-power-of-2 DEPTH only
            when USE_JOHNSON=0) and `parameter fifo_mem_t MEM_STYLE = FIFO_AUTO` (SRL/BRAM/AUTO
            memory branches). Neither appears in the doc's Parameters section. Worse, the doc's own
            Related Modules line says "USE_JOHNSON=1: For non-power-of-2 depths ... (replaces the
            retired fifo_async_div2)", contradicting both the headline and the "Use async_div2"
            advice, which points to a retired module.
  Impact:   A reader needing depth 12 would conclude this FIFO cannot do it, or go looking for a
            deleted module. fifo_control.md has the same stale reference: "all FIFO variants
            (sync, async, async_div2)".
```

```
[CONFIRMED] fifo_control.md documents the pre-fix AW'(D) casts that the RTL explicitly corrected to (AW+1)'(...)
  File:     docs/markdown/RTLCommon/fifo_control.md
  Says:     "### Width Casting Fix ... // Fixed: Cast D to AW-bit width to match other operands
            (AW'(D) - wdom_rd_ptr_bin[AW-1:0] + wr_ptr_bin[AW-1:0]) ... The `AW'(D)` casting
            ensures all operands have matching bit widths" — plus AW'(AFT), AW'(AET), and AW'(D)
            in the "Occupancy Calculation", "Almost Empty Logic", and "Count Generation" blocks.
  Actually: rtl/common/fifo_control.sv uses `(AW+1)'(D)`, `(AW+1)'(AFT)`, `(AW+1)'(AET)`, with the
            comment "For depth=16, AW=4: AW'(16) = 4'b0000 (wrong!), (AW+1)'(16) = 5'b10000
            (correct!)".
            Recomputation: DEPTH=16, AW=4 → AW'(16) = 0. The doc's wraparound formula gives
            count = 0 − rd_ptr + wr_ptr instead of 16 − rd_ptr + wr_ptr — off by the full depth,
            and negative counts make the >= AFT / <= AET thresholds fire wrongly.
  Impact:   The doc preserves the exact bug the RTL fixed and presents it as "the fix"; a reader
            reimplementing from the doc gets wrong almost-full/almost-empty/count at wraparound.
            (Minor companion issue: the doc shows `assign count = (w_rdom_ptr_xor) ? ... : ...`
            but the RTL is `assign count = (REGISTERED == 1) ? r_count : w_count;` — count is
            registered in flop mode, which the doc never mentions.)
```

```
[CONFIRMED] debounce.md claims release detection takes DEBOUNCE_DELAY ticks; the RTL releases after a single sample
  File:     docs/markdown/RTLCommon/debounce.md
  Says:     "- **Press detection**: `DEBOUNCE_DELAY` ticks after button stabilizes
            - **Release detection**: `DEBOUNCE_DELAY` ticks after button releases
            - **Asymmetric**: Same delay for both press and release"
  Actually: rtl/common/debounce.sv drives `w_debounced_signals[i] = &r_shift_regs[i]` — an AND of
            the shift register. One '0' sample shifted in on the first long_tick after release
            makes the AND 0, so the output falls after 1 tick, not DEBOUNCE_DELAY ticks. Only the
            press direction requires DEBOUNCE_DELAY consecutive pressed samples. ("Asymmetric:
            Same delay" is also self-contradictory wording.)
  Impact:   A reader expecting symmetric debounce gets output glitches on release bounce: the
            output drops on the first released sample and re-asserts only after 4 stable pressed
            samples.
```

```
[CONFIRMED] counter_ring.md's mathematical description of the rotation is backwards relative to the RTL and the page's own tables
  File:     docs/markdown/RTLCommon/counter_ring.md
  Says:     "ring_out[i] = ring_out[i-1]  for i = 1 to WIDTH-1 / ring_out[0] = ring_out[WIDTH-1]";
            "Feedback: MSB connects back to LSB (no inversion)";
            "Rotation: `{ring_out[0], ring_out[WIDTH-1:1]}` - MSB becomes new LSB"
  Actually: rtl/common/counter_ring.sv: `ring_out <= {ring_out[0], ring_out[WIDTH-1:1]};` —
            new MSB = old LSB; new[i] = old[i+1]. Recompute WIDTH=4 from reset 0001: the doc's
            equation predicts 0010; the RTL produces 1000, which matches the doc's own state table
            ("Step 1 | 1000"). The feedback is LSB→MSB, not MSB→LSB.
  Impact:   The formal description describes the opposite rotation direction and contradicts the
            correct state tables on the same page.
```

```
[CONFIRMED] decoder.md shows an `assign data = 0;` line that is not in the RTL, and claims initialization behavior that does not exist
  File:     docs/markdown/RTLCommon/decoder.md
  Says:     "assign data = 0;  // Initialize all outputs to 0" (Core Logic code block);
            "**Default initialization**: All outputs start at 0";
            "Output initialization ensures clean power-up behavior" (Design Notes).
  Actually: rtl/common/decoder.sv contains only the generate loop `assign data[i] = (encoded == i)
            ? 1'b1 : 1'b0;` — no initialization line. If the doc's line existed alongside the
            generate assigns, every bit would have two drivers (constant 0 and the compare),
            resolving to X exactly on the asserted output.
  Impact:   The doc misquotes the RTL; "clean power-up" is meaningless for this purely
            combinational module; pasting the doc's code into a design yields X on the selected
            output.
```

```
[CONFIRMED] dataint_crc.md's "CRC-64 (ECMA-182)" example parameters contradict the RTL header table and the actual standard
  File:     docs/markdown/RTLCommon/dataint_crc.md
  Says:     "#### CRC-64 (ECMA-182) ... .REFIN(1), .REFOUT(1) ...
            .POLY_INIT(64'h0000000000000000), .XOROUT(64'hFFFFFFFFFFFFFFFF)"
  Actually: The RTL header's own standards table (rtl/common/dataint_crc.sv) lists CRC-64-ECMA as
            REFIN 0, REFOUT 0, XOROUT 0x00..., matching the real ECMA-182 definition
            (non-reflected, xorout 0, init 0). The doc's settings resemble CRC-64/XZ, except that
            variant uses init = all-ones, not 0 — so the example matches neither.
  Impact:   The example does not compute the named standard; a reader validating against published
            CRC-64-ECMA vectors will fail.
```

```
[SUSPECTED] dataint_crc.md basic example passes cascade_sel = 8'hFF although the port is documented as one-hot
  File:     docs/markdown/RTLCommon/dataint_crc.md
  Says:     Port table: "cascade_sel | CHUNKS | One-hot cascade stage selection";
            example: ".cascade_sel(8'hFF),  // Use all chunks"
  Actually: 8'hFF is not one-hot. It happens to work because the selection loop
            `for (int i = 0; i < CH; i++) if (cascade_sel[i]) w_selected_cascade_output = w_cascade[i];`
            is last-match priority, so all-ones selects w_cascade[CH-1] (i.e., all chunks). The
            doc's streaming example builds proper one-hot, so the two examples disagree.
  Impact:   Low — functionally correct here, but it misrepresents the documented encoding and
            relies on an undocumented priority property.
```

```
[SUSPECTED] fifo_sync_multi.md / fifo_sync_multi_sigmap.md cite a source path that does not match the RTL provided
  File:     docs/markdown/RTLCommon/fifo_sync_multi.md (and fifo_sync_multi_sigmap.md)
  Says:     "**Location:** `rtl/common/`" and "### Source Code - `rtl/common/testcode/fifo_sync_multi.sv`"
  Actually: The ground-truth RTL for these modules is located at
            formal/common/fifo_sync_multi/fifo_sync_multi_prove/src/fifo_sync_multi.sv (and the
            _sigmap equivalent). A testcode copy may also exist, but I could not verify it from
            the material provided.
  Impact:   Possibly stale source reference; module content itself matches the docs exactly.
```

---

## POSSIBLE RTL BUGS

1. **`johnson2bin` has dead `clk`/`rst_n` ports, and `fifo_async` falsely claims it is registered.** `rtl/common/johnson2bin.sv` is purely combinational (`always_comb` + two `assign`s); `clk` and `rst_n` are never used. But `rtl/common/fifo_async.sv` instantiates it under the comment `// johnson2bin is registered (takes clk/rst_n)`. In Johnson mode this means the pointer-decode path from the synchronizer through the `leading_one_trailing_one` priority encoders into `fifo_control` is combinational, while the in-source documentation claims a registering stage exists. Not a data-corruption bug, but the comment misleads about timing structure and the unused ports are cruft.

2. **`debounce` only debounces the press direction.** Output = AND of the shift register, so a single released sample clears it. Release-side bounce therefore reaches the output (drop, then re-assert after DEBOUNCE_DELAY stable pressed samples). This is a common simplification, but for a module whose stated purpose is "requiring a stable state for multiple consecutive samples before considering the button state as valid," the asymmetry looks unintended. (Reported above as doc finding #6.)

3. **Observation (low confidence): `dataint_crc` output conditioning is bypassed on `load_crc_start`.** Every cycle except start, `crc <= w_result_xor` (REFOUT reflection + XOROUT). On `load_crc_start`, `crc <= POLY_INIT` raw. For CRC-32 settings (init = all-ones, XOROUT = all-ones) the output shows `0xFFFFFFFF` for one cycle instead of the conditioned `0x00000000`; it self-corrects the following cycle. Minor transient inconsistency, not a functional failure.

---

## Overall accuracy

The bulk of this book is solid: module declarations, port tables, and parameter defaults match the RTL for 17 of 19 pages, and I recomputed every numeric table I could — the CLZ/CTZ truth tables, the one-hot `ctz + clz = WIDTH − 1` identity (including its stated non-one-hot exception), the Hamming parity-bit formulas for WIDTH = 4/8/16/32, the parity chunk boundaries, the ring-counter state tables, and the FIFO full/empty equations — all correct. The damaging defects are concentrated and mostly of one kind: the docs lagging or inventing RTL features. Three pages document things that do not exist (`ALGO_NAME`, `INSTANCE_NAME`, and simulation error checks in both FIFO pages), with examples that would fail elaboration verbatim. `fifo_control.md` enshrines the pre-fix width-cast bug as "the fix," and `fifo_async.md` simultaneously hides the `USE_JOHNSON` parameter, overstates the power-of-2 restriction, and points readers to a retired module. The `debounce` timing claims and the `counter_ring` rotation equations are plain wrong relative to the RTL — the latter contradicting correct tables on the same page. Fixing these nine confirmed items would bring the book close to fully accurate.