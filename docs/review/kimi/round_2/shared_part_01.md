# Review: shared_part_01 (GAXI modules + shared-infrastructure overviews)

I verified every port list, parameter table, and behavioral claim in the 8 GAXI module docs against the provided RTL, recomputed the latency/count/drop-mechanics by tracing the FSMs and pointer logic, and cross-checked the three overview/status pages for internal consistency. Findings are ranked by severity.

---

## Findings

### 1. The flagship "zero-latency bypass" of the skid buffer does not exist — minimum latency is 1 cycle

```
[CONFIRMED] "Zero-latency bypass" claim contradicted by fully registered RTL
  File:     docs/markdown/RTLAmba/gaxi/gaxi_skid_buffer.md (also README.md, gaxi_skid_buffer_struct.md, gaxi_skid_buffer_async.md, gaxi_regslice.md)
  Says:     "✅ **Zero-Latency Bypass:** When empty, data appears at output immediately (0 cycles)";
            latency table "| Empty → Read | 0 | Immediate (combinatorial) |";
            "**Key Observations:** - Write at cycle N → Read valid at cycle N";
            "Critical Paths: **Write → Read (empty):** Combinatorial path"
  Actually: gaxi_skid_buffer.sv drives the read side entirely from registers:
              assign rd_data = r_data[0];            // r_data is a flop array
            and rd_valid is assigned inside `ALWAYS_FF_RST`. Tracing a write to
            an empty buffer: w_wr_xfer in cycle N → slot 0 loaded and
            rd_valid set at the N/N+1 edge → read handshake completes in cycle
            N+1. There is no combinational path from wr_data/wr_valid to
            rd_data/rd_valid anywhere in the module. Minimum write→read
            latency is exactly 1 clock, identical to gaxi_fifo_sync mux mode.
  Impact:   The module's defining feature is absent. Every document built on it
            is off by one cycle: README.md "Performance Characteristics" row
            "| gaxi_skid_buffer | 0 cycles | 1 cycle |"; gaxi_skid_buffer_async.md
            "| Skid buffer (empty) | 0 cycles |" (so "Total (empty path) 3-5" is
            really ~4-6); gaxi_skid_buffer_struct.md "Zero-Latency Bypass:
            Identical performance to base skid buffer"; and gaxi_regslice.md's
            comparison table ("gaxi_skid_buffer: 0-1 cycle (variable), Bypass
            Path ✅ Yes (when empty)") plus its selection guidance ("skid_buffer:
            Latency-sensitive paths") — the stated reason to choose a skid buffer
            over a regslice evaporates. All six WaveDrom scenario descriptions in
            gaxi_skid_buffer.md ("Write at cycle N → Read valid at cycle N")
            describe behavior the RTL does not produce.
```

### 2. gaxi_drop_fifo_sync documents two status ports that do not exist; its own example would not compile

```
[CONFIRMED] almost_full / almost_empty ports documented but not in RTL
  File:     docs/markdown/RTLAmba/gaxi/gaxi_drop_fifo_sync.md
  Says:     Key Features: "FIFO count and almost-full/almost-empty flags";
            Status Signals table: "| `almost_full` | output | 1 | ..." and
            "| `almost_empty` | output | 1 | ..."; usage example connects
            ".almost_full (almost_full), .almost_empty(almost_empty)"
  Actually: The RTL port list is: axi_aclk, axi_aresetn, wr_valid, wr_ready,
            wr_data, rd_ready, count, rd_valid, rd_data, drop_valid, drop_ready,
            drop_count, drop_all. The almost flags exist only as internal wires
            (r_wr_almost_full, r_rd_almost_empty from fifo_control) and are never
            exported.
  Impact:   A reader instantiating per the doc gets an elaboration error
            (no such port); a reader designing flow control around almost_full
            must add it themselves.
```

```
[CONFIRMED] README drop-FIFO example uses nonexistent port drop_count_valid
  File:     docs/markdown/RTLAmba/gaxi/README.md
  Says:     ".drop_count      (drop_n_packets),  // Drop N oldest entries
             .drop_count_valid(drop_trigger),
             .drop_all        (flush_fifo),"
  Actually: gaxi_drop_fifo_sync has no `drop_count_valid` port; the drop
            handshake is `drop_valid` / `drop_ready` (both omitted from the
            example). The module's own page (gaxi_drop_fifo_sync.md) documents
            drop_valid/drop_ready correctly, so the README also contradicts the
            sibling page.
  Impact:   Example fails to elaborate ("port not found"); even after renaming,
            drop_valid/drop_ready left unconnected means the drop function
            silently never works.
```

### 3. Phantom `INSTANCE_NAME` parameter documented on six modules that do not have it

```
[CONFIRMED] INSTANCE_NAME parameter does not exist in any of these RTL modules
  Files/quotes:
    gaxi_skid_buffer.md:        "parameter     INSTANCE_NAME = "DEADF1F0"," (interface
                                block, parameters table, and Error Checking code)
    gaxi_skid_buffer_struct.md: "parameter      INSTANCE_NAME = "DEADF1F0",  # Debug
                                identifier" plus Key Feature "Debug Support: Instance
                                naming and transaction logging"
    gaxi_fifo_sync.md:          "| `INSTANCE_NAME` | "DEADF1F0" | Debug instance name |"
    gaxi_fifo_async.md:         "parameter     INSTANCE_NAME = "DEADF1F0"" (interface block)
    gaxi_skid_buffer_async.md:  "parameter     INSTANCE_NAME = "DEADF1F0"" (interface
                                block + parameters table)
    gaxi_regslice.md:           "parameter     INSTANCE_NAME = "REGSL1D"" (interface
                                block + parameters table)
  Actually: None of the six modules declares INSTANCE_NAME. Verified against each
            RTL parameter list, e.g. gaxi_fifo_async: MEM_STYLE, REGISTERED,
            DATA_WIDTH, DEPTH, USE_JOHNSON, N_FLOP_CROSS, ALMOST_*_MARGIN, DW, D,
            AW, JCW, N; gaxi_regslice: DATA_WIDTH, DW only. (The two newest docs,
            gaxi_drop_fifo_sync.md and gaxi_skid_buffer_dbldrn.md, correctly omit
            it — this looks like stale template boilerplate copied across the
            six older pages.)
  Impact:   Setting the documented parameter fails elaboration. A reader may also
            expect the "debug instance naming / transaction logging" that the docs
            advertise; nothing of the kind exists.
```

### 4. Documented simulation assertion blocks that do not exist in the RTL

```
[CONFIRMED] Error-checking code quoted in docs is absent (RTL check blocks are empty)
  Files/quotes:
    gaxi_skid_buffer.md — an entire "Error Checking" section:
        'if ((wr_valid && !wr_ready) && (wr_xfer)) begin
             $display("Error: %s write while buffer full, %t", INSTANCE_NAME, $time);'
      RTL gaxi_skid_buffer contains no assertion code at all. (The quoted logic is
      also self-contradictory — wr_xfer = wr_valid & wr_ready can never be true when
      !wr_ready.)
    gaxi_fifo_async.md — "Error Checking / Simulation-only assertions catch protocol
      violations" with two $display blocks. RTL gaxi_fifo_async contains only:
          always_ff @(posedge axi_rd_aclk) begin
              if (w_read && r_rd_empty) begin
              end
          end
      i.e. an empty shell (see POSSIBLE RTL BUGS).
    gaxi_regslice.md — "Assertions: Built-in simulation checks ... Detect backpressure
      hot spots (wr_valid && !wr_ready) ... Detect invalid reads (rd_ready && !rd_valid)
      ... Sanity check count > 4'd1". RTL implements only the count>1 $error; the two
      protocol checks do not exist.
  Impact:   Readers relying on documented protocol-violation detection to debug
            integration issues get nothing.
```

### 5. Wrong parameter defaults and a wrong port width in gaxi_drop_fifo_sync.md

```
[CONFIRMED] Documented defaults disagree with RTL
  File:     docs/markdown/RTLAmba/gaxi_drop_fifo_sync.md
  Says:     "| `DATA_WIDTH` | int | 32 | ..." and "| `DEPTH` | int | 16 | FIFO depth
            (must be power of 2) |"
  Actually: RTL: "parameter int DATA_WIDTH = 4," and "parameter int DEPTH = 4,"
  Impact:   Anyone instantiating with defaults and connecting a 32-bit bus per the
            doc silently truncates to 4 bits; depth assumptions (count width,
            drop_count range) are off by 4x.

[CONFIRMED] drop_count width documented as fixed 8 bits
  File:     docs/markdown/RTLAmba/gaxi_drop_fifo_sync.md
  Says:     "| `drop_count` | input | 8 | Number of entries to drop |"
  Actually: RTL: "input logic [AW:0] drop_count" with AW = $clog2(DEPTH), i.e.
            width = $clog2(DEPTH)+1 (5 bits at the doc's own default DEPTH=16).
  Impact:   Testbench/driver written for an 8-bit port mis-sizes the signal.
```

### 6. Documented drop-clamping behavior is not implemented

```
[CONFIRMED] "FIFO count decreases by min(N, current_count)" — RTL does not clamp
  File:     docs/markdown/RTLAmba/gaxi_drop_fifo_sync.md
  Says:     "**Result**: FIFO count decreases by min(N, current_count)"
  Actually: The drop path is counter_bin_load with .add_enable(w_use_drop_ptr &&
            !drop_all), .add_value(drop_count) — an unconditional add with wrap at
            2*DEPTH. There is no comparison against occupancy anywhere. The RTL's
            own header says "drop_count must be <= current FIFO count (checked in
            simulation)" — but no such check exists in the module (see POSSIBLE
            RTL BUGS). Dropping more entries than are present advances the read
            pointer past the write pointer and corrupts count/empty state (e.g.
            D=16, wr=5, rd=3, drop 5 → reported count becomes 29).
  Impact:   A reader who believes the clamp exists will hit silent FIFO corruption
            instead of a benign saturating drop.
```

### 7. README "depth rules" note contradicts the sync-FIFO doc and the RTL

```
[CONFIRMED] README says all FIFOs need power-of-2 depth; gaxi_fifo_sync does not
  File:     docs/markdown/RTLAmba/gaxi/README.md
  Says:     "The FIFOs (`gaxi_fifo_sync`, `gaxi_drop_fifo_sync`, `gaxi_fifo_async`)
            address memory with a binary pointer and need a power of 2 -- except
            `gaxi_fifo_async` with `USE_JOHNSON=1`..."
  Actually: gaxi_fifo_sync.md says "**Arbitrary Depth:** Any depth supported (power
            of 2 optimal)" and the RTL header says "Parameterized Synchronous FIFO
            -- This works with any depth". The implementation backs this: counter_bin
            wraps at MAX=D for any D, and fifo_control contains explicit non-power-of-2
            fixes (the (AW+1)'(D) casts with comments "For depth=16, AW=4: AW'(16) =
            4'b0000 (wrong!), (AW+1)'(16) = 5'b10000 (correct!)").
  Impact:   Reader unnecessarily restricts gaxi_fifo_sync depths; the "not a
            contradiction" note is itself contradicted two pages later.
```

### 8. gaxi_regslice.md comparison table misstates the skid buffer's depth

```
[CONFIRMED] Skid buffer depth given as "1 entry (+ skid slot)"
  File:     docs/markdown/RTLAmba/gaxi/gaxi_regslice.md
  Says:     "| **Depth** | 1 entry | 1 entry (+ skid slot) |"  (regslice vs skid_buffer)
  Actually: gaxi_skid_buffer has parameter DEPTH = 2 default, intended {2,4,6,8}
            ("Depth is expected to be one of {2, 4, 6, 8}" in the RTL header; its
            own doc says "Elastic Buffering: Depth 2-8 entries"). Storage is DEPTH
            full entries, not 1 + a skid slot.
  Impact:   Understates skid-buffer capacity; also feeds the incorrect regslice-vs-skid
            selection guidance (together with Finding 1).
```

### 9. shared/README.md contradicts itself (and DOCUMENTATION_STATUS.md) on monitor packet width

```
[CONFIRMED] 64-bit vs 128-bit monitor packet, same page disagrees with itself
  File:     docs/markdown/RTLAmba/shared/README.md
  Says:     axi_monitor_reporter section: "Purpose: Generate standardized 128-bit
            `monitor_packet_t` records" with a "Packet Format (128 bits)" table
            ("[127:124] Packet Type ..."); but the monbus_arbiter section says
            "parameter int DATA_WIDTH = 64 // Monitor bus width", the
            axi_monitor_base section says "Monitor bus output: 64-bit packets",
            and the Summary says "Standardized 64-bit event packets".
            DOCUMENTATION_STATUS.md sides with 128: "128-bit packet + 64-bit
            side-band timestamp, carried atomically through a 192-bit skid".
  Actually: Cannot be resolved from this part's RTL (monitor modules are in the
            monitor book), but the page cannot be right in both places.
  Impact:   Anyone sizing a monbus interconnect or writing a packet decoder gets
            opposite answers depending on which paragraph they read.
```

### 10. Smaller internal inconsistencies in shared/README.md

```
[CONFIRMED] "AXI Utilities (5 modules)" lists four
  File:     docs/markdown/RTLAmba/shared/README.md
  Says:     "### AXI Utilities (5 modules)" followed by a 4-row table
            (axi_gen_addr, axi_master_rd_splitter, axi_master_wr_splitter,
            axi_split_combi).
  Impact:   Cosmetic miscount, but trivially fixed.

[SUSPECTED] axi_split_combi described as two different things on two pages
  Files:    docs/markdown/RTLAmba/shared/README.md — "Combined splitter |
            Bidirectional split (read + write)" / "Purpose: Combined read + write
            splitter ... Bidirectional split (all 5 AXI channels)"
            docs/markdown/RTLAmba/shared/DOCUMENTATION_STATUS.md — "axi_split_combi.sv
            - Pure combinational split decision logic ... Used by both read and
            write splitters"
  Actually: Module not in this part's RTL, so I cannot say which description is
            right; they are mutually exclusive (a bidirectional 5-channel splitter
            vs. a combinational decision helper).
  Impact:   Reader cannot tell whether to instantiate it as a splitter or as a
            helper inside one.

[SUSPECTED] CDC section retained in full despite "moved" note
  File:     docs/markdown/RTLAmba/shared/README.md
  Says:     Note: "Clock domain crossing modules have moved ... documented under
            [RTLAmba/cdc](../cdc/README.md)" — yet the page still carries a complete
            cdc_4_phase_handshake section (parameters, FSM states, timing, example)
            below. The retained section looks like stale pre-move content; I could
            not verify it against RTL (CDC modules are not in this part).
  Impact:   Two potentially divergent copies of the same documentation.

[SUSPECTED] axi_gen_addr WRAP formula is not a correct next-address function
  File:     docs/markdown/RTLAmba/shared/README.md
  Says:     "WRAP (0x10): boundary = (len + 1) << size;
            next_addr = (curr_addr + (1 << size)) & ~(boundary - 1);"
  Actually: As written this aligns down to the wrap boundary on every beat, e.g.
            curr=0x1000, size=2, len=3 → (0x1004) & ~0xF = 0x1000 instead of
            0x1004. It is only correct at the wrap point. The actual RTL (not
            provided in this part) presumably computes the standard wrapped
            increment; the documented formula is wrong as stated.
  Impact:   A reader reimplementing burst math from the doc produces wrong
            addresses on every non-wrapping beat of a WRAP burst.
```

### 11. Minor confirmed mismatches

```
[CONFIRMED] Skid buffer internals described as a packed vector; RTL uses an unpacked array
  File:     docs/markdown/RTLAmba/gaxi/gaxi_skid_buffer.md
  Says:     "logic [BUF_WIDTH-1:0] r_data;       // [DEPTH * DATA_WIDTH - 1 : 0]"
  Actually: RTL (post-2026-04-23 refactor): "logic [DW-1:0] r_data [DEPTH];" — an
            unpacked array of per-slot registers, refactored precisely to avoid the
            dynamic part-select the doc's description implies.
  Impact:   Low; misleads anyone reading the doc to understand timing/area behavior.

[CONFIRMED] "Skid buffer ... Fixed depth (typically 2-4 entries)" in async wrapper
  File:     docs/markdown/RTLAmba/gaxi/gaxi_skid_buffer_async.md
  Actually: gaxi_skid_buffer_async instantiates gaxi_skid_buffer with only
            .DATA_WIDTH(DW); DEPTH takes its default of 2, always. "Typically 2-4"
            should read "fixed at 2".
  Impact:   Low.

[CONFIRMED] USE_JOHNSON parameter of gaxi_skid_buffer_async undocumented
  File:     docs/markdown/RTLAmba/gaxi/gaxi_skid_buffer_async.md
  Actually: RTL exposes "parameter int USE_JOHNSON = 0" with an explicit comment:
            "Must be exposed here: a wrapper that hides it cannot be built at a
            non-power-of-2 depth." The doc's interface block and parameter table
            omit it (while including the phantom INSTANCE_NAME — Finding 3).
  Impact:   Users of the wrapper cannot discover how to build non-power-of-2
            depths, the very reason the parameter exists.

[CONFIRMED] README protocol overview gives count width as [3:0] for all modules
  File:     docs/markdown/RTLAmba/gaxi/README.md
  Says:     "Optional Monitoring: - `count[3:0]` - Current FIFO/buffer occupancy"
  Actually: True for the skid buffers and regslice ([3:0]); the FIFOs output
            count as [AW:0] = $clog2(DEPTH)+1 bits.
  Impact:   Low; width mismatch for anyone wiring FIFO count to a 4-bit signal.
```

---

## POSSIBLE RTL BUGS

1. **Empty error-checking blocks in `gaxi_fifo_sync` and `gaxi_fifo_async`.** Both modules contain "overflow/underflow error checking" always blocks with completely empty bodies (`if (w_write && r_wr_full) begin end`). Either the documented `$display`/`$error` checks were stripped (leaving dead code that also orphaned the docs' INSTANCE_NAME references) or the checks were never implemented. Recommend implementing the checks inside `translate_off` regions or deleting the shells.

2. **`gaxi_drop_fifo_sync` has no guard against over-drop.** The header comment promises "drop_count must be <= current FIFO count (checked in simulation)", but the module contains no such check, and the pointer math (unconditional add via `counter_bin_load`) corrupts FIFO state if it happens (recomputation in Finding 6). Either an assertion or the clamp the documentation claims (`min(N, count)`) is needed. Related dead code: the write-pointer instance has `load = w_use_drop_ptr && drop_all` with `load_value = r_wr_ptr_bin` — loading the write pointer with its own current value, i.e. a no-op.

3. **`gaxi_skid_buffer_dbldrn` still uses the dynamic indexed part-select pattern** (`r_data[(DW * r_data_count) +: DW] <= wr_data;`) that the `gaxi_skid_buffer` header explicitly identifies as a 100 MHz Artix-7 timing failure mode and was refactored away from in the base module ("per-bit multipliers (CARRY4 chain) and a MUXF7-rooted mux tree 17 logic levels deep"). Functionally correct, but likely inherits the timing problem the sibling module just fixed.

---

## Overall accuracy

The eight module pages are structurally solid — port names, handshake descriptions, the drop-FIFO FSM timing, the double-drain transfer table, and the regslice behavior all match the RTL precisely, and `gaxi_skid_buffer_dbldrn.md` is essentially flawless. The damage is concentrated in two systematic problems: (1) the central "zero-latency bypass" feature advertised for the skid-buffer family is not present in the current registered implementation, invalidating the latency tables on five pages and the regslice-versus-skid selection guidance; and (2) stale template boilerplate — a phantom `INSTANCE_NAME` parameter and phantom `$display` assertion blocks — was copied across six of the eight module docs and describes debug infrastructure that does not exist. `gaxi_drop_fifo_sync.md` additionally invents two status ports, gets both parameter defaults wrong, and claims a drop-count clamp the hardware does not perform. The `shared/` overview pages read as having drifted from the implementation: the 64-bit vs 128-bit monitor-packet contradiction, the module-count error, and the retained-but-"moved" CDC section should be reconciled with the monitor and CDC books before release.