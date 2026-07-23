# Review: `shared_part_02` — RTL AMBA Shared Infrastructure (11 pages)

I checked every parameter table, port list, functional description, and code example against the RTL in this unit, recomputing all numeric claims (counter wrap times, split arithmetic, WRAP address math, mask ranges, CRC behavior). Findings are ordered by reader impact.

---

## Findings

```
[CONFIRMED] The "golden CRC" contract documented for both master characterization blocks is not implemented — the CRC never accumulates
  File:     docs/markdown/RTLAmba/shared/axi4_master_wr_pattern_gen.md (also axi4_master_rd_crc_check.md)
  Says:     "o_expected_crc | output | CRC_WIDTH | Running CRC-32 over the written LFSR stream"
            and in axi4_master_rd_crc_check.md: "A `dataint_crc` accumulates over the regenerated LFSR
            stream ... so `o_actual_crc` equals the writer's `o_expected_crc` on a clean wire."
            Both usage examples conclude with a CRC compare, e.g.
            "assign integrity_ok = (rd_actual_crc == wr_expected_crc) && !rd_data_error;"
  Actually: Both modules instantiate dataint_crc with `.load_from_cascade (1'b0)`. In
            rtl/common/dataint_crc.sv the state register only updates when load_from_cascade=1:
                else if (load_crc_start)    r_crc_value <= POLY_INIT;
                else if (load_from_cascade) r_crc_value <= w_selected_cascade_output;
            So r_crc_value is pinned at POLY_INIT ('1) forever, and the registered output is
            constant: crc = POLY_INIT ^ XOROUT = 32'hFFFF_FFFF ^ 32'hFFFF_FFFF = 32'h0000_0000
            (REFOUT=0 in these instances). One cycle after cfg_start both o_expected_crc and
            o_actual_crc are 0x0000_0000 regardless of data. The slave-side blocks
            (axi4_slave_rd_pattern_gen / axi4_slave_wr_crc_check) do it correctly —
            `.load_from_cascade(ch_load_from_cascade)` gated per beat.
  Impact:   The documented end-to-end CRC check is vacuous: both CRCs are the same constant, so
            `rd_actual_crc == wr_expected_crc` passes on any wire, corrupted or not. The per-beat
            compare (o_data_error) does work, but a reader relying on the documented CRC compare
            gets a check that can never fail. See POSSIBLE RTL BUGS #1.
```

```
[CONFIRMED] axi4_dma_observer's documented default configuration emits no monbus packets; the six parameters that enable the headline features are undocumented
  File:     docs/markdown/RTLAmba/shared/axi4_dma_observer.md
  Says:     Overview promises "an error / interrupt FIFO drained over an AXI-Lite slave-read port,
            a bulk-trace memory dump over an AXI4-burst master-write port"; the What's-inside table
            says each tap is a "pass-through skid + transaction monitor that emits a monbus packet
            on each event". The Parameters table lists no TAP_ENABLE_* entries.
  Actually: rtl/amba/shared/axi4_dma_observer.sv declares six parameters the doc never mentions:
            TAP_ENABLE_ERROR_LOGIC / TIMEOUT / COMPL / THRESHOLD / DEBUG all default 1'b0, only
            TAP_ENABLE_PERF_LOGIC defaults 1'b1 — with the RTL's own comment:
            "Default = perf-only ... Instances that need the completion/error monbus dump path
            (e.g. the standalone observer unit test) override the relevant enable to 1'b1."
            And at every tap instantiation: `.cfg_perf_enable (1'b0), // perf packets off by default`.
            So with the documented defaults the only elaborated cone (perf) is runtime-disabled and
            all others are unelaborated: zero monbus traffic, err FIFO never fills, irq_out never
            asserts, no dump bursts. The doc's own Phase-3 test (dump beats appear) is only possible
            because the test overrides these undocumented parameters.
  Impact:   A reader who instantiates the observer exactly as documented gets a transparent pipe
            with all observability inert and no documented way to turn it on.
```

```
[CONFIRMED] alignment_mask documented as supporting "4KB to 8MB" and value 0xFFFF; the port is 12 bits (max 4KB)
  File:     docs/markdown/RTLAmba/shared/axi_master_rd_splitter.md and axi_master_wr_splitter.md
            (identical "Integration Considerations" text)
  Says:     "12-bit mask supports boundaries: 4KB to 8MB"
            "Common values: 0xFFF (4KB), 0xFFFF (64KB)"
  Actually: RTL port is `input logic [11:0] alignment_mask`. The boundary math is
            next_boundary_addr = (current_addr | mask) + 1, so the largest usable mask is
            0xFFF → 4KB. 0xFFFF needs 16 bits (truncates to 0xFFF = 4KB, not 64KB); an 8MB
            boundary would need mask 0x7FFFFF (23 bits). Recomputation: mask 0xFFF →
            (addr|0xFFF)+1 = next 4KB boundary; there is no way to express anything larger.
  Impact:   A reader configuring a 64KB or larger interleave region writes a value that silently
            truncates to a 4KB boundary, splitting transactions 16–2048× more than intended.
```

```
[CONFIRMED] Documented split-FIFO backpressure does not exist; a full split-info FIFO silently drops records
  File:     docs/markdown/RTLAmba/shared/axi_master_rd_splitter.md and axi_master_wr_splitter.md
  Says:     rd page: "Module continues operation (FIFO write stalls fub_arready)"
            wr page: "FIFO Overflow: Split FIFO can fill if consumer stalls. Backpressure
            propagates to fub_awready"
  Actually: In both modules the split-info gaxi_fifo_sync is instantiated with its ready output
            left unconnected:
                .wr_valid(w_split_fifo_valid), .wr_data(split_fifo_din),
                /* verilator lint_off PINCONNECTEMPTY */
                .wr_ready (),  // Not used
            and fub_arready/fub_awready are functions only of split state, m_axi_arready/awready
            and block_ready. In gaxi_fifo_sync, w_write = wr_valid && wr_ready, so when full the
            record is simply not written — no stall, no error.
  Impact:   A reader relying on the documented stall for lossless split tracking (e.g. error
            correlation) loses records silently once the FIFO fills.
```

```
[CONFIRMED] axi4_slave_wr_crc_check page describes the old single-outstanding B design; the RTL now has a 16-deep B FIFO
  File:     docs/markdown/RTLAmba/shared/axi4_slave_wr_crc_check.md
  Says:     "the id/user are separately latched into r_b_id / r_b_user at WLAST and those drive the
            B channel. B is single-outstanding (r_b_pending), which is safe because the STREAM
            master drains B within the burst period; a higher-rate multi-channel sink would need
            a B FIFO (noted in the RTL)." Design Notes repeat: "Single-outstanding B is deliberate
            but bounded ... The RTL explicitly flags that a faster multi-channel sink needs a B FIFO."
  Actually: rtl/amba/shared/axi4_slave_wr_crc_check.sv contains an inline B FIFO
            (BFIFO_DEPTH=16, r_bfifo_mem), pushed on every WLAST and popped on the B handshake:
                assign fub_axi_bvalid = (r_bfifo_count != '0);
                assign {fub_axi_buser, fub_axi_bid} = r_bfifo_mem[r_bfifo_rptr];
            The RTL comment explains the superseded design: "The old single r_b_pending bit dropped
            the new B whenever a WLAST coincided with a B consume -> ~1 dropped B per channel ...
            The module comment already called for a B FIFO here." No r_b_id/r_b_user/r_b_pending
            signals exist.
  Impact:   The documented limitation (and the signal names a debugger would look for) no longer
            exist; the page's central B-channel section describes hardware that was replaced.
```

```
[CONFIRMED] rd_splitter page: Problem Statement and the worked example analyze the same transaction and reach opposite conclusions
  File:     docs/markdown/RTLAmba/shared/axi_master_rd_splitter.md
  Says:     Problem Statement: "(ADDR=0x0FC0, LEN=7, 8 beats total) ... crosses 4KB boundary at
            0x1000 ... First split: ADDR=0x0FC0, LEN=0 (1 beat to boundary); Second split:
            ADDR=0x1000, LEN=6 (7 beats remaining)".
            The same page's "Transaction Splitting Example Scenario": "Address: 0x0FC0, Length: 7
            (8 beats), Size: 3'b011 (8 bytes per beat) ... End address: 0x0FFF ... Transaction
            crosses boundary: NO".
  Actually: With 8-byte beats, 0x0FC0 + 8×8 = 0x1000, end 0x0FFF < 0x1000 — no crossing (the
            worked example is correct; axi_split_combi computes the same). The 1+7 split is only
            coherent with 64-byte beats (0x0FC0 + 64 = 0x1000), which the page never states — it
            was lifted from the RTL header comment, which does say "(8 beats, 512 bytes total)".
            With the module's own default AXI_DATA_WIDTH=32 (4-byte beats) the example is even
            further off. The wr_splitter page repeats the same example (Problem Statement and
            Response Consolidation Example) with the same unstated 64-byte-beat assumption, though
            nothing there contradicts it explicitly.
  Impact:   Two contradictory worked examples of the module's core function on one page; a reader
            cannot tell which beat size the splitting narrative assumes.
```

```
[CONFIRMED] amba_clock_gate_ctrl page misdescribes the base controller: the counter decrements to zero, it does not increment to the threshold
  File:     docs/markdown/RTLAmba/shared/amba_clock_gate_ctrl.md
  Says:     "Base Controller Operation: ... 2. Increments idle counter when wakeup=0 (idle)
            3. Gates clock when counter >= cfg_cg_idle_count" and, in the gating sequence,
            "3. Idle counter starts incrementing".
  Actually: rtl/common/clock_gate_ctrl.sv loads the counter with cfg_cg_idle_count on
            reset/wakeup/disable and decrements it while idle:
                if (wakeup || !cfg_cg_enable) r_idle_counter <= cfg_cg_idle_count;
                else if (r_idle_counter != 'h0) r_idle_counter <= r_idle_counter - 1'b1;
                wire w_gate_enable = cfg_cg_enable && !wakeup && (r_idle_counter == 'h0);
            Gating occurs when the counter reaches 0. (The doc's own threshold table — "Gate after
            4 consecutive idle cycles" for value 4 — is consistent with decrement-to-zero, so the
            page also contradicts itself.)
  Impact:   Readers of the base controller get the wrong operational model; anyone probing the
            counter will see it count down toward gating, not up toward a threshold.
```

```
[CONFIRMED] wr_splitter page claims all split responses are accepted during consolidation; the final one is gated by fub_bready
  File:     docs/markdown/RTLAmba/shared/axi_master_wr_splitter.md
  Says:     "B Channel Ready: Consolidation mode: m_axi_bready = 1 (accept all responses)" and
            "Critical: Must accept all split responses even if upstream not ready"; also
            "Collection (each B response): Accept response even if fub_bready not asserted".
  Actually: rtl/amba/shared/axi_master_wr_splitter.sv:
                m_axi_bready = fub_bready || !w_is_final_response;
            Non-final responses are always accepted, but the final split response — the one that
            carries the consolidated B upstream — is only accepted when fub_bready is high. The
            downstream slave must hold that last B until the upstream master is ready.
  Impact:   Moderate: a reader designing or verifying the downstream slave per the doc would
            violate AXI (dropping BVALID early) or mis-model backpressure on the final response.
```

```
[CONFIRMED] axi_gen_addr WRAP example computes the wrong wrapped address
  File:     docs/markdown/RTLAmba/shared/axi_gen_addr.md
  Says:     "Example: 4-beat wrap at 0x0FF8 wraps back to 0x0FF8 (not 0x1000)"
  Actually: Recomputation against rtl/amba/shared/axi_gen_addr.sv (size=3 → 8 B/beat, len=3 →
            len_log2=2): wrap_mask = (1<<(3+2))−1 = 0x1F; increment = 8;
            aligned_addr = (0x0FF8+8) & ~7 = 0x1000;
            wrap_addr = (0x0FF8 & ~0x1F) | (0x1000 & 0x1F) = 0x0FE0.
            This matches AXI WRAP semantics (32-byte region [0x0FE0, 0x1000), wrap to the region
            base). The RTL is correct; the doc's "wraps back to 0x0FF8" is wrong.
  Impact:   A reader hand-checking the module gets a wrong expected value and may "fix" correct RTL.
```

```
[CONFIRMED] axi_gen_addr "Used By" section cites modules that do not instantiate it
  File:     docs/markdown/RTLAmba/shared/axi_gen_addr.md
  Says:     "Used By: axi_master_rd_splitter.sv (boundary crossing detection),
            axi_master_wr_splitter.sv (boundary crossing detection), Address generation pipelines"
  Actually: Both splitters instantiate `axi_split_combi` for boundary detection
            (`inst_axi_split_combi`); `axi_gen_addr` is not instantiated anywhere in the RTL
            provided in this unit. It may have users elsewhere in the repo, but the two cited
            users do not exist.
  Impact:   Misleads anyone tracing dependencies or assessing the blast radius of a change.
```

```
[CONFIRMED] Gap: BURST_LEN_MULTIPLE parameter (with a cfg_burst_len legality guard) is undocumented in both master characterization pages
  File:     docs/markdown/RTLAmba/shared/axi4_master_wr_pattern_gen.md and axi4_master_rd_crc_check.md
  Says:     Parameter tables end at STRIDE_WIDTH / aliases; cfg_burst_len documented as
            "Beats per burst (1..256)".
  Actually: Both modules have `parameter int BURST_LEN_MULTIPLE = 1` with a sim-only assertion on
            every cfg_start that cfg_burst_len is a nonzero multiple of it ("A non-conforming
            cfg_burst_len yields a ragged final sub-command ... -> SLVERR/partial write"). Projects
            that set it >1 face a documented-nowhere constraint on cfg_burst_len.
  Impact:   A user of a DRAM harness who hits the $error has no documentation explaining it.
```

```
[CONFIRMED] Gap: several axi4_dma_observer ports are undocumented (cam_clear, FIFO status)
  File:     docs/markdown/RTLAmba/shared/axi4_dma_observer.md
  Says:     The "Port surface" section lists four groups: tap pairs, observer outputs (s_axil_*,
            m_axi_*, irq_out), configuration, and bus-meter controls/outputs.
  Actually: The RTL also has `cam_clear` (synchronous clear for all CAMs — compressor template
            CAM plus every tap's transaction CAM, with an RTL comment saying to pulse it to
            "reset compression stats / unstick stale entries") and status outputs err_fifo_full,
            write_fifo_full, err_fifo_count[15:0], write_fifo_count[15:0]. None appear anywhere in
            the page. (i_hist_metric / i_hist_bin and cfg_compress_en are covered in prose.)
  Impact:   A user cannot discover the CAM-maintenance input or the FIFO-level telemetry from the
            documentation.
```

```
[CONFIRMED] Minor: the "typical ICG cell" example does not match the actual instantiation
  File:     docs/markdown/RTLAmba/shared/amba_clock_gate_ctrl.md
  Says:     "Standard ICG cell instantiation (inside clock_gate_ctrl):
            ICG u_icg (.CLK(clk_in), .EN(gate_enable), .CLK_OUT(clk_out));  // From controller FSM"
  Actually: rtl/common/clock_gate_ctrl.sv: `icg u_icg (.clk(clk_in), .en(~w_gate_enable),
            .gclk(clk_out));` — cell name `icg`, ports clk/en/gclk, and the enable comes from a
            counter, not an FSM (the module has no FSM).
  Impact:   Low — presented as illustrative, but the "(inside clock_gate_ctrl)" caption makes it
            factually wrong about the RTL; confusing for grep-and-trace readers.
```

---

## POSSIBLE RTL BUGS

1. **CONFIRMED — CRC accumulator load tied off in `axi4_master_wr_pattern_gen` and `axi4_master_rd_crc_check`.** Both instantiate `dataint_crc` with `.load_from_cascade(1'b0)`, so the CRC state never advances past `POLY_INIT` and both CRC outputs are constant `32'h0000_0000` one cycle after `cfg_start`. The sibling slave blocks gate `load_from_cascade` with the per-beat strobe (`w_r_beat`/`w_w_beat` && channel match) — that is clearly the intended pattern. Presumably the masters meant `.load_from_cascade(w_w_beat)` / `.load_from_cascade(w_r_beat)`. As shipped, the golden-CRC integrity contract is vacuous (any two runs "match").

2. **SUSPECTED — `axi_master_wr_splitter` response consolidation breaks with multiple outstanding upstream transactions.** In IDLE, a new AW acceptance unconditionally reinitializes the consolidation state (`r_consolidated_resp_status <= OKAY`, `r_received_response_count <= 0`, `r_expected_response_count <= 1/2`, `r_waiting_for_responses <= 0/1`, `r_original_txn_id <= fub_awid`) with no check that the previous transaction's split B responses have all arrived. If upstream issues a new write while split responses are pending, the in-flight consolidation is clobbered: the surviving split responses then pass through unconsolidated, and a worse earlier error is lost. Either the module needs a single-outstanding guard (suppress `fub_awready` while `r_waiting_for_responses`) or the documentation needs to state the restriction — currently neither exists. I could not fully close on end-to-end impact without simulation, hence SUSPECTED.

3. **CONFIRMED (build-gated) — `axi_split_combi` contains a syntactically broken leftover inside ``ifdef DEBUG_AXI_SPLIT``:** a bare line `remaining_len_after_split, remaining_len_after_split + 1);` with no opening call — clearly the tail of a deleted `$display`. Harmless in normal builds; the module will not compile if `DEBUG_AXI_SPLIT` is ever defined.

4. **Minor comment rot — `axi4_slave_wr_crc_check.sv` header** says the per-channel demux is "off the low bits of the W-side wuser (which the STREAM master drives with the burst's channel index)"; the implementation demuxes off `r_wr_id[CIW-1:0]` (captured `awid`), and the doc page correctly describes `awid`. Comment only.

---

## Overall assessment

The unit splits cleanly by page family. The slave-side characterization pages (`axi4_slave_rd_pattern_gen`, `axi4_dma_slaves`) and `axi_bus_meter` are accurate: parameters, ports, FSM behavior, the gapless-burst fix, the counter widths and wrap times (42.9 s / 655 µs at 100 MHz both check out), and even the `cascade_sel = 4'b1000` detail match the RTL. The two master characterization pages are mechanically accurate (ports, FSM, hash pipeline, ID modes all verified) but their central integrity feature — the comparable golden CRCs — describes hardware the RTL does not implement (RTL bug #1), which also undermines both usage examples. The two splitter pages share two factual errors (mask range overstated by 2048×, non-existent FIFO backpressure) and the rd page contradicts itself on its primary worked example; the wr page additionally documents a stale B-channel design for `axi4_slave_wr_crc_check` and overstates response-acceptance during consolidation. The observer page is structurally accurate but omits the six `TAP_ENABLE_*` parameters without which every feature it advertises is inert at default — the most damaging documentation gap in this unit. The clock-gate page's timing tables are right, but its prose model of the base controller (increment vs. decrement) is backwards.