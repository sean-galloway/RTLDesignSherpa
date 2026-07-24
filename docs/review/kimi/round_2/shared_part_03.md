# Review: shared_part_03 (12 pages, 10 modules + 6 dependencies verified)

I checked every parameter table, port list, bit-ordering claim, worked example, and behavioral description against the provided RTL. The `clock_gated_variants.md` guide covers modules (`amba_clock_gate_ctrl`, `clock_gate_ctrl`, all `_cg` wrappers) whose RTL is **not included in this unit**, so it could only be checked for internal consistency — noted at the end.

---

## Findings

```
[CONFIRMED] Latency-histogram doc claims straddling completions are measured; the RTL drops all completions during freeze
  File:     docs/markdown/RTLAmba/shared/axi_perf_latency_hist.md
  Says:     "Only histogram accumulation freezes on `i_freeze`; `r_time` keeps counting so a
            transaction whose command was accepted before the window closed and whose completion
            arrives just after still yields a correct latency."
            (also Key Features: "Free-running (non-frozen) timestamp so latencies straddling the
            window boundary stay correct", and the Free-Running Timestamp section: "Only the
            histogram accumulation is frozen.")
  Actually: In axi_perf_latency_hist.sv the FIFO push/pop AND the stage-0 event capture are both
            gated by freeze:
                if (!i_freeze) begin ... w_push / w_pop / r_burst_active ... end
                s0_valid <= w_ev && !i_freeze;
            A completion that handshakes while i_freeze=1 records nothing — no FIFO pop, no
            pipeline event, no histogram increment. The free-running r_time cannot rescue the
            measurement because the event itself is discarded. So far more than "histogram
            accumulation" is frozen, and no straddling latency is ever produced. The doc even
            contradicts itself three sections later: "Stage 0: ... Gated by i_freeze (a frozen
            window captures no new events)."
  Impact:   A reader believes transactions in flight at window close are counted with correct
            latencies. They are silently dropped, so o_hist_total undercounts and the tail bins
            lose exactly the longest transactions — the ones a tail-latency tool exists to find.
```

```
[CONFIRMED] sdpram_slave.md describes a legacy backend (sdpram_slave.sv with WR_PROTOCOL/RD_PROTOCOL string parameters) that does not exist in the RTL
  File:     docs/markdown/RTLAmba/shared/sdpram_slave.md
  Says:     "One common backend (sdpram_slave.sv) with the BRAM port-A/B glue, bulk-clear FSM,
            burst tracker, and the two protocol-skid generate blocks (gated by WR_PROTOCOL /
            RD_PROTOCOL string parameters)." and "Four thin wrappers ... instantiate the backend
            with the matching parameter setting" and "The bare sdpram_slave remains directly
            callable..."
  Actually: No module sdpram_slave and no WR_PROTOCOL/RD_PROTOCOL parameters appear anywhere in
            the provided RTL. Each wrapper (e.g. sdpram_slave_axi4_axi4.sv) directly instantiates
            the native leaf skids (axi4_slave_wr / axi4_slave_rd, or axil4_slave_wr/rd) plus
            sdpram_core; the AXIL single-beat tie-offs live in the wrapper at the core boundary.
            The other four sdpram pages in this same book (sdpram_core.md and the three sibling
            wrapper pages) describe exactly this core+wrapper architecture, so this page is both
            unsupported by the RTL and contradicted by its own sibling pages.
  Impact:   A reader hunts for a module and parameterization that isn't there, and the page's
            "Why four wrappers + a backend?", Migration, and Test sections all build on the
            phantom backend.
```

```
[CONFIRMED] o_dbg_vr bit map is exactly reversed
  File:     docs/markdown/RTLAmba/shared/sdpram_slave.md
  Says:     "o_dbg_vr | 10 | External {aw,w,b,ar,r}_{valid,ready} (AW = [9:8], W = [7:6],
            B = [5:4], AR = [3:2], R = [1:0])"
  Actually: All four wrappers assign
                o_dbg_vr = {rready, rvalid, arready, arvalid, bready, bvalid,
                            wready, wvalid, awready, awvalid};
            so the true map is R = [9:8], AR = [7:6], B = [5:4], W = [3:2], AW = [1:0] —
            the precise reverse of the table. The sibling wrapper pages give the concatenation
            in the correct (RTL-matching) order, so this page also contradicts them.
  Impact:   Anyone decoding the debug pairs during debug reads the wrong channel's handshake.
```

```
[CONFIRMED] o_cfg_done_clear documented as a pulse; the RTL drives a sticky level
  File:     docs/markdown/RTLAmba/shared/sdpram_slave.md
  Says:     "o_cfg_done_clear (output) — pulses high when the clear FSM finishes."
  Actually: In sdpram_core.sv, r_done_clear is set on clr_last and is only cleared when a new
            i_cfg_start_clear is accepted (or on reset):
                CLR_BUSY: if (clr_last) begin r_clr_state <= CLR_IDLE; r_done_clear <= 1'b1; end
            It stays high indefinitely after the walk completes. (sdpram_core.md's wording —
            "Asserted when the clear walk has finished" — is consistent with the RTL.)
  Impact:   A consumer designed for a one-cycle strobe (edge detect, pulse handshake) is
            mis-designed; the two pages also disagree.
```

```
[CONFIRMED] WRAP handling mischaracterized: "$error"/"rejected"/"treated as INCR" are all wrong
  File:     docs/markdown/RTLAmba/shared/sdpram_slave.md
  Says:     "WRAP (2'b10) is rejected by a SIMULATION-only $error and treated as INCR in synth
            (the BRAM glue advances linearly)."
  Actually: The wrappers use `assert (s_axi_awburst != 2'b10) else $warning(...)` — a $warning,
            not $error — and the burst is accepted and proceeds normally. In axi_gen_addr.sv,
            burst=2'b10 selects the computed wrap_addr, not the INCR path, so it is not
            "treated as INCR" either. The wrapper pages' phrasing ("assertion flagging
            unvalidated WRAP bursts", "warns at the sim boundary") is the accurate version.
  Impact:   Minor — misstates the severity of the sim check and the synth-time behavior.
```

```
[SUSPECTED] Test section describes a regression against the nonexistent bare backend
  File:     docs/markdown/RTLAmba/shared/sdpram_slave.md
  Says:     "val/amba/test_sdpram_slave.py exercises the bare sdpram_slave backend across all
            four (WR_PROTOCOL, RD_PROTOCOL) combinations via @pytest.mark.parametrize."
  Actually: The test file is not in the review material, but since no sdpram_slave module with
            WR_PROTOCOL/RD_PROTOCOL parameters exists in the RTL, this description cannot match
            the current code. Presumably stale along with the rest of the page.
  Impact:   A reader running the documented command may find the test does something else.
```

---

## POSSIBLE RTL BUGS

1. **`axi_split_combi.sv` — broken `DEBUG_AXI_SPLIT` block (SUSPECTED).** The provided source contains, inside `` `ifdef DEBUG_AXI_SPLIT ``, an `always_ff` body that is just the fragment `remaining_len_after_split, remaining_len_after_split + 1);` — no `$display`, an unmatched close paren. As shown, the module will not compile with `DEBUG_AXI_SPLIT` defined. Harmless in normal builds (preprocessed out), but the doc's "Debug Support" section describes console output this block can no longer produce. Worth a check against the real source in case this is a snapshot artifact.

2. **`sdpram_core.sv` — latent WRAP-address bug (SUSPECTED, currently masked).** Both `axi_gen_addr` instances are fed `.len(r_wr_beats_left)` / `.len(r_rd_beats_left)` — the *decrementing* beats-remaining counter — rather than the latched burst length. `len` only feeds the WRAP mask computation, so INCR/FIXED are unaffected, but for a WRAP burst the wrap boundary would shrink after every beat. WRAP is sim-gated by assertion today, so this only matters when someone acts on the "not yet validated" note and tries to enable WRAP.

---

## Overall accuracy

Most of this part is in good shape. I verified line-by-line and found **no defects** in `axi_split_combi.md` (both worked examples recompute exactly: 0x0FC0/len=7 → no split; len=8 → split_len=7, remaining=0), `axis4_master_pattern_gen.md` and `axis4_slave_pattern_check.md` (every parameter default, the FSM behavior, tlast cadence, pre-advance compare semantics, and sticky error/pkt-count clearing all match), `axis_bus_meter.md` (bucket decode, 42.9 s wrap figure at 2^32/100 MHz, never-incremented `r_ch_idle`, overflow packing all confirmed), `sdpram_core.md`, and all four wrapper pages (port lists, tie-off values, `o_dbg_vr`/`o_dbg_fub_vr` ordering, per-wrapper WRAP-assertion placement, and the axil_axil `CORE_ID_WIDTH=1` detail are all correct). The damage is concentrated in two pages: `axi_perf_latency_hist.md` (the freeze/straddle claim — the most consequential finding here because it misstates what the instrument measures) and `sdpram_slave.md` (stale legacy architecture plus three smaller factual errors). `clock_gated_variants.md` could not be verified against RTL in this unit since none of its modules' RTL was provided; its internal arithmetic is consistent (22 transport + 12 monitor = 34, of which 26 gate) and its Known Gaps section matches the already-documented `*_mon_cg` gap, so I found nothing new to report there.