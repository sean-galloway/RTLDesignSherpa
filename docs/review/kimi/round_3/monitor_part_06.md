# Review: monitor_part_06 (monbus CAMs, compressor, group core/family, halfbeat packer, trans CAM)

Seven pages reviewed against the provided RTL. The compressor page has a cluster of stale descriptions from before the pipelined-CAM / per-template-timestamp revision; the CAM, packer, and trans-CAM pages are largely accurate. Findings ranked roughly by impact.

---

## Findings

### 1. Stale global-`r_last_ts` delta scheme described in four places — contradicts the page's own per-template section and the RTL

```
[CONFIRMED] monbus_compressor.md describes a global r_last_ts delta baseline that no longer exists in the RTL
  File:     docs/markdown/RTLAmba/monitor/monbus_compressor.md
  Says:     "delta_ts = (current_source_ts - r_last_ts) & ((1 << 60) - 1)" and
            "r_last_ts is updated on **every** record encoded (Tier-0 and Tier-1 alike),
            so the decoder can rebuild the absolute timestamp from a chain of deltas"
            (§ "2. Delta-encoded timestamp");
            mermaid: DELTA["delta_ts =<br/>(in_source_ts - r_last_ts)<br/>mod 2^60"];
            decision tree: "Compute delta_ts = (in_source_ts - r_last_ts) & ((1 << 60) - 1)"
            and "r_last_ts ← in_source_ts. Done." (formats A, B, C)
  Actually: There is no r_last_ts in monbus_compressor.sv. delta_ts is computed per
            template from the matched CAM entry's stored 24-bit timestamp:
              assign pipe_delta_ts = {{(TS_BITS-TS_STORE_BITS){1'b0}},
                                      (m_src_ts_lo - pipe_res_old_ts)};
            The same page's later section "Per-template delta_ts" says so itself:
            "Earlier revisions measured delta_ts against a single global r_last_ts...
            The current encoder measures delta_ts against the matched CAM entry's
            stored last_ts". The two halves of the document disagree.
  Impact:   Anyone implementing a decoder (or auditing the format) from §2 / the
            decision tree would chain deltas against a global per-record baseline.
            The real format chains per-template against the CAM entry's low-24 ts.
            For interleaved multi-source traffic these produce different encodings.
```

### 2. Compressor doc describes the old 3-action CAM port; the production `monbus_cam_pipe` has no action port at all

```
[CONFIRMED] "CAM exposes three actions / FSM issues TOUCH/INSTALL/NONE" is stale
  File:     docs/markdown/RTLAmba/monitor/monbus_compressor.md
  Says:     "The CAM exposes three actions on its single access port:
            ACTION_NONE 2'b00 / ACTION_TOUCH 2'b01 / ACTION_INSTALL 2'b10 ...
            The compressor's FSM issues TOUCH after Tier-1 hits, INSTALL after
            Tier-0 escapes caused by a CAM miss, and NONE during the slot 1 /
            slot 2 of a Tier-0 RAW expansion."
            Decision tree: "Issue ACTION_INSTALL on the CAM (key, event_data)."
            The architecture mermaid also labels the block "monbus_cam" with
            access_hit/access_idx/access_old_data (no old_ts).
  Actually: The instantiated CAM is monbus_cam_pipe (u_cam_pipe). Its ports are
            access_en/access_key/access_new_data/access_new_ts only — there is no
            action input. The action is self-derived:
              s1_action <= eff_hit ? ACTION_TOUCH : ACTION_INSTALL;
            and every access_en=1 cycle commits (there is no NONE; the compressor
            cannot issue "NONE during RAW beats 1/2" because it never presents an
            access then). The doc's own "CAM Design" section two paragraphs earlier
            correctly says the production CAM is monbus_cam_pipe.
  Impact:   Reader gets the wrong CAM interface contract and a wrong mental model
            of encoder/decoder state synchronization (no-op lookups don't exist;
            every presented record TOUCHes or INSTALLs).
```

### 3. `monbus_group_core.md`: AR-acceptance rule contradicts the RTL (and the page's own port table)

```
[CONFIRMED] "AR is accepted only at slice 0 with at least one record buffered" is not what the hardware does
  File:     docs/markdown/RTLAmba/monitor/monbus_group_core.md
  Says:     "AR is accepted only at slice 0 with at least one record buffered;
            rvalid drops mid-burst if the FIFO underruns..."
  Actually: monbus_group_core.sv:
              assign fub_s_arready = !r_rd_in_burst;
            arready depends only on burst idleness — it does not check the slice
            index or FIFO occupancy. (The page's own port table gets it right:
            "fub_s_arready | AR ready (accepts only when idle)".) Note the RTL
            block comment above the drain contains the same incorrect sentence
            as the doc; the code disagrees with both. rvalid/rlast behavior as
            documented (rvalid = r_rd_in_burst && !err_fifo_empty; rlast on
            beats_remaining==1) is accurate.
  Impact:   A reader modeling the slave-read port would wrongly believe an AR can
            be stalled until data is buffered, and that misaligned bursts can't be
            accepted mid-record. In reality ARs are accepted whenever idle and
            rvalid stalls until a record arrives; a misaligned previous burst
            leaves the next AR starting mid-record (as the doc's own arlen advice
            acknowledges).
```

### 4. Compressor stat counters documented as saturating; RTL wraps

```
[CONFIRMED] "They saturate (do not wrap) at 0xFFFF_FFFF" — no saturation logic exists
  File:     docs/markdown/RTLAmba/monitor/monbus_compressor.md
  Says:     "Each output stat is a 32-bit registered counter. They saturate (do not
            wrap) at 0xFFFF_FFFF so a long-running capture never silently rolls
            back to 0."
  Actually: All eight counters are plain increments, e.g.
              r_tier1_a <= r_tier1_a + 1;
            No saturation compare anywhere in monbus_compressor.sv. At 2^32 events
            of a class the counter wraps to 0.
  Impact:   Exactly the failure mode the doc promises cannot happen: a long capture
            (2^32 records of one tier is reachable in hours at high event rates)
            silently rolls the stats to zero.
```

### 5. CAM per-entry storage table: phantom 5-bit "position rank", missing 24-bit timestamp, wrong totals

```
[CONFIRMED] per-entry size 119 bits / total 3.8 Kb is wrong; actual is 138 bits / ~4.3 Kb
  File:     docs/markdown/RTLAmba/monitor/monbus_compressor.md (§ "CAM Design")
  Says:     "| valid | 1 |  | key | 49 |  | last_event_data | 64 |
            | position rank | 5 |  | total per entry | 119 |
            Total CAM storage: 32 entries × 119 bits ≈ 3.8 Kb (~480 bytes)."
  Actually: Storage in both monbus_cam.sv and monbus_cam_pipe.sv is
            r_valid[DEPTH], r_key[DEPTH], r_data[DEPTH], r_ts[DEPTH].
            There is no stored position rank — the whole point of the
            position-indexed design (documented correctly elsewhere) is that the
            slot index IS the rank: "No tag pointers... no per-entry counter —
            pure structural" (monbus_cam.md). And the 24-bit r_ts added in the
            per-template revision is missing from the table.
            Recompute: 1 + 49 + 64 + 24 = 138 bits/entry;
            32 × 138 = 4 416 bits ≈ 4.3 Kb = 552 bytes (vs. documented
            119 bits / 3 808 bits / ~480 bytes).
  Impact:   Wrong area/storage estimate (~15% low) and a wrong structural fact
            (a stored rank field that doesn't exist).
```

### 6. Compressor latency documented as 2 cycles; actual is 3

```
[CONFIRMED] "net latency 2 cycles" / "2 cycles in flight" undercounts by one
  File:     docs/markdown/RTLAmba/monitor/monbus_compressor.md (§ "Pipeline and Timing")
  Says:     "The encoder is split into 2 registered stages (1 in, 1 register in the
            middle, 1 out — net latency 2 cycles)."
            Table: "Tier-1 record ... 1 record → 1 slot, 2 cycles in flight"
            and "Tier-0 record ... 2 cycles + 2 RAW beats".
  Actually: Three registered stages separate input acceptance from out_valid:
              T    in_valid && cam_en (record presented)
              T+1  monbus_cam_pipe registers result_* (result_valid=1);
                   result writes into u_res_skid (gaxi_skid_buffer, DEPTH=2)
              T+2  skid rd_valid=1 (registered) → p_valid; enc_commit fires;
                   q_* registers at end of T+2
              T+3  out_valid = q_valid = 1, slot driven
            in→out latency = 3 cycles. The module's own header comment says
            "Pipeline (3 stages)", and the doc itself describes three registered
            elements (CAM result, result skid, q register).
  Impact:   Latency budget off by 1 cycle. Throughput claims (1 record/cycle
            tier-1, 1/3 tier-0) are correct — only the latency figure is wrong.
```

### 7. Decision tree still describes the single-cycle design ("combinational on cycle 0", "same clock edge")

```
[CONFIRMED] Encoder Decision Tree timing description is stale
  File:     docs/markdown/RTLAmba/monitor/monbus_compressor.md (§ "Encoder Decision Tree")
  Says:     "2. CAM lookup (combinational): ..." and
            "The format-selector logic is combinational on cycle 0; the slot
            emission and CAM state update happen on the same clock edge."
  Actually: The CAM result the encoder uses is registered (monbus_cam_pipe result
            register + 2-deep result skid). The format selector is combinational
            but operates on the skid output and its result is REGISTERED into q_*
            ("Stage 2a ... REGISTERED" — the doc's own Pipeline section says this:
            "2a — encode register (q_*) ... REGISTERED"). CAM commit happens inside
            the pipelined CAM one cycle after the access is presented.
  Impact:   Contradicts the page's own Pipeline-and-Timing section; a reader cannot
            reconcile "combinational on cycle 0" with the registered 3-stage
            pipeline described elsewhere in the same document.
```

### 8. `monbus_cam_pipe.md`: priority encoder described backwards ("highest-numbered match / LRU side")

```
[CONFIRMED] "picks the highest-numbered match (LRU side of the array...)" — RTL picks the lowest-numbered (MRU side)
  File:     docs/markdown/RTLAmba/monitor/monbus_cam_pipe.md (Pipeline Diagram stage table)
  Says:     "Combinational priority encode picks the highest-numbered match (LRU
            side of the array, to keep the encoder ordering identical to the
            single-cycle module)."
  Actually: monbus_cam_pipe.sv:
              for (int i = DEPTH-1; i >= 0; i--)
                if (w_match_oh[i]) begin raw_hit = 1'b1; raw_idx = IDX_WIDTH'(i); ...
            Later (lower-i) iterations overwrite, so the LOWEST index wins — the
            MRU side, since slot 0 = MRU. monbus_cam.sv does the same and its
            comment says "priority: lowest-index wins". So the ordering is indeed
            identical between the two modules, but it is lowest/MRU, not
            highest/LRU.
  Impact:   Small functionally (the match vector is at most one-hot by the CAM
            invariant, so priority rarely matters), but a reader comparing the two
            implementations against the prose will be misled about which entry a
            duplicate would resolve to.
```

### 9. "2⁶⁰ cycles ≈ 117 days at 100 MHz" — off by ~3 orders of magnitude

```
[CONFIRMED] timestamp-range figure is wrong
  File:     docs/markdown/RTLAmba/monitor/monbus_compressor.md (§ "2. Delta-encoded timestamp")
  Says:     "Absolute timestamps need 60 bits to cover practical recording windows
            (2⁶⁰ cycles ≈ 117 days at 100 MHz)."
  Actually: 2^60 / (1e8 cycles/s × 86 400 s/day) = 1.153e18 / 8.64e12
            ≈ 133 400 days ≈ 365 years. (117 days would correspond to ~2^50
            cycles.)
  Impact:   Low practical (either way "long enough"), but a stated physical number
            that is wrong by 1000×.
```

### 10. Geometry-pipeline settle mechanism misdescribed in both group documents

```
[CONFIRMED] "settle counter holds the plan invalid after r_wr_addr moves" — the counter does not reset on in-IDLE address moves
  File:     docs/markdown/RTLAmba/monitor/monbus_group_core.md and monbus_group.md
  Says:     group_core: "(the plan trails the stable r_wr_addr, which only moves in WR_W)"
            group.md:   "A geom_valid settle counter holds the plan invalid for the
                        first few cycles after r_wr_addr moves so the pipeline can
                        reflect the settled address before the FSM commits."
  Actually: monbus_group_core.sv:
              if (r_wr_state != WR_IDLE) r_geom_settle <= 2'd0;
              else if (r_geom_settle != 2'd3) r_geom_settle <= r_geom_settle + 2'd1;
            The counter resets only when the FSM LEAVES WR_IDLE. But r_wr_addr also
            moves inside WR_IDLE — at commit (r_wr_addr <= r_plan_addr), in the
            rewind-snap branch (r_wr_addr <= r_cfg_base_addr), and in the 4KB
            step-over branch — and none of these reset the settle counter. So after
            a snap, geom_valid stays asserted against a stale plan for up to 3
            cycles. (The inline RTL comment "settle counter resets on r_wr_addr
            change" is likewise wrong — see POSSIBLE RTL BUGS.) The outcome is
            still safe, because a commit always consumes r_plan_addr and
            r_plan_geo_units from one consistent pipeline snapshot and r_plan_ok=0
            blocks commits while stale — but the documented mechanism
            ("holds the plan invalid", "only moves in WR_W") is not what the code does.
  Impact:   Mechanism description wrong; matters to anyone reasoning about the
            rewind-snap corner or modifying the FSM.
```

### 11. Slot-tag tables say 0x4 is reserved / "decoder must error" — but HALF_BEAT_EN=1 streams contain tag 0x4

```
[CONFIRMED] cross-page inconsistency on tag 0x4
  File:     docs/markdown/RTLAmba/monitor/monbus_compressor.md and monbus_group.md
  Says:     compressor: "Tags 0x4-0xF — Reserved (decoder must error on these)"
            group:      "4'h4..4'hF = reserved"
  Actually: monbus_halfbeat_packer.sv: localparam TAG_HALF_PAIR = 4'h4, and the
            packer emits {TAG_HALF_PAIR, slotA, slotB} beats into the write stream
            whenever HALF_BEAT_EN=1 (documented correctly in
            monbus_halfbeat_packer.md). A decoder for a half-beat stream must
            ACCEPT 0x4.
  Impact:   A decoder built from the compressor/group tag tables would raise an
            error on a legal half-beat capture stream. The compressor table is
            defensible for the compressor's own output (it never emits 0x4), but
            "decoder must error on these" is wrong for the format family.
```

### 12. Gap: the 4KB step-over branch is undocumented

```
[CONFIRMED] undocumented writer behavior when cfg_base_addr itself can't hold a whole record
  File:     docs/markdown/RTLAmba/monitor/monbus_group_core.md / monbus_group.md
  Says:     Both documents describe only the rewind-snap (snap r_wr_addr to
            cfg_base_addr) and note base having room is "the host's
            responsibility".
  Actually: monbus_group_core.sv has a second WR_IDLE branch
            (do_flush && geom_valid && !r_plan_ok && r_wr_addr == r_cfg_base_addr)
            that steps r_wr_addr to the next 4KB boundary:
              r_wr_addr <= {r_cfg_base_addr[ADDR_WIDTH-1:12] + 1'b1, 12'd0};
            with a long comment explaining the wedge it fixes. Neither doc
            mentions this hop or the resulting base↔boundary behavior on
            misconfiguration.
  Impact:   Minor (corner case), but anyone diagnosing a capture with a
            base-near-4KB window will see addresses the docs say can't occur.
```

### 13. `monbus_cam.md` TOUCH row misdescribes which slots change

```
[CONFIRMED] Per-Slot Update Mechanics table, TOUCH row
  File:     docs/markdown/RTLAmba/monitor/monbus_cam.md
  Says:     "TOUCH matching slot P | Slots 0..P-1 shift down by 1, slot 0 becomes
            the (matched key, new_data), slot P and below are unchanged from
            their previous positions but written one slot earlier."
  Actually: monbus_cam.sv (shift_to = access_idx = P for TOUCH): slot 0 gets the
            new entry; slots 1..P get old slots 0..P-1; slots ABOVE P are
            unchanged. So slot P is written (with old slot P-1's content) — it is
            not "unchanged", and "slots ... written one slot earlier" is
            backwards (entries move one slot later/toward LRU). The RTL's own
            header comment has the correct version:
              slot 1..P:    new entry = old entry [slot-1]
              slot P+1..N:  unchanged
  Impact:   Minor; garbled mechanism description, off by one slot.
```

### 14. `monbus_cam.md` claims a per-slot generate loop; the RTL is a single always_ff with for-loops

```
[CONFIRMED] structural misdescription (minor)
  File:     docs/markdown/RTLAmba/monitor/monbus_cam.md
  Says:     "A per-slot generate loop generates DEPTH independent always_ff
            updates, each gated by do_shift && (CNT_WIDTH'(i) <= shift_to)."
            (also: "parallel per-slot updates in a generate loop" in the Storage
            Model section)
  Actually: monbus_cam.sv uses ONE ALWAYS_FF_RST block containing for-loops; there
            is no generate construct in the module. (Functionally equivalent after
            unrolling, and the sibling monitor_trans_cam.sv really does use a
            per-slot generate — possibly the source of the confusion.)
  Impact:   Minor; a reader opening the file won't find the described structure.
```

### 15. `monbus_group.md` sub-module table misplaces the input skid

```
[CONFIRMED] "gaxi_skid_buffer (inside compressor) — Input skid..." is mislabeled
  File:     docs/markdown/RTLAmba/monitor/monbus_group.md (Sub-modules table)
  Says:     "| gaxi_skid_buffer (inside compressor) | Input skid on the
            (source_ts, packet) feed; breaks the aggregator → CAM long route |"
  Actually: The input skid (u_comp_in_skid) is instantiated in
            monbus_group_core.sv, feeding the compressor's in_* port. The skid
            inside monbus_compressor.sv is u_res_skid, the CAM RESULT skid — a
            different buffer on a different path.
  Impact:   Minor; misattributes a timing-fix location (relevant to anyone
            floorplanning or editing the hierarchy).
```

### 16. `monbus_cam_pipe.md` interface listing omits two parameters used by its own ports

```
[CONFIRMED] code excerpt incomplete (would not compile as a declaration)
  File:     docs/markdown/RTLAmba/monitor/monbus_cam_pipe.md (Top-level Interface)
  Says:     parameter list shows only KEY_WIDTH/DATA_WIDTH/TS_WIDTH/DEPTH, but the
            port list uses IDX_WIDTH (result_idx) and CNT_WIDTH (cam_count).
  Actually: monbus_cam_pipe.sv declares six parameters, including
            IDX_WIDTH = (DEPTH > 1) ? $clog2(DEPTH) : 1 and
            CNT_WIDTH = $clog2(DEPTH + 1) — which the sibling monbus_cam.md page
            does include.
  Impact:   Minor; instantiators with defaults are unaffected, but the excerpt is
            not a compilable module header as printed.
```

### 17. `monbus_group.md` puts the mod-3 rounding in pipeline stage 2; RTL does it in stage 3

```
[CONFIRMED] minor mechanism placement error (self-contradictory within the same passage)
  File:     docs/markdown/RTLAmba/monitor/monbus_group.md (burst-geometry section)
  Says:     "stage 2 (planned): min-cap tree + whole-record /3 rounding via
            u_mod3_geo ... stage 3 (rounded + addr): r_plan_geo_units ..."
  Actually: Stage 2 registers only s2_beats_planned = min(limit-cap, 4KB-cap).
            u_mod3_geo is fed by s2_beats_planned and the rounding
            (units = s2_beats_planned - w_geo_rem3) happens in the stage-3 block
            that registers r_plan_geo_units/r_plan_addr. The doc's own stage-3
            label "(rounded + addr)" contradicts its stage-2 text.
  Impact:   Minor; one-stage offset in the description of where the rounding lives.
```

### 18. Stat-counter table boundary conditions off by one

```
[CONFIRMED] "> 2²³" / "> 2⁴⁰" vs RTL "≥"
  File:     docs/markdown/RTLAmba/monitor/monbus_compressor.md (Statistics Counters table)
  Says:     "stat_delta_ts_ovf | Tier-0 escape caused by delta_ts > 2²³" and
            "stat_event_data_ovf | ... event_data > 2⁴⁰ (delta_ts fit)"
  Actually: RTL: p_delta_ts >= (60'(1) << DELTA_TS_B_BITS)   // ≥ 2^23
                 p_event_data >= (64'(1) << EVENT_DATA_A_BITS) // ≥ 2^40
            At exactly 2^23 (resp. 2^40) the value doesn't fit the field, escapes
            to RAW, and is counted — the doc's strict-> excludes that boundary.
  Impact:   Trivial; off-by-one at the exact boundary.
```

---

## POSSIBLE RTL BUGS

**1. `r_geom_settle` is not reset by in-`WR_IDLE` `r_wr_addr` changes, despite the inline comments claiming it is (SUSPECTED, appears benign).** The rewind-snap branch comment says "Next cycle, geom_valid drops (settle counter resets on r_wr_addr change)" — the code only resets the counter when `r_wr_state != WR_IDLE`. Tracing a snap cycle-by-cycle: after `r_wr_addr <= cfg_base_addr`, `geom_valid` stays high and `r_plan_ok` stays stale-0 for ~3 cycles, so the `== cfg_base_addr` step-over branch fires spuriously (jumping `r_wr_addr` to the next 4KB boundary), then the `!= cfg_base_addr` branch snaps it back — `r_wr_addr` ping-pongs for ~3 cycles until the pipeline re-derives the plan from `cfg_base_addr` and a normal commit occurs. I could not construct a *bad burst*: every commit uses `r_plan_addr`/`r_plan_geo_units` from a single self-consistent snapshot, and `r_plan_ok=0` blocks commits while stale. Net effect looks like wasted cycles plus spurious address toggling, not corruption — but the mechanism does not match its own comments, and a simulation check of the Phase-5 rewind-snap scenario would be worthwhile.

**2. Stat counters wrap; documentation promises saturation.** Listed as finding 4 (doc error); noted here because if the documented saturate-at-`0xFFFF_FFFF` behavior is the intent, the RTL is missing the feature.

**3. `monbus_compressor` drives `in_ready = cam_en = in_valid && !clear && (r_credit < SKID_DEPTH)`** — ready depends combinationally on valid (AXI handshake-convention violation). Safe with the current upstream (the group core's skid asserts `rd_valid` independently of `rd_ready`), but a producer that waits for ready before asserting valid would deadlock. Convention note rather than a bug in context.

---

## Overall accuracy

The seven pages split cleanly by quality. `monbus_cam.md`, `monbus_cam_pipe.md`, `monbus_halfbeat_packer.md`, and `monitor_trans_cam.md` are faithful to their RTL on interfaces, parameters, encodings, and behavior — their defects are small (a backwards priority-encoder description, a garbled TOUCH-mechanics row, a generate-loop that isn't, an incomplete parameter list). The two group pages are mostly accurate and unusually candid about their timing-driven structure; their real errors are the AR-acceptance rule and the settle-counter mechanism, both cases where the prose mirrors an inline RTL comment that the code has since outgrown. `monbus_compressor.md` is the weak page: it is a palimpsest of the pre-pipeline, pre-per-template revision — the global `r_last_ts` scheme, the three-action CAM port, the "combinational on cycle 0" decision tree, the 2-cycle latency, and the 119-bit CAM entry all describe hardware that no longer exists, and several of these directly contradict later sections of the same page that describe the current design correctly. The dataset arithmetic (682 records / 770 slots / 2.66× / 93.5 %, per-tier splits) is internally consistent and recomputes correctly. Highest-value fixes: rewrite the compressor page's §2, decision tree, CAM-design, and pipeline-timing sections against the current RTL, and correct the stats-saturation claim (or add saturation to the RTL).