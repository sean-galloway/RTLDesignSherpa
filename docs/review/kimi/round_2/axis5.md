# Review: axis5 (RTL AMBA AXI5-Stream)

I checked every parameter default, port list, port width, packing order, parity claim, busy-signal claim, and the wake-up/gating latency arithmetic in all five pages against the four modules and the three dependencies in `RTL.sv`. Most of the book recomputes cleanly. Two significant defects and a few minor ones follow.

---

## Findings

```
[CONFIRMED] _cg pages claim TREADY stays low while the clock is gated and that
"nothing is lost"; the RTL holds TREADY high, so inbound beats are silently
dropped during the wake-up window
  File:     docs/markdown/RTLAmba/axis5/axis5_master_cg.md
  Says:     "Nothing is lost during those cycles: `fub_axis5_tready` is driven by
            the skid buffer on `gated_clk`, so it stays low while the clock is
            stopped and the producer simply holds TVALID until the clock resumes."
            (and in Benefits: "No protocol impact (transparent to
            upstream/downstream)")
  Also in:  docs/markdown/RTLAmba/axis5/axis5_slave_cg.md
  Says:     "Nothing is lost during those cycles: `s_axis_tready` ... stays low
            while the clock is stopped and the upstream master simply holds
            TVALID until the clock resumes."
            and "No transfer can slip past the check while gated:
            `s_axis_tready` is driven on `gated_clk`, so no transfer is accepted
            until the clock has resumed"
  Actually: In gaxi_skid_buffer, wr_ready is a *registered* output on the core
            clock (which the _cg wrappers connect to gated_clk):
                wr_ready <= (32'(r_data_count) <= DEPTH-2) || ...
            Gating only engages when the stream is fully idle, i.e.
            r_data_count==0, so wr_ready's last clocked value is 1
            (0 <= DEPTH-2 for any legal depth). While the clock is stopped the
            register simply holds that 1. The producer/upstream master sits on
            the always-running aclk (the docs themselves say "Input signals:
            Must be on aclk domain"), sees TVALID && TREADY == 1, completes the
            handshake, and advances — but no gated edge occurs to capture the
            data until the two-register wake-up chain restarts gated_clk ~3
            aclk cycles later. Beats presented during that window are dropped,
            and (for the slave) their parity errors are never captured either.
  Impact:   A reader integrates axis5_*_cg believing wake-up is lossless and
            protocol-transparent. In reality the first beats after every
            gate-to-wake transition are silently lost. This is the most
            damaging kind of doc defect: it asserts safety the design does
            not provide. See POSSIBLE RTL BUGS #1.
```

```
[CONFIRMED] Docs claim ENABLE_WAKEUP=0 removes the TWAKEUP ports / yields an
AXI4-Stream-compatible port list; the ports persist in the port list
  File:     docs/markdown/RTLAmba/axis5/README.md
  Says:     "TWAKEUP can be tied to 0 for always-awake operation, or removed
            entirely with `ENABLE_WAKEUP=0`"
  Also in:  all four module pages ("Note on `ENABLE_WAKEUP`")
  Says:     "Set it to 0 for an AXI4-Stream-compatible port list with no
            wake-up sideband and slightly less area."
  Actually: The ports are declared unconditionally in axis5_master.sv /
            axis5_slave.sv (`input logic fub_axis_twakeup`, `output logic
            m_axis_twakeup`, etc.). ENABLE_WAKEUP=0 only changes the generate
            packing: `g_no_twakeup: assign m_axis_twakeup = 1'b0;` and the
            input is left out of the packed word. The port list still contains
            TWAKEUP (and, in the _cg wrappers, the input is still sampled by
            the r_wakeup OR). Same structure for TPARITY: with ENABLE_PARITY=0
            the port remains at width PW_WIDTH=1, output tied '0. The book's
            own examples contradict "removed entirely" — they still connect
            `.fub_axis_tparity('0)` / `.m_axis_tparity()` with parity disabled.
  Impact:   Moderate-low. A reader expecting the sideband ports to disappear
            (e.g. for a strict AXI4-Stream interface match) still has to deal
            with them. Functionally harmless but factually wrong in five files.
```

```
[CONFIRMED] README says TID/TDEST/TUSER can be "set 0 to remove"; the ports
remain, 1 bit wide and tied off
  File:     docs/markdown/RTLAmba/axis5/README.md
  Says:     "| TID | Implemented | Width `AXIS_ID_WIDTH` (default 8, set 0 to
            remove) |" (same wording for TDEST and TUSER)
  Actually: IW_WIDTH = (IW > 0) ? IW : 1 (likewise DESTW_WIDTH, UW_WIDTH), so
            the port never disappears; with width 0 the output generate block
            ties it to '0 (`g_no_tid: assign m_axis_tid = '0;`) and the input
            is ignored. The module pages describe this correctly ("0 to
            disable", "TID tied to 0", "zero-width avoidance"), so the README
            also contradicts the module pages.
  Impact:   Low; cosmetic port-list confusion, same class as the previous
            finding.
```

```
[CONFIRMED] (minor gap) "Conservative: 32-64 cycles" idle-count advice is
unreachable at the default counter width
  File:     docs/markdown/RTLAmba/axis5/axis5_master_cg.md and
            docs/markdown/RTLAmba/axis5/axis5_slave_cg.md
  Says:     "Conservative: 32-64 cycles - Only gates during extended idle"
  Actually: CG_IDLE_COUNT_WIDTH defaults to 4 and i_cg_idle_count is ICW bits
            wide; clock_gate_ctrl's header states max count = 2^ICW-1 = 15.
            Neither axis5 page states the max. A reader who drives a value
            like 32 into the 4-bit port gets silent truncation to 0, which
            makes the counter load 0 and gates the clock almost immediately
            after activity stops — the opposite of "conservative".
  Impact:   Low, but a real configuration trap; one sentence ("values above
            2^CG_IDLE_COUNT_WIDTH-1 require widening the counter") fixes it.
```

```
[SUSPECTED] "+5-10%" area overhead for the _cg variants is an unsourced number
presented as fact
  File:     docs/markdown/RTLAmba/axis5/axis5_master_cg.md and
            axis5_slave_cg.md ("Clock Gating vs. Non-Gated Variant" tables)
  Says:     "Area | Smaller | +5-10% (clock gate logic)"
  Actually: The README's own Performance section states "No synthesis or
            timing run for these modules is published in this repository", so
            no area measurement backs the figure. I cannot disprove it (it is
            plausible), but it is an unmeasured claim stated as data.
  Impact:   Low.
```

---

## POSSIBLE RTL BUGS

**1. Data loss in `axis5_master_cg` / `axis5_slave_cg` on wake from a gated idle (serious).**
As detailed in Finding 1: when `amba_clock_gate_ctrl` gates the clock, the core skid buffer's `wr_ready` is frozen at 1 (empty buffer ⇒ `r_data_count=0 <= DEPTH-2`). An inbound transfer arriving while gated handshakes successfully from the producer's point of view (both on the ungated `aclk`) but is never captured, because the first usable `gated_clk` edge only arrives ~3 `aclk` cycles later (wrapper `r_wakeup` → `amba_clock_gate_ctrl` `r_wakeup` → combinational ICG enable). At full rate the first ~2 beats of every post-gate burst are silently dropped; the slave-side parity check also cannot flag them. The gating condition itself is safe only for the *outbound* side (`m_axis5_tvalid`/`fub_axis5_tvalid` keep the clock running while data is pending). A minimal fix is to mask the input-ready with the gating status on the aclk side, e.g. `fub_axis5_tready = core_tready & ~axis_clock_gating;` — producers then hold TVALID (as AXI requires) until the clock resumes, and no beat is lost. The same pattern presumably affects the other `_cg` wrappers in the library that share this structure; worth auditing the axis4/axi4/axil4/apb books for it.

**2. Stale comment in `axis5_master_cg.sv` (trivial).** The block comment above `r_wakeup` lists five keep-alive conditions including "4. Downstream is ready (accepting data)", but the code ORs only four terms (`fub_axis5_tvalid || core_busy || m_axis5_tvalid || fub_axis5_twakeup`) and does not include `m_axis5_tready`. The documentation's expression matches the code, so this is purely an RTL comment inconsistency. (`axis5_slave_cg.sv`'s comment matches its code.)

---

## Verified-correct items (spot list)

- All parameter defaults (SKID_DEPTH=4, DATA=32, ID=8, DEST=4, USER=1, ENABLE_WAKEUP=1, ENABLE_PARITY=0, CG_IDLE_COUNT_WIDTH=4) match the RTL in all four modules.
- All four port lists, including the `fub_axis_*` vs `fub_axis5_*`/`m_axis5_*` prefix difference the README warns about, match exactly; the README's port-prefix warning is accurate for both _cg variants.
- The conditional packing orders (`{tdata, tstrb, tlast, tid, tdest, tuser[, twakeup][, tparity]}`) match the generate blocks verbatim.
- Parity claims: even parity via `^tdata[i*8 +: 8]`, sticky `parity_error` cleared only by reset, master checks on its output, slave on its input, sampled on accepted transfers — all confirmed against the RTL. The 12.5%-overhead / 64-bits-for-512 arithmetic is correct.
- `busy = (int_t_count > 0) || <input tvalid>` matches the documented description on all four pages.
- The wake-up/gating latency arithmetic is right: two register stages + combinational ICG enable ⇒ first usable gated edge 3 `aclk` cycles after activity, and gating `i_cg_idle_count`+3 cycles after last activity — I traced both against the RTL and they agree with `clock_gate_ctrl`'s own header ("cfg_cg_idle_count + 1 clocks from last wakeup").
- Reset-behavior claims (both `r_wakeup` registers reset to 1, idle counter loads `i_cg_idle_count` on reset, `aresetn` reaches controller and core ungated) are all confirmed.
- "1 transfer/clock sustained" and "1–2 cycle skid latency" recompute correctly from `gaxi_skid_buffer`; the performance table is appropriately hedged as uncharacterized.
- TKEEP/TPOISON/chunking absent, TPARITY proprietary — all true of the RTL.

## Overall assessment

This is one of the more accurate books: parameters, ports, widths, packing, parity semantics, and the (non-trivial) clock-gating latency arithmetic all verify against the RTL, and the deviations from the ARM signal set are disclosed honestly. Two defects need fixing before release: (1) the repeated claim that the `_cg` wrappers lose nothing during wake-up because TREADY "stays low" — the RTL does the opposite, and the claim currently disguises a genuine data-loss bug in both `_cg` modules; (2) the "ports are removed / AXI4-Stream-compatible port list" wording for `ENABLE_WAKEUP=0` (and "set 0 to remove" for TID/TDEST/TUSER in the README), which is false in five files — the ports persist, tied off. Minor items: the unsourced "+5–10%" area figure and the 32–64-cycle idle-count advice that silently exceeds the default 4-bit counter range.