# Review: `axis4` book (6 docs, 4 modules + 3 dependencies)

## Method

I checked every port list, parameter table, and code-example port name in the six pages against the four module declarations in `RTL.sv`; re-derived the wakeup terms and gating/ungating latency arithmetic from `amba_clock_gate_ctrl` + `clock_gate_ctrl`; re-derived the skid-buffer latency and sustained-throughput behaviour from the `gaxi_skid_buffer` always_ff blocks; and recomputed all bandwidth numbers.

What verified clean (so you don't have to re-check): both module declarations reproduced in the docs match the RTL exactly (parameters, derived parameters, ports); the `busy` equations (`(int_t_count > 0) || fub_axis_tvalid` / `s_axis_tvalid`) match; the wakeup terms quoted in the clock-gating guide (`user_valid = fub_axis_tvalid || m_axis_tready || busy`, `axi_valid = m_axis_tvalid`, and the slave substitution) match the RTL verbatim, as do the quoted `w_gate_enable` expression and the `tready = cg_gating ? 1'b0 : int_tready` hold-off; the 1-stage/2-cycle ungating and `cfg_cg_idle_count + 1 / + 2` gating-latency formulas are arithmetically correct against the counter logic (I traced cfg=3 cycle by cycle: gating in cycle A+5 = cfg+2 after last activity); `SKID_DEPTH` is indeed passed verbatim to `gaxi_skid_buffer.DEPTH` with supported values {2,4,6,8}; the throughput table (1.6/3.2/6.4/25.6 GB/s) is arithmetically correct, and 1 beat/cycle sustained is confirmed for DEPTH=2 steady state; TKEEP/TWAKEUP are genuinely absent; the `_cg` wrappers genuinely have no `busy`, `cg_clk_count`, `cg_test_enable`, or `ENABLE_CLOCK_GATING`.

## Findings

```
[CONFIRMED] Wrong source directory for gaxi_skid_buffer
  File:     docs/markdown/RTLAmba/axis4/README.md
  Says:     "Shared Infrastructure: `rtl/amba/shared/` (gaxi_skid_buffer)"
  Actually: The RTL banner reads "SOURCE FILE: rtl/amba/gaxi/gaxi_skid_buffer.sv".
            Only amba_clock_gate_ctrl lives under rtl/amba/shared/; the named
            module is in rtl/amba/gaxi/.
  Impact:   A reader looking for the skid-buffer source is sent to the wrong
            directory. Low impact.
```

```
[CONFIRMED] Inline "Gate after N idle cycles" comments contradict the guide's own formula
  File:     docs/markdown/RTLAmba/axis4/axis_clock_gating_guide.md
  Says:     ".cfg_cg_idle_count(4'd1)   // Gate after 1 idle cycle" (and 4'd5/4'd10
            variants, plus "4'd3 // Gate after 3 idle cycles" in the usage example)
  Actually: The same page states gating engages "cfg_cg_idle_count + 2 cycles
            after the last bus activity". With cfg=1 that is 3 cycles after last
            activity, not 1. I verified the formula itself against clock_gate_ctrl
            (counter reloads while wakeup=1, decrements to 0, gates at count==0)
            and it is correct; the shorthand comments undercount by 2.
  Impact:   Minor. The precise formula is documented two sections earlier, but a
            reader skimming the config examples gets a gating point 2 cycles early.
```

```
[CONFIRMED] "25-70%" power-savings range on the _cg pages vs 0-70% in the guide's own table
  File:     docs/markdown/RTLAmba/axis4/axis_master_cg.md (same text in axis_slave_cg.md)
  Says:     "Power Savings: Estimated 25-70% depending on stream duty cycle"
  Actually: The guide's table in axis_clock_gating_guide.md lists "Video (1080p
            with blanking) ... 10-15%" and "Continuous stream ... 0%", i.e. the
            realistic span is 0-70%. Both figures are labelled planning estimates,
            so this is a soft contradiction between pages of the same book.
  Impact:   Minor. A reader of only the module page gets a too-optimistic lower
            bound for high-duty-cycle streams.
```

```
[SUSPECTED] gaxi_fifo_async instantiation in the CDC example cannot be verified
  File:     docs/markdown/RTLAmba/axis4/axis_master.md
  Says:     "gaxi_fifo_async #(.DEPTH(64), .DATA_WIDTH(32 + 4 + 1 + 4 + 4 + 1))
            u_cdc_fifo (.wr_clk(...), .wr_axis(cdc_src_axis), .rd_axis(dst_axis), ...)"
            and "gaxi_fifo_async.DEPTH is also a literal entry count (default 16)"
  Actually: gaxi_fifo_async is not among the modules/dependencies in RTL.sv, so I
            could not check its port list or DEPTH default. The DATA_WIDTH=46
            arithmetic itself is correct (TSize = 32+4+1+4+4+1), but the
            interface-style ports wr_axis/rd_axis are inconsistent with the
            discrete wr_valid/wr_ready/wr_data style of every other gaxi module
            shown here, so this may not compile as written.
  Impact:   Low-to-moderate if the ports are wrong: the example is presented as a
            real integration pattern (unlike the explicitly-flagged `.*` shorthand
            elsewhere on the same page).
```

## POSSIBLE RTL BUGS

None found. I specifically traced the `_cg` wrappers for gating deadlock (gating requires `m_axis_tvalid`/`fub_axis_tvalid` = 0, count = 0, and the relevant TREADY = 0; any wakeup term re-opens the clock within 2 cycles while the incoming TREADY hold-off prevents protocol violation) and checked the `gaxi_skid_buffer` hold/load/shift table including the simultaneous read+write case at count = 1 and count > 1. All correct.

## Overall accuracy

This book is in very good shape — visibly better than the defect classes the brief warns about. The earlier review feedback has clearly been incorporated: `SKID_DEPTH` is documented as a literal entry count with the legal set {2,4,6,8}, the throughput/area/frequency tables carry explicit "design targets, not measured" disclaimers, the non-compiling `.m_axis_*(...)` shorthand is self-flagged, the fictitious `axis_arbiter`/`axis_interconnect` are disclaimed, the TKEEP-over-TSTRB convention is honestly described, and the clock-gating latency analysis is precise and correct down to the cycle. The remaining defects are one wrong file path, one set of lazy inline comments that contradict the page's own (correct) formula, one soft cross-page inconsistency in a disclaimed power range, and one unverifiable FIFO instantiation. Nothing here would cause a reader to wire up a module incorrectly or mis-size a buffer.