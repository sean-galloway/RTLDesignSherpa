# Review: `axil4` book (10 docs / 8 modules + 3 dependencies)

## Method

I checked every parameter table, port table, derived-size formula, `busy` equation, clock-gating wakeup term, gating/ungating latency figure, and code example against `RTL.sv`, and recomputed the throughput/latency numbers from the `gaxi_skid_buffer` implementation (registered `wr_ready`/`rd_valid`, shift-register storage ⇒ exactly 1 cycle per buffer traversal, verified against the slot-update and count logic). Monitor-wrapper claims (`axil4_*_mon`, `cfg_axi_pkt_mask`, MonBus) are not verifiable from this bundle — those modules live in the `monitor` book — so I did not score them.

The vast majority of the book checks out. I found two genuine defects.

---

## Findings

```
[CONFIRMED] Write-transaction latency "Slave latency + 3" overstates the module's buffering
            overhead by one cycle and contradicts the doc's own explanation
  File:     docs/markdown/RTLAmba/axil4/README.md
  Says:     "| AW+W → B (single) | Slave latency + 3 | AW and W buffers, then the B buffer |"
            and "The write figure assumes the slave accepts AW and W in the same cycle."
  Also:     docs/markdown/RTLAmba/axil4/axil4_master_wr.md
  Says:     "| Total write latency | Slave latency + 3 | AW + W + Slave + B, best case |"
            and "The `+3` best case assumes the slave asserts AWREADY and WREADY in the
            **same** cycle, so the AW and W buffer traversals overlap."
  Actually: The AW and W skid buffers are independent instances
            (`aw_channel`, `w_channel` in axil4_master_wr.sv, each one gaxi_skid_buffer
            adding exactly 1 cycle: write handshake cycle N → rd_valid/data cycle N+1).
            Under the doc's own same-cycle-accept assumption the two traversals are
            concurrent, so overhead = max(1,1) [AW∥W] + 1 [B] = **2 cycles**, not 3.
            Cross-checks: (a) the doc's own signal-flow trace — frontend handshake cycle 1,
            slave handshake cycle 2, slave B at cycle 6, frontend B handshake cycle 7 — is
            6 cycles total with a 4-cycle slave, i.e. +2; (b) the read path is documented
            as +2 for two serial buffers, and the write path also has only two *serial*
            buffer stages; (c) the sentence "so the AW and W buffer traversals overlap"
            directly contradicts the "+3" it is justifying — if they overlap they sum to 1.
  Impact:   A reader budgeting write latency over-counts by one cycle, and the two pages
            teach an internally inconsistent latency model (+1 per channel vs +3 total).
```

```
[CONFIRMED] AxPROT encoding table swaps the meaning of bits [0] and [2] versus the AXI spec
  File:     docs/markdown/RTLAmba/axil4/axil4_master_rd.md ("PROT Encoding" table)
  Says:     "| 3'b001 | Unprivileged | Secure | Instruction |" and
            "| 3'b100 | Privileged   | Secure | Data |"
  Actually: Per ARM IHI 0022E (the spec this page cites): AxPROT[0] = 0 unprivileged /
            1 privileged; AxPROT[1] = 0 secure / 1 non-secure; AxPROT[2] = 0 data /
            1 instruction. So 3'b001 = Privileged/Secure/Data and 3'b100 =
            Unprivileged/Secure/Instruction — the table has bits [0] and [2] interchanged.
            (Rows where bit2==bit0 — 000, 010, 101, 111 — are coincidentally correct; rows
            001, 011, 100, 110 are wrong.) The RTL is transparent transport
            (`.wr_data({fub_araddr, fub_arprot})`, never inspected), so the module neither
            enforces nor defines the encoding — ground truth here is the AXI spec the doc
            references. Confidence basis: spec encoding, not RTL.
  Impact:   A reader using this table to drive `fub_arprot` signals the opposite of intent
            for privilege vs. instruction — e.g. 3'b100, which the table calls a privileged
            data access, is actually an unprivileged instruction fetch. Any downstream
            slave that does enforce PROT would misbehave.
```

Everything else I checked passed. For the record, verified-correct items include: all parameter names/defaults/widths on all 8 modules; the derived sizes (`ARSize=AW+3`, `RSize=DW+2`, `AWSize=AW+3`, `WSize=DW+(DW/8)`, `BSize=2`) and the packing order shown in the docs; every port name/direction/width in the four base-module pages and the four `_cg` pages (including the correct observation that `busy` is not exposed on `_cg` wrappers); the `busy` Boolean equations quoted in `axil4_master_rd.md` / `axil4_master_wr.md` (they match the RTL term-for-term); the documented wakeup terms for `axil4_master_rd_cg` (`user_valid = fub_arvalid || fub_rready || int_busy`, etc. — exact match); the ready-forcing snippet in the clock-gating guide (exact match to RTL); the read latency "Slave latency + 2"; the gating latency "cfg_cg_idle_count + 2 clocks after last bus activity" and ungating "first gated-clock edge 2 clocks after activity" (I re-derived both from `amba_clock_gate_ctrl`'s `r_wakeup` flop plus the combinational `w_gate_enable` into the ICG: cfg=2 ⇒ gating asserted 4 clocks after last activity, released edge 2 clocks after new activity — matches); `cg_idle = registered ~wakeup`; the `{2,4,6,8}` DEPTH constraint (matches the `gaxi_skid_buffer` header); and the WSTRB byte-lane tables. All code examples reference only ports and parameters that exist. The resource/power tables carry explicit "order-of-magnitude, unmeasured" disclaimers, so they are not reported (and are a known-weak area anyway).

---

## POSSIBLE RTL BUGS

1. **[SUSPECTED] `clock_gate_ctrl` uses an undeclared identifier in its port list.** The port `input logic [N-1:0] cfg_cg_idle_count` uses `N`, but `N` is declared as a `localparam` in the module *body* (`localparam int N = IDLE_CNTR_WIDTH; // Alias for backwards compatibility`), after the ANSI port list. Strictly, body localparams are not visible in the port list; acceptance is tool-dependent. Since `reset_defs.svh` is included before the module, an `N` macro from that header could also silently bind instead (I could not see the header contents). The sibling module `amba_clock_gate_ctrl` does this correctly with `parameter int ICW` in the parameter list. Cannot compile here, so flagged as suspected — but if their CI simulator accepts it, it is still a portability hazard for other tools (Verilator/ASIC flows). This affects every `_cg` module in the book, since they all instantiate `amba_clock_gate_ctrl` → `clock_gate_ctrl`.

2. **[Minor, comment only] `axil4_master_rd_cg.sv` port comment says `cg_idle // All buffers empty indicator`.** It is actually the registered no-activity flag (`idle = ~r_wakeup` in `amba_clock_gate_ctrl`). The documentation describes it correctly ("no activity on the previous cycle"); only the RTL comment is loose. The other three `_cg` wrappers have no such comment.

---

## Overall assessment

This is a well-verified book. The interface documentation (ports, parameters, derived sizes, `busy` equations, clock-gating mechanics) is exact — several of the trickier claims (wakeup equations, 2-clock ungating latency, idle-count gating latency, ready-forcing behavior) are precisely right, and the latency/resource sections mostly carry honest disclaimers. The two confirmed defects worth fixing before release are the **write-latency "+3"** (wrong by one cycle and self-contradictory in both `README.md` and `axil4_master_wr.md`; the correct best case is slave latency + 2) and the **swapped AxPROT table** in `axil4_master_rd.md`, which is the more dangerous of the two because a reader will act on it directly. The monitor-integration content in `README.md` could not be verified from this bundle and should be re-checked when the `monitor` book is reviewed.