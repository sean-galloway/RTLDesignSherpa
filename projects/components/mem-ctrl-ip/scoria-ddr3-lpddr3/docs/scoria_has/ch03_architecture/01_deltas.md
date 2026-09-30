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

# What Is Inherited, and the Blocks That Change

## The inheritance, stated once

Nineteen of pumice's twenty-four FUBs carry over with no functional change, as
do the top, core, AXI4 macro and the DFI datapath. Chapter 2.3 lists them. This
chapter covers only what changes, and the list is short by design.

**The inheritance is an argument, not a convenience.** Those blocks have been
through board bring-up, a read-path rebuild that took reads from 291.7 to
571.3 MB/s, and a formal campaign across nine modules. Re-deriving them would
discard that evidence and reintroduce the bugs it caught.

**Important — inherit `global_timers` in its FIXED form.** pumice's version
published readiness one cycle late: the registered status flop sampled the
current counter state rather than the next, so the flags alone permitted tCCD
and tRTW violations. The fix computes one next-state function and feeds both the
counter and its status flop from it. A fresh implementation written from a
behavioural description of the same block would reintroduce the defect, because
the description does not mention the flop. Copy the module.

## The changes, in one table

| Block | Marking | Cause | Where |
|---|---|---|---|
| `init_sequencer` | MODIFIED | `RESET#` is a pin; MR order is MR2-MR3-MR1-MR0; ZQCL closes init | 3.2 |
| `mode_register` | MODIFIED | MR0-MR3 replaces MR0-MR2 plus EMRS3 | 3.2 |
| `dfi_cmd_formatter` | MODIFIED | new encodings: `ZQCL`, `ZQCS`, `PREA` | 3.2 |
| `scoria_zq_ctrl` | **NEW** | periodic `ZQCS` is maintenance traffic | 3.2 |
| `scoria_wrlvl_ifc` | **NEW** | DDR3 adds write leveling | 3.3 |
| `refresh_ctrl` | INHERITED | pumice already implements `REFpb`; LPDDR3 uses the same device-fixed mechanism. Only a mode-select CSR is added | 3.4 |
| `powerdown_ctrl` | MODIFIED | self-refresh against the split DFI low-power requests | below |
| `scoria_mem_cmd_scheduler` | MODIFIED | must admit ZQ demand alongside refresh | 3.2 |
| `scoria_csr` | MODIFIED | new timing registers and leveling telemetry | Ch 5 |

: Table 3.1: Every change, with its cause

## Power-down: the one change small enough to cover here

DDR3 and LPDDR3 both offer precharge-power-down, active-power-down and
self-refresh (`SRE` / `SRX`). pumice's `powerdown_ctrl` already implements
idle-timer-driven entry and exit; what changes is the interface beneath it.

DFI v2.1.1 had a single `dfi_lp_req`. DFI v3.1 **splits it** into
`dfi_lp_ctrl_req` and `dfi_lp_data_req`, letting the controller request low-power
state for the command path and the data path independently. `powerdown_ctrl`
therefore drives two requests where it drove one, and the distinction is real:
a controller can idle the data path while keeping the command path alive, which
is what active-power-down wants.

**Note:** the reverse asymmetry — bringing one back up without the other — is
where a naive implementation will deadlock. The requirement in this edition is
that entry and exit are symmetric per path and that the CSR exposes which paths
are currently down. The exact handshake ordering is an open question in
Chapter 6, because it depends on PHY behaviour this specification cannot fix.
