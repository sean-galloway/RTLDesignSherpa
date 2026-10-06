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

# Snoop AC/CD/CR Timing and Ordering

## External ACE Snoop Port

| Signal | Direction | Purpose |
|--------|-----------|---------|
| `m_axi_acvalid` / `m_axi_acready` | in / out | AC handshake |
| `m_axi_acaddr` | in | snoop line address |
| `m_axi_acsnoop` | in | snoop type |
| `m_axi_cdvalid` / `m_axi_cdready` | out / in | CD handshake |
| `m_axi_cddata` | out | snoop data beat |
| `m_axi_cdlast` | out | last CD beat |
| `m_axi_crvalid` / `m_axi_crready` | out / in | CR handshake |
| `m_axi_crresp` | out | 5-bit response |

## Transaction Sequence

```
Cycle :  0   1   2   3   4   5   6   7
AC_v  :  1   0   0   0   0   0   0   0
AC_r  :  1   0   0   0   0   0   0   0   <- AC handshake
lookup:      L0  L1
CD_v  :  0   0   0   1   1   1   0   0
CD_r  :  0   0   0   1   1   1   0   0
last  :  0   0   0   0   0   1   0   0
CR_v  :  0   0   0   0   0   0   1   0
CR_r  :  0   0   0   0   0   0   1   0   <- CR after CDLAST
```

- Cycle 0: AC handshake. The snoop address and type are captured.
- Cycles 1–2: `amber_control` performs tag lookup on port B. If the line is M/E and the snoop requires data, it reads the data array port B.
- Cycles 3–5: CD beats are driven and accepted.
- Cycle 6: CR is asserted after `CDLAST` has been accepted.
- Cycle 7: CR handshake completes; the adapter returns to idle.

## CR-After-CDLAST Rule

`amber_snoop_resp` holds `m_axi_crvalid` low until the last CD beat has been accepted. This is stronger than the minimum IHI0022 requirement but matches the family convention and the cocotb-framework 1.2.0 compliance checker. It also makes the gather logic simple: the manager sees one closed response at a time.

## Multiple Outstanding Snoops

The `axi4ace_snoop_slave` wrapper buffers up to `SKID_DEPTH_AC` snoops. However, `amber_control` processes them one at a time because it is a single FSM. Therefore the effective outstanding snoop count is 1 from the core's perspective; the adapter FIFO absorbs bursts of AC arrivals.

## AC Ready Backpressure

`m_axi_acready` is the skid-buffer `wr_ready` from `axi4ace_snoop_slave`. It can be low when the AC skid is full. The manager must respect this; amber never drops a snoop address because the adapter buffers it.

---

**Last Updated:** 2026-10-06
