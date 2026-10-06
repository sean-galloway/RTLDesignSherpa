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

# Snoop Port: AC/CD/CR Adapter

## Adapter purpose

`amber_snoop_resp` is the ACE-shaped snoop responder (amber D4). It decouples the cache core from ACE signaling: the fabric side speaks real ACE AC/CR/CD; the core side is a bus-agnostic `{address, type, response, data}` transaction.

## Real snoop-slave port (`axi4ace_snoop_slave`)

The module's external (manager → cache) side uses `m_axi_*`; the internal (cache FSM) side uses `fub_*`:

| Signal | Direction | Width | Notes |
|---|---|---|---|
| `m_axi_acaddr` | in | `ADDR_WIDTH` | snoop address |
| `m_axi_acsnoop[3:0]` | in | 4 | snoop transaction type |
| `m_axi_acprot[2:0]` | in | 3 | snoop protection |
| `m_axi_acvalid` | in | 1 | AC valid |
| `m_axi_acready` | out | 1 | AC ready |
| `m_axi_crresp[4:0]` | out | 5 | snoop response |
| `m_axi_crvalid` | out | 1 | CR valid |
| `m_axi_crready` | in | 1 | CR ready |
| `m_axi_cddata` | out | `DATA_WIDTH` | snoop data |
| `m_axi_cdlast` | out | 1 | CD last beat |
| `m_axi_cdvalid` | out | 1 | CD valid |
| `m_axi_cdready` | in | 1 | CD ready |
| `fub_acaddr` | out | `ADDR_WIDTH` | internal snoop address |
| `fub_acsnoop[3:0]` | out | 4 | internal snoop type |
| `fub_acprot[2:0]` | out | 3 | internal snoop protection |
| `fub_acvalid` | out | 1 | internal AC valid |
| `fub_acready` | in | 1 | internal AC ready |
| `fub_crresp[4:0]` | in | 5 | internal response |
| `fub_crvalid` | in | 1 | internal CR valid |
| `fub_crready` | out | 1 | internal CR ready |
| `fub_cddata` | in | `DATA_WIDTH` | internal snoop data |
| `fub_cdlast` | in | 1 | internal CD last |
| `fub_cdvalid` | in | 1 | internal CD valid |
| `fub_cdready` | out | 1 | internal CD ready |
| `busy` | out | 1 | activity status for clock gating |

: Table 4.5: `axi4ace_snoop_slave` pin contract

## Ordering and the family convention

Per the in-repo ACE definition, CR and CD must not be asserted before the AC handshake, and responses are returned in the order of the AC addresses. amber strengthens this: CD beats complete before CR is asserted for the same transaction, giving onyx a single closed response at a time. Multiple outstanding snoops are buffered by the skid FIFOs inside the adapter; the cache core processes them one at a time because `amber_control` is a single FSM.

## Bus-agnostic core boundary

The `fub_*` side is the only boundary the cache core sees. If `onyx` is later replaced by a real ACE interconnect, only `amber_snoop_resp` (and the top-level wiring) changes; `amber_core` does not. That was the reason D4 chose an ACE-shaped transport with a thin adapter.
