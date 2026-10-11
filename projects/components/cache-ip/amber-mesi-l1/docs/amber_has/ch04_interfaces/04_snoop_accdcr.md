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

## House-module pin contract — not restated here

`axi4ace_snoop_slave` is a house module: its full `m_axi_*`/`fub_*` pin
contract lives in `rtl/amba/ace/axi4ace_snoop_slave.sv` and the AMBA
documentation index — this HAS does not duplicate it. The amber-visible
facts are the boundary rule and the ordering guarantee in the next
section; on the internal side, the cache core drives CRRESP combinationally
at the `fub_acvalid/fub_acready` grant and sources CD beats on
`fub_cdvalid/fub_cdready`, one transaction at a time (single control FSM).

## Ordering and the family convention

Per the in-repo ACE definition, CR and CD must not be asserted before the AC handshake, and responses are returned in the order of the AC addresses. The book reinforces that ACE snoops carry no ID and the snoop channels are strictly in-order, so the adapter's CR+CD ordering obligation is absolute (Chinnakonda, §7.1, §14.18). amber strengthens this: CD beats complete before CR is asserted for the same transaction, giving onyx a single closed response at a time. Multiple outstanding snoops are buffered by the skid FIFOs inside the adapter; the cache core processes them one at a time because `amber_control` is a single FSM. The response bound is therefore one snoop at a time through the core; the adapter FIFOs absorb any back-pressure.

## RACK/WACK (resolved 2026-10-11)

Ruling 2026-10-11 (Sean): the family ACE contract omits RACK/WACK. The
D7 port guarantees ordered data-return and snoop paths to the coherency
point, which is the condition Chinnakonda §7.20/§14.39 gives for omitting
them. The house `axi4ace_master_rd/wr` and `axi4ace_snoop_slave` wrappers
still auto-pulse RACK/WACK; that behavior is deprecated for family contract
use, and its removal is tracked as amber RTL follow-up A5. Amber's existing
CD-before-CR, in-order snoop processing already provides the ordering the
signals were meant to protect.

## Bus-agnostic core boundary

The `fub_*` side is the only boundary the cache core sees. If `onyx` is later replaced by a real ACE interconnect, only `amber_snoop_resp` (and the top-level wiring) changes; `amber_core` does not. That was the reason D4 chose an ACE-shaped transport with a thin adapter.
