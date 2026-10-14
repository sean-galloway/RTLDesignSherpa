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

# Axon — Cell Result Router (spec sketch)

**Codename:** axon · **Owner block:** cell · **Status:** pre-HAS sketch

Axon is the block that gets a CGRA's results off the array and onto the
network: a SERV agent (or a small group of them) paired with the delta AXIS
fabric, attached at the **tile** boundary — the level where the cell array
faces RAPIDS (owner hierarchy 2026-10-13: four cells make a tetrad, four tetrads
make a tile; the tile connects to RAPIDS). It is the tile-level twin
of [hive-serv](../../hive-serv/)'s monitors — the same idiom (tiny bit-serial
agent + stream fabric), applied to the data path instead of the control path.

## Role

1. **Collect** CGRA result streams as the array produces them (per-PE or
   per-row, TBD with the cgra design).
2. **Packetize** results as AXIS PKT_DATA with the hardware-enforced TID
   rule (the fabric overrides source ID — see the HIVE HAS §4.2; axon sits on
   the same rule).
3. **Stream out** over delta toward RAPIDS S2MM channels (the channel-aware
   programming model is the HIVE HAS §5.2 contract; axon is a producer).
4. **Local housekeeping** via the same control-network frame format as HIVE
   (MAS §2.4) — thresholds, counters, status: one protocol everywhere.

## Interfaces (preliminary)

| Path | Protocol | Notes |
|---|---|---|
| cgra results → axon | TBD with cgra | internal to cell |
| axon → delta | AXIS 128/256b, PKT_DATA | AXIS-only rule; tdest = RAPIDS/tile per delta routing |
| HIVE-C → axon | control-network frames / PKT_CONFIG | same frame format as HIVE monitors |
| config/status | AXI4-Lite | registers only, per the house rule |

## What is deliberately NOT decided here

PE count, fabric geometry, context/memory model, and the cgra↔axon data
format all belong to the cgra's own HAS/MAS. This sketch pins only the
boundary: axon consumes whatever the cgra produces and speaks the standing
fabric contracts on the outside.

**Next step:** cell PRD, then axon HAS (reusing the hive_has chapter
skeleton), then cgra HAS/MAS when the array's design firms up.
