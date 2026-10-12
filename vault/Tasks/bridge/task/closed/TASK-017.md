# TASK-017: bridge HAS/MAS v2.0 — protocol-set truth + ACE section + version alignment

**Status:** CLOSED 2026-10-12 (commit in the fabric-gen-ip docs batch). Owner
review found the bridge HAS/MAS summary bullets still read "AXI4, AXI4-Lite,
APB" even though the RTL has supported eight protocols since v1.3–1.6 of the
books (bridge TASK-004/005/006/007/008).
**Priority:** P3
**Filed from:** owner fact-check ("the bridge HAS is wrong I think; it
actually does AMBA 3, 4, 5 and WB4") — confirmed against
`bin/bridge_pkg/config_validator.py` (`valid_protocols = {axi3, axi4, axi5,
apb, apb5, axil, axil5, wb4}`) before touching the docs.

## What changed

- All stale summary bullets now state the full per-port eight-protocol set,
  slave or master side: HAS front matter + purpose, MAS index overview +
  key features.
- New explicit section in HAS ch03: "ACE and Coherency — Explicitly Out of
  Scope" (no AC/CR/CD channels in the RTL; coherence belongs to cache-ip).
- Version strings aligned: HAS/MAS index + front matter now 2.0 / 2026-10-12
  (were 1.2 / 1.7 / PDF 1.9 — three different truths); 2.0 rows added to both
  revision histories.
- Stale rendered versions (v1.0–v1.9 PDF+DOCX, 40 files) deleted; books
  regenerated at v2.0 and delivered to the owner's Kindle.

## Note

Detailed protocol chapters (ch03 03_protocol_support, ch04 AXI5/APB5/WB4,
ch06 AXI3 integration) were already accurate — the staleness was confined to
overview/summary prose.
