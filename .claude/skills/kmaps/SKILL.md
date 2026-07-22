---
name: kmaps
description: Signal-contracts + K-map workbooks (xlsx) for a component - contract sheets per interface and computed Karnaugh maps for key combinational decisions. Use when documenting or reviewing decision logic in engines/schedulers/arbiters.
---

# Signal contracts + K-maps

Methodology: bin/SIGNAL_CONTRACTS_KMAPS.md (canonical).
Reference implementations:
  projects/components/memory-controllers/pumice-ddr2-lpddr2/docs/gen_signal_contracts_kmaps.py
  projects/components/dmas/stream/docs/gen_signal_contracts_kmaps.py

The three rules: maps are COMPUTED from a Python mirror of the verbatim RTL
expression (file:line cited), a citation registry greps every quote on every
run (nonzero exit on drift), and the xlsx is a build artifact - never
hand-edit. Mirroring the expressions IS a design review; report anything
suspicious found while mirroring.
