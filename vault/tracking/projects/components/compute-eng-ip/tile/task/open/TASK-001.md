# TASK-001: Study IBM NorthPole for tile architecture ideas

**Priority:** P3
**Status:** open -- 2026-10-19
**Owner:** sean galloway

## Why

Owner, 2026-10-19: look into the IBM NorthPole inference chip for ideas
on the tile. NorthPole is a 2D array of cores with memory on chip beside
the compute and several on-chip networks, which is close to the tile's
shape (cells on delta, MonBus per level). The details below are questions
to answer from the published papers, not facts assumed here.

## What to look at

- Compute and memory per core vs a cell, and how much memory sits near
  the compute.
- The networks: how many, what each carries (activations, partial sums,
  program/control), and how they compare with delta plus the MonBus tree
  (TILE_SPEC 3, 5).
- How the program and weights reach the cores, vs the control cores and
  `desc` packets (TILE_SPEC 11.11, 11.13).
- Flow control and ordering between cores, vs the straps and credits
  (TILE_SPEC 11.9-11.11) and the ordering hazards (RAPIDS MAS O1-O4).
- Precision and datapath width per core.

## Done when

A short note in the tile docs (or a vault note) lists the ideas worth
adopting, each with the TILE_SPEC section it would change, and the owner has
ruled on each. Cite published sources only (the NorthPole papers and IBM
publications).
