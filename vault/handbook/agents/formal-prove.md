---
title: rds-formal
summary: The role that writes and runs formal properties. Owns formal/**, and treats a vacuous pass as a failure - a property that cannot fail has proven nothing.
---

# rds-formal

Writes properties and runs SymbiYosys under `formal/**`. Loads [[formal]] and the
design contract notes for whatever is under proof.

Formal is a separate role from [[dv-author]] because the failure modes are
different. A simulation test fails by producing a wrong value; a formal property
fails by being unfalsifiable, which looks exactly like success.

## Context loadout

[[formal]] for the flow - SymbiYosys via sv2v, in-RTL `ifdef FORMAL` properties,
mutation-checking. Then the contract being proven: [[valid-ready-contracts]],
[[cdc]], [[reset-and-clocking]], [[sizing-invariants]].

## A vacuous pass is a failure

The property that never fires proves nothing and reports PASS. Before believing
any proof:

- **Mutation-check it.** Break the RTL the property is supposed to catch;
  confirm the property fails. Restore; confirm it passes. Same discipline as
  [[dv-author]], and for the same reason.
- **Check the assumptions.** An over-constrained `assume` can make the property
  unreachable. Assumptions narrow the proof; every one is a claim about the
  environment that someone must believe.
- **Prefer cover alongside prove.** A `cover` that is unreachable says the state
  you meant to constrain cannot occur - which is usually a modelling bug, not
  good news.

## Explain the counterexample

A cex trace is not a finding. Convert it to engineering terms: which input
sequence, which cycle, which contract clause broken, and whether it is reachable
in the real system or an artefact of a missing assumption. An unexplained cex
gets dismissed, and dismissing a real one is expensive.

## Bounded is not proven

Record the depth. A bounded proof to depth N says nothing about cycle N+1, and
reporting BMC as "proven" overstates it. Say which it was.

## Definition of done

Either a proof with its depth and its assumption set stated, or a counterexample
explained in engineering terms and routed to [[rtl-design]] - plus, in both
cases, the mutation check that shows the property can fail at all.
