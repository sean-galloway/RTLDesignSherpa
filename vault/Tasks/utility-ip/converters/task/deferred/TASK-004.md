# TASK-004: AXI3 monitor-lite observer for seam measurements

**Priority:** P3
**Status:** DEFERRED
**Owner:** TBD

## What

Create an `axi3_monlite` observer module for the DE10 leg-bridge seam that non-intrusively records AXI3 transaction latencies, outstanding counts, and throughput without changing converter behavior.

## Why

Seam-level performance tuning (for example, the tag-based overlap in TASK-003) needs cycle-accurinate, in-system measurements that are too heavy to infer from simulation alone. A lightweight monitor that samples `AR/AW/R/B` handshakes and reports over a simple register interface would provide the required visibility.

## Un-defer condition

A board leg or system integration task needs real seam measurements and is ready to allocate an AXI-Lite register aperture for the observer.
