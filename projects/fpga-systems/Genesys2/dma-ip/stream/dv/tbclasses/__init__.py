# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2026 sean galloway
"""Testbench classes shared by every build in this area.

COMPONENT level, not per-build: build-mon and build-perf elaborate the same
`stream_harness` with different parameters, so the UART transport that talks to
it is one class, used by both.

A build keeps its OWN tbclasses/ only for something genuinely build-specific
(build-mon/dv/tbclasses/dma_slave_monitors_tb.py drives a FUB that only the
monitor flavor instantiates).

Available:
- StreamHarnessTB: UART-driven harness transport (CSR, desc_ram, APB, trace)
"""

__all__ = ['StreamHarnessTB']
