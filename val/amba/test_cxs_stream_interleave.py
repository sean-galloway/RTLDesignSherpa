# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2026 sean galloway
#
# RTL Design Sherpa - Industry-Standard RTL Design and Verification
# https://github.com/sean-galloway/RTLDesignSherpa
#
# Module: test_cxs_stream_interleave
# Purpose: per-stream packet framing (IHI 0079D 2.5.2) in cxs_master and
#          cxs_slave: four streams interleaved flit by flit on one link
#
# Documentation: docs/markdown/rtl-amba/cxs/README.md
# Subsystem: amba
# Author: sean galloway
# Created: 2026-10-16
"""Each DUT runs twice on the same traffic: with CXS_STREAM_SRCID_BITS = 2
(the four streams tracked) every flit must pass with protocol_error low; with
the key off the endpoint frames the link as one stream and protocol_error
MUST rise. Scenarios and claims: bin/TBClasses/cxs/cxs_interleave_tb.py."""
import os

import pytest
import cocotb

from CocoTBFramework.components.cxs import CXSConfig
from TBClasses.cxs.cxs_interleave_tb import CXSMasterInterleaveTB, CXSSlaveInterleaveTB
from cxs_test_common import COUNTS, current_test_level, run_cxs

CFG = CXSConfig(issue='D', data_width=512, max_pkt_per_flit=2, srcid_width=4, max_credit=15)


@cocotb.test(timeout_time=50, timeout_unit="ms")
async def cxs_stream_interleave_test(dut):
    cls = CXSSlaveInterleaveTB if os.environ['DUT'] == 'cxs_slave' else CXSMasterInterleaveTB
    tb = cls(dut) if cls is CXSMasterInterleaveTB else cls(dut, rx_fifo_depth=CFG.max_credit)
    await tb.setup_clocks_and_reset()
    passed = await tb.run_interleaved(COUNTS[current_test_level()])
    assert passed, f"{len(tb.errors)} error(s); first: {tb.errors[:1]}"


@pytest.mark.parametrize("dut_name", ["cxs_slave", "cxs_master"])
@pytest.mark.parametrize("key_bits", [2, 0])
def test_cxs_stream_interleave(request, dut_name, key_bits):
    os.environ['TEST_NSTREAMS'] = '4'
    os.environ['EXPECT_PROTOCOL_ERROR'] = '1' if key_bits == 0 else '0'
    run_cxs(request, dut_name, CFG, current_test_level(),
            {'CXS_STREAM_SRCID_BITS': key_bits}, tag_extra=f"_key{key_bits}")
