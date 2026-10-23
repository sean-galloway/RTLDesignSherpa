# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2026 sean galloway
#
# RTL Design Sherpa - Industry-Standard RTL Design and Verification
# https://github.com/sean-galloway/RTLDesignSherpa
#
# Module: test_rapids_g_cxs_top
# Purpose: rapids-g (rapids TASK-034): every product rapids_cxs_top test, unchanged,
#          on rapids_g_cxs_top -- the same top with its schedulers sequenced by gatling.
#
# Author: sean galloway
# Created: 2026-10-21

"""The product dv/tests/top/test_rapids_cxs_top.py wrappers, re-hosted on rapids_g_cxs_top
(rapids_g_rehost). Nothing here but the hookup: the tests, their parameters
and their checks are the product's."""

from rapids_g_rehost import rehost

import test_rapids_cxs_top as _product   # noqa: E402  (rapids_g_rehost put its directory on sys.path)

rehost(_product, globals(), {
    'DATA_WIDTH': 512, 'ADDR_WIDTH': 64, 'AXI_ID_WIDTH': 8, 'SRAM_DEPTH': 512,
    'APB_ADDR_WIDTH': 13, 'APB_DATA_WIDTH': 32,
})
