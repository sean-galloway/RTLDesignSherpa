# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2026 sean galloway
"""The product dv/tests/top/test_stream_top_regs.py wrappers, re-hosted on the
stream-g tops (this directory's conftest re-points their simulator run at
stream_g_top_ch8 / stream_g_top_ch16). Nothing here but the hookup."""
import test_stream_top_regs as _product   # noqa: E402  (conftest put dv/tests/top on sys.path)

for _name in dir(_product):
    if _name.startswith('test_'):
        globals()[_name] = getattr(_product, _name)
