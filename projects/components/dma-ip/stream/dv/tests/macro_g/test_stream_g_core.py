# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2026 sean galloway
"""The product dv/tests/macro/test_stream_core.py wrappers, re-hosted on stream_core_g
(this directory's conftest re-points their simulator run). Nothing here but the hookup."""
import test_stream_core as _product   # noqa: E402  (conftest put dv/tests/macro on sys.path)

for _name in dir(_product):
    if _name.startswith('test_'):
        globals()[_name] = getattr(_product, _name)
