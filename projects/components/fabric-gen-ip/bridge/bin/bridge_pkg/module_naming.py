# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2026 sean galloway
"""Names of the modules a bridge generates, in one place.

Every module a bridge emits must carry the bridge's name. The port adapters
used to be named after the port alone (``<port>_adapter``), and every bridge
emits a ``subtractive_adapter`` for its catch-all slave, so two generated
bridges in one design -- a configuration bridge beside a data bridge, as the
Genesys 2 fabric benchmark has -- defined the same module twice with
different bodies (each imports its own ``<bridge>_pkg``). The adapter FILES
keep their ``<port>_adapter.sv`` names, so generated filelists and the
generator tests that read them are unchanged; only the module names move.
"""


def adapter_module_name(bridge_name: str, port_name: str) -> str:
    """Module name of the adapter for master or slave port `port_name`."""
    return f"{bridge_name}_{port_name}_adapter"
