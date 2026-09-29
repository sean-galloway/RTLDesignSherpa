"""projects.components -- the component areas.

Import shim for hyphenated area directories (Sean, 2026-09-29: the DMA area is
`projects/components/dma-ip/`, and a hyphen cannot appear in an import
statement). Python code imports it as `projects.components.dma_ip`; the finder
below resolves that name, and everything under it, onto the on-disk `dma-ip`
directory. Nothing else changes: the packages keep their `__init__.py` files
and `from projects.components.dma_ip.rapids.dv.tbclasses.x import Y` is a plain
import line. This module runs before any `projects.components.*` submodule is
imported, which is what makes the alias reliable in pytest and inside the
cocotb simulator process alike.
"""
import importlib.abc
import importlib.machinery
import importlib.util
import os
import sys

_HERE = os.path.dirname(os.path.abspath(__file__))

# importable name -> on-disk directory name
_ALIASES = {
    "dma_ip": "dma-ip",
}


class _AliasFinder(importlib.abc.MetaPathFinder):
    """Resolve projects.components.<alias>[.sub...] onto projects/components/<dir>."""

    prefix = __name__ + "."

    def find_spec(self, fullname, path=None, target=None):
        if not fullname.startswith(self.prefix):
            return None
        parts = fullname[len(self.prefix):].split(".")
        if parts[0] not in _ALIASES:
            return None
        location = os.path.join(_HERE, _ALIASES[parts[0]], *parts[1:])
        if os.path.isdir(location):
            init = os.path.join(location, "__init__.py")
            if os.path.isfile(init):
                return importlib.util.spec_from_file_location(
                    fullname, init, submodule_search_locations=[location])
            # namespace-style package (no __init__.py)
            spec = importlib.machinery.ModuleSpec(fullname, None, is_package=True)
            spec.submodule_search_locations = [location]
            return spec
        if os.path.isfile(location + ".py"):
            return importlib.util.spec_from_file_location(fullname, location + ".py")
        return None


if not any(isinstance(f, _AliasFinder) for f in sys.meta_path):
    sys.meta_path.insert(0, _AliasFinder())
