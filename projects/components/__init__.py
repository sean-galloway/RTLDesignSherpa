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
    # 2026-09-29 (Sean): the rest of the family directories, same rule
    "utility_ip": "utility-ip",        # converters, misc
    "noc_ip": "noc-ip",                # delta
    "compute_eng_ip": "compute-eng-ip",  # hive
    "ecc_ip": "ecc-ip",                # reed-solomon, bch
    "cache_ip": "cache-ip",            # amber-mesi-l1, onyx-ace-ccu
    "fabric_gen_ip": "fabric-gen-ip",  # apbx-xbar, bridge
    "mem_ctrl_ip": "mem-ctrl-ip",      # pumice, scoria, andesite
}


def _resolve(parts):
    """Walk projects/components/<family>/... one segment at a time. A segment
    is taken as written when it exists (a `.py` counts); otherwise its
    hyphenated spelling is used, so `reed_solomon` finds `reed-solomon` and
    `pumice_ddr2_lpddr2` finds `pumice-ddr2-lpddr2` without a table entry
    per component. Only the family level is looked up by table."""
    base = os.path.join(_HERE, _ALIASES[parts[0]])
    for part in parts[1:]:
        cand = os.path.join(base, part)
        if os.path.exists(cand) or os.path.isfile(cand + ".py"):
            base = cand
        else:
            base = os.path.join(base, part.replace("_", "-"))
    return base


class _AliasFinder(importlib.abc.MetaPathFinder):
    """Resolve projects.components.<alias>[.sub...] onto projects/components/<dir>."""

    prefix = __name__ + "."

    def find_spec(self, fullname, path=None, target=None):
        if not fullname.startswith(self.prefix):
            return None
        parts = fullname[len(self.prefix):].split(".")
        if parts[0] not in _ALIASES:
            return None
        location = _resolve(parts)
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
