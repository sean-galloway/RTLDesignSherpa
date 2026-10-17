# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2026 sean galloway
#
# Build-time bundling for the bridge generator wheel. Metadata lives in
# pyproject.toml; this file only adds the copies the wheel must carry.

"""Bundle the RTL closure and the repo-bin helpers into the wheel."""

import importlib.util
import shutil
from pathlib import Path

from setuptools import setup
from setuptools.command.build_py import build_py

HERE = Path(__file__).resolve().parent
BIN = HERE / 'bin'
# The checkout root: the nearest ancestor holding the filelist registry and
# the amba RTL (the same test bridge_pkg/_paths.rds_root() applies).
REPO = next((p for p in HERE.parents
             if (p / 'bin' / 'filelists.toml').is_file() and (p / 'rtl' / 'amba').is_dir()),
            HERE)


def _load_ip_closure():
    # By path, not `import bridge_pkg`: the isolated build environment has no
    # jinja2/pyyaml, and ip_closure needs only the standard library.
    spec = importlib.util.spec_from_file_location(
        'bridge_ip_closure', BIN / 'bridge_pkg' / 'ip_closure.py')
    mod = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(mod)
    return mod


class BuildWithBundle(build_py):
    def run(self):
        super().run()
        if not (REPO / 'bin' / 'filelists.toml').is_file():
            raise SystemExit(
                f"bridge wheel must be built from an RTL Design Sherpa checkout "
                f"(no bin/filelists.toml under {REPO})")
        pkg = Path(self.build_lib) / 'bridge_pkg'
        vendor = pkg / '_vendor'
        shutil.rmtree(vendor, ignore_errors=True)
        shutil.copytree(REPO / 'bin' / 'rtl_generators' / 'verilog',
                        vendor / 'rtl_generators' / 'verilog',
                        ignore=shutil.ignore_patterns('__pycache__', '*.pyc'))
        shutil.copy2(REPO / 'bin' / 'rtl_generators' / '__init__.py',
                     vendor / 'rtl_generators' / '__init__.py')
        shutil.copy2(REPO / 'bin' / 'peakrdl_generate.py', vendor / 'peakrdl_generate.py')

        closure = _load_ip_closure().closure(REPO)
        ip = pkg / 'ip'
        shutil.rmtree(ip, ignore_errors=True)
        for rel in sorted(closure.files):
            dst = ip / rel
            dst.parent.mkdir(parents=True, exist_ok=True)
            shutil.copy2(REPO / rel, dst)
        # Headers reached only by `include (never named in a .f) ride along
        # with their include directory.
        for rel in sorted(closure.incdirs):
            (ip / rel).mkdir(parents=True, exist_ok=True)
            for hdr in sorted((REPO / rel).glob('*.svh')) + sorted((REPO / rel).glob('*.vh')):
                shutil.copy2(hdr, ip / rel / hdr.name)
        print(f"bundled {len(closure.files)} RTL/filelist files into {ip}")


setup(cmdclass={'build_py': BuildWithBundle})
