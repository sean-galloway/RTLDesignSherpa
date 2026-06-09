# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2026 sean galloway
"""
Bridge cfg RDL generator (task 90.2).

Renders bridge_pkg/jinja_templates/bridge_cfg.rdl.j2 from a bridge's
adapter list and invokes `peakrdl regblock --cpuif axi4-lite-flat` to
emit the SV regblock. The bridge top (90.3) instantiates that regblock
and routes its hwif_out fields to the existing internal cfg_* nets.

Design notes:
  - Single source of truth for per-monitor cfg fields is the
    MONITOR_CFG_SIGNALS list in
    components/axi4_timing_wrapper_component.py — the template
    mirrors that schema by hand (CTRL + LATENCY + MASKS_A..E) so a
    width change there must be matched in the template. The list
    is small enough that this is fine; a future refinement could
    emit the field defs from MONITOR_CFG_SIGNALS programmatically.
  - Window cfg (Stage A perfmon) is emitted only when the adapter's
    mon_enables['perf'] is True.
  - Address-range cfg is emitted only when n_addr_ranges > 0.
  - Group cfg (mon_group_*) is always emitted at the end of the
    addrmap; it's shared across all monitors at the
    monbus_axil_group inside the bridge.
"""

from __future__ import annotations

import os
import shutil
import subprocess
from dataclasses import dataclass, field
from pathlib import Path
from typing import List, Optional

from jinja2 import Environment, FileSystemLoader


@dataclass
class CfgAdapterPort:
    """One adapter port's contribution to the bridge cfg space.

    `idx` mirrors the bridge-top port-name convention: e.g. host_0,
    stream_desc_1, monbus_wr_2. `has_wr` / `has_rd` come from the
    master's `channels` field ('wr', 'rd', 'rw').
    """
    name: str
    idx: int
    has_wr: bool
    has_rd: bool
    perfmon_enabled: bool = False
    n_addr_ranges: int = 0
    addr_width: int = 32


@dataclass
class CfgRdlGenerator:
    bridge_name: str
    adapters: List[CfgAdapterPort] = field(default_factory=list)
    # Tuple of (base_name, width) for each mon_group_* cfg signal.
    # Pass the bridge generator's _MON_GROUP_CFG list here.
    mon_group_cfg: tuple = ()

    def _build_group_regs(self) -> list:
        """Pack mon_group_cfg into 32-bit register descriptors that the
        Jinja template can iterate. 32-bit fields each get their own
        MON_GROUP_<NAME> reg; 16-bit fields are packed two per register
        as MON_GROUP_PACK_<N>."""
        regs = []
        pack_idx = 0
        pending = None  # (base, width)
        for base, width in self.mon_group_cfg:
            if width == 32:
                regs.append({
                    'reg': f"MON_GROUP_{base.upper()}",
                    'desc': f"mon_group {base} (32-bit)",
                    'width': 32,
                    'field': base,
                })
                if pending is not None:
                    regs.append({
                        'reg': f"MON_GROUP_PACK_{pack_idx}",
                        'desc': f"mon_group pack #{pack_idx} (low half only)",
                        'width': 16,
                        'fields': [{'name': pending[0], 'hi': 15, 'lo': 0}],
                    })
                    pack_idx += 1
                    pending = None
            elif width == 16:
                if pending is None:
                    pending = (base, width)
                else:
                    regs.append({
                        'reg': f"MON_GROUP_PACK_{pack_idx}",
                        'desc': f"mon_group pack #{pack_idx}: {pending[0]} + {base}",
                        'width': 16,
                        'fields': [
                            {'name': pending[0], 'hi': 15, 'lo': 0},
                            {'name': base,       'hi': 31, 'lo': 16},
                        ],
                    })
                    pack_idx += 1
                    pending = None
            else:
                raise NotImplementedError(
                    f"mon_group field {base!r} unsupported width {width}"
                )
        if pending is not None:
            regs.append({
                'reg': f"MON_GROUP_PACK_{pack_idx}",
                'desc': f"mon_group pack #{pack_idx} (low half only)",
                'width': 16,
                'fields': [{'name': pending[0], 'hi': 15, 'lo': 0}],
            })
        return regs

    def render_rdl(self, template_dir: Optional[Path] = None) -> str:
        """Render the bridge_cfg.rdl.j2 template into RDL text."""
        if template_dir is None:
            template_dir = (
                Path(__file__).resolve().parent.parent / 'jinja_templates'
            )
        env = Environment(
            loader=FileSystemLoader(str(template_dir)),
            trim_blocks=True,
            lstrip_blocks=True,
        )
        env.globals['range'] = range
        template = env.get_template('bridge_cfg.rdl.j2')
        return template.render(
            bridge_name=self.bridge_name,
            adapters=self.adapters,
            group_regs=self._build_group_regs(),
        )

    def write_rdl(self, output_dir: Path) -> Path:
        """Render + write the .rdl. Returns the written path."""
        output_dir.mkdir(parents=True, exist_ok=True)
        rdl_path = output_dir / f'{self.bridge_name}_cfg.rdl'
        rdl_path.write_text(self.render_rdl(), encoding='utf-8')
        return rdl_path

    def run_peakrdl(
        self,
        rdl_path: Path,
        output_dir: Path,
        peakrdl_bin: str = 'peakrdl',
    ) -> List[Path]:
        """Invoke peakrdl regblock --cpuif axi4-lite-flat on rdl_path.

        Returns the list of generated SV files. The caller is
        responsible for adding them to the bridge's filelist.
        """
        if shutil.which(peakrdl_bin) is None:
            raise RuntimeError(
                f"peakrdl binary not found on PATH ({peakrdl_bin!r}). "
                "Install with: pip install peakrdl peakrdl-regblock"
            )
        output_dir.mkdir(parents=True, exist_ok=True)
        cmd = [
            peakrdl_bin, 'regblock',
            str(rdl_path),
            '--cpuif', 'axi4-lite-flat',
            '-o', str(output_dir),
        ]
        env = os.environ.copy()
        result = subprocess.run(
            cmd, cwd=str(output_dir.parent), env=env,
            capture_output=True, text=True, check=False,
        )
        if result.returncode != 0:
            raise RuntimeError(
                f"peakrdl regblock failed ({result.returncode}):\n"
                f"stdout:\n{result.stdout}\nstderr:\n{result.stderr}"
            )
        # peakrdl emits {basename}.sv + {basename}_pkg.sv
        base = rdl_path.stem
        out_sv = output_dir / f'{base}.sv'
        out_pkg = output_dir / f'{base}_pkg.sv'
        return [out_pkg, out_sv]

    def generate(
        self,
        output_dir: Path,
        run_peakrdl: bool = True,
    ) -> dict:
        """Convenience: write RDL + optionally run peakrdl. Returns a
        dict with 'rdl_path' and 'sv_paths' (empty list if !run_peakrdl).
        """
        rdl_path = self.write_rdl(output_dir)
        sv_paths: List[Path] = []
        if run_peakrdl:
            sv_paths = self.run_peakrdl(rdl_path, output_dir)
        return {'rdl_path': rdl_path, 'sv_paths': sv_paths}
