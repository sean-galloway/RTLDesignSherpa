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
            if width in (1, 32):
                if width == 32:
                    regs.append({
                        'reg': f"MON_GROUP_{base.upper()}",
                        'desc': f"mon_group {base} (32-bit)",
                        'width': 32,
                        'field': base,
                    })
                else:  # width == 1: solo 1-bit register
                    regs.append({
                        'reg': f"MON_GROUP_{base.upper()}",
                        'desc': f"mon_group {base} (1-bit)",
                        'width': 1,
                        'field': base,
                        # Default compression ON (project rule: monitors in
                        # use => compress). Harmless when no compressor HW.
                        'reset': "1'h1",
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
        # peakrdl runs with cwd=output_dir.parent, so any relative paths
        # we pass would resolve against that cwd, not the caller's.
        # Resolve both to absolute paths so peakrdl always sees the same
        # files regardless of where bridge_generator.py was invoked from.
        rdl_abs = rdl_path.resolve()
        out_abs = output_dir.resolve()
        cmd = [
            peakrdl_bin, 'regblock',
            str(rdl_abs),
            '--cpuif', 'axi4-lite-flat',
            '-o', str(out_abs),
        ]
        env = os.environ.copy()
        result = subprocess.run(
            cmd, cwd=str(out_abs.parent), env=env,
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
        self._patch_resp_buffer_reset(out_sv)
        return [out_pkg, out_sv]

    # Reset loop PeakRDL's axi4-lite CPUIF emits for its response buffer. It is
    # an unpacked array of a struct, reset element-by-element inside a for.
    _RESP_RESET_LOOP = """            for(int i=0; i<2; i++) begin
                axil_resp_buffer[i].is_wr <= '0;
                axil_resp_buffer[i].err <= '0;
                axil_resp_buffer[i].rdata <= '0;
            end
"""
    # The loop UNROLLED, not collapsed. `axil_resp_buffer <= '{default: '0};`
    # also clears BLKLOOPINIT but then trips a Verilator CODEGEN bug: it emits
    # C++ assigning `unsigned int` to the struct type and g++ rejects it
    # ("no match for operator="). Per-field scalar assignments avoid both.
    _RESP_RESET_WHOLE = """            // Reset unrolled from PeakRDL's per-element for loop by
            // cfg_rdl_generator -- see the note there. Same assignments,
            // no loop.
            axil_resp_buffer[0].is_wr <= '0;
            axil_resp_buffer[0].err <= '0;
            axil_resp_buffer[0].rdata <= '0;
            axil_resp_buffer[1].is_wr <= '0;
            axil_resp_buffer[1].err <= '0;
            axil_resp_buffer[1].rdata <= '0;
"""

    @classmethod
    def _patch_resp_buffer_reset(cls, sv_path: Path) -> None:
        """Rewrite PeakRDL's response-buffer reset loop as a whole-array reset.

        Verilator cannot elaborate a non-blocking assignment to an array with a
        COMPOUND element type inside a loop -- `%Error-BLKLOOPINIT: Unsupported`
        -- and once it hits that in an always_ff it rejects every compound-array
        NBA in the block, 9 errors in the emitted regblock. That fails the BUILD,
        so every test on a regblock bridge dies before it starts. It is not a
        warning and cannot be waived.

        An unroll budget does NOT help here, which is the obvious first guess:
        measured 9 errors both with and without
        `--unroll-count 16384 --unroll-stmts 200000`. The loop bound is 2; the
        problem is the compound element type, not the iteration count.

        The rewrite UNROLLS the loop rather than collapsing it.
        `axil_resp_buffer <= '{default: '0};` also clears BLKLOOPINIT, but then
        trips a Verilator codegen bug -- the emitted C++ assigns `unsigned int`
        to the struct type and g++ rejects it. Per-field scalar assignments,
        which is what the loop expanded to anyway, avoid both. Same six
        assignments, no loop.

        The transform is a strict, exact-text replacement and it ASSERTS that it
        matched. If a PeakRDL upgrade changes the template, this fails loudly
        instead of silently emitting RTL that will not build -- the failure mode
        that let the original sit unnoticed.
        """
        text = sv_path.read_text()
        if cls._RESP_RESET_LOOP not in text:
            # Already the whole-array form, or a template that no longer needs
            # the fix -- but say which, so "no patch" is never silent.
            if "axil_resp_buffer[1].rdata <= '0;" in text:
                return
            raise RuntimeError(
                f"{sv_path.name}: cfg_rdl_generator could not find PeakRDL's "
                f"axil_resp_buffer reset loop to rewrite, and the whole-array "
                f"form is not present either. The PeakRDL template has changed. "
                f"Re-check whether Verilator still rejects the emitted reset "
                f"(BLKLOOPINIT) and update _RESP_RESET_LOOP, or delete this "
                f"patch if it is no longer needed."
            )
        sv_path.write_text(text.replace(cls._RESP_RESET_LOOP,
                                        cls._RESP_RESET_WHOLE))

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
