# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2025 sean galloway
#
# RTL Design Sherpa - Industry-Standard RTL Design and Verification
# https://github.com/sean-galloway/RTLDesignSherpa
#
# Module: svsherpa.tools
# Purpose: Verify generated RTL with verilator, verible and yosys
#
# Documentation: docs/markdown/svsherpa/index.md
# Subsystem: svsherpa
#
# Author: sean galloway
# Created: 2026-07-30
"""Toolchain verification.

A generator that emits plausible-looking SystemVerilog is not much use; the
question is always whether the output actually lints, elaborates and
synthesises. These helpers run the real tools on generated text, so a unit test
can assert it.

Each checker degrades to ``skipped`` when its tool is absent rather than
failing, so the suite still runs on a machine without the full flow.

    >>> report = verify(module)          # lint + elaborate + synth
    >>> report.ok
    True
"""

from __future__ import annotations

import shutil
import subprocess
import tempfile
from dataclasses import dataclass, field
from pathlib import Path
from typing import Sequence

# Verilator warnings that are noise for a single generated file checked in
# isolation, not defects in the generated RTL.
VERILATOR_WAIVERS = (
    "DECLFILENAME",   # module name need not match a temp file name
    "UNUSEDSIGNAL",   # svsherpa reports unused signals itself, with names
    "UNUSEDPARAM",
)


@dataclass
class ToolResult:
    """The outcome of one checker."""

    tool: str
    status: str            # pass | fail | skipped
    output: str = ""

    @property
    def ok(self) -> bool:
        return self.status in ("pass", "skipped")

    def __str__(self) -> str:
        mark = {"pass": "PASS", "fail": "FAIL", "skipped": "SKIP"}[self.status]
        return f"[{mark}] {self.tool}"


@dataclass
class Report:
    """The combined outcome of every checker that ran."""

    results: list[ToolResult] = field(default_factory=list)

    @property
    def ok(self) -> bool:
        return all(r.ok for r in self.results)

    @property
    def failures(self) -> list[ToolResult]:
        return [r for r in self.results if r.status == "fail"]

    def __str__(self) -> str:
        lines = [str(r) for r in self.results]
        for failure in self.failures:
            lines.append(f"--- {failure.tool} output ---")
            lines.append(failure.output.strip())
        return "\n".join(lines)


def _run(cmd: Sequence[str], cwd: Path | None = None) -> subprocess.CompletedProcess:
    return subprocess.run(
        list(cmd), capture_output=True, text=True, cwd=cwd, timeout=180, check=False
    )


def _write_sources(
    sv_text: str, name: str, workdir: Path, includes: Sequence[str] = ()
) -> Path:
    """Write *sv_text* plus stub includes so the file compiles standalone."""
    target = workdir / f"{name}.sv"
    # POSIX 3.206: a text file ends in a newline, and verilator enforces it.
    target.write_text(sv_text if sv_text.endswith("\n") else sv_text + "\n")
    inc_dir = workdir / "includes"
    inc_dir.mkdir(exist_ok=True)
    for include in includes:
        src = Path(include)
        dst = inc_dir / src.name
        if src.exists():
            dst.write_text(src.read_text())
    return target


def verilator_lint(
    sv_text: str,
    name: str = "dut",
    *,
    include_dirs: Sequence[str] = (),
    defines: Sequence[str] = (),
    waivers: Sequence[str] = VERILATOR_WAIVERS,
) -> ToolResult:
    """``verilator --lint-only`` -- catches width, driver and elaboration errors."""
    exe = shutil.which("verilator")
    if not exe:
        return ToolResult("verilator lint", "skipped", "verilator not found")
    with tempfile.TemporaryDirectory() as tmp:
        work = Path(tmp)
        target = _write_sources(sv_text, name, work)
        cmd = [exe, "--lint-only", "-Wall", "--timing"]
        for code in waivers:
            cmd.append(f"-Wno-{code}")
        for path in include_dirs:
            cmd.extend(["-I" + str(path)])
        for macro in defines:
            cmd.append(f"+define+{macro}")
        cmd.append(str(target))
        proc = _run(cmd, work)
    output = (proc.stdout + proc.stderr).strip()
    status = "pass" if proc.returncode == 0 else "fail"
    return ToolResult("verilator lint", status, output)


def verible_lint(
    sv_text: str,
    name: str = "dut",
    *,
    waiver_file: str | None = None,
    rules: Sequence[str] = (),
) -> ToolResult:
    """``verible-verilog-lint`` -- style and house-convention checks."""
    exe = shutil.which("verible-verilog-lint")
    if not exe:
        return ToolResult("verible lint", "skipped", "verible-verilog-lint not found")
    with tempfile.TemporaryDirectory() as tmp:
        work = Path(tmp)
        target = _write_sources(sv_text, name, work)
        cmd = [exe]
        if waiver_file and Path(waiver_file).exists():
            cmd.append(f"--waiver_files={waiver_file}")
        if rules:
            cmd.append("--rules=" + ",".join(rules))
        cmd.append(str(target))
        proc = _run(cmd, work)
    output = (proc.stdout + proc.stderr).strip()
    status = "pass" if proc.returncode == 0 else "fail"
    return ToolResult("verible lint", status, output)


def yosys_synth(sv_text: str, name: str = "dut", top: str = "") -> ToolResult:
    """``yosys`` read + hierarchy + synth -- proves the RTL is synthesizable.

    This is the check that separates 'parses' from 'is hardware'. A latch where
    a flop was intended, or a construct that simulates but will not synthesise,
    shows up here.
    """
    exe = shutil.which("yosys")
    if not exe:
        return ToolResult("yosys synth", "skipped", "yosys not found")
    with tempfile.TemporaryDirectory() as tmp:
        work = Path(tmp)
        target = _write_sources(sv_text, name, work)
        top_name = top or name
        script = (
            f"read_verilog -sv {target.name}; "
            f"hierarchy -check -top {top_name}; "
            f"proc; opt; check -assert"
        )
        proc = _run([exe, "-q", "-p", script], work)
    output = (proc.stdout + proc.stderr).strip()
    status = "pass" if proc.returncode == 0 else "fail"
    return ToolResult("yosys synth", status, output)


def verible_format(sv_text: str, name: str = "dut") -> str:
    """Return *sv_text* run through ``verible-verilog-format``.

    Offered as an option, not applied by default: svsherpa's own formatting is
    tuned to house style, and handing output to a general formatter loses the
    column alignment that makes port lists readable.
    """
    exe = shutil.which("verible-verilog-format")
    if not exe:
        return sv_text
    with tempfile.TemporaryDirectory() as tmp:
        work = Path(tmp)
        target = _write_sources(sv_text, name, work)
        proc = _run([exe, str(target)], work)
    return proc.stdout if proc.returncode == 0 else sv_text


def verify(
    module,
    *,
    lint: bool = True,
    style: bool = False,
    synth: bool = True,
    defines: Sequence[str] = (),
    include_dirs: Sequence[str] = (),
    waiver_file: str | None = None,
) -> Report:
    """Run the toolchain against *module* (a Module or an SV string).

    ``style`` is off by default because verible's rule set is a project
    decision; point it at the repo waiver file to turn it on meaningfully.
    """
    sv_text = module if isinstance(module, str) else module.emit()
    name = "dut" if isinstance(module, str) else module.name
    # A macro-style reset needs its definitions, which live outside this file.
    inline = _inline_reset_defs(sv_text) if "`ALWAYS_FF_RST" in sv_text else sv_text

    report = Report()
    if lint:
        report.results.append(
            verilator_lint(
                inline, name, include_dirs=include_dirs, defines=defines
            )
        )
    if style:
        report.results.append(verible_lint(sv_text, name, waiver_file=waiver_file))
    if synth:
        report.results.append(yosys_synth(inline, name, top=name))
    return report


RESET_DEFS_INLINE = """
`define RST_ASSERTED(rst) ( !(rst) )
`define ALWAYS_FF_RST(clk, rst, BODY) \\
    always_ff @(posedge (clk) or negedge (rst)) BODY
"""


def _inline_reset_defs(sv_text: str) -> str:
    """Substitute a standalone definition of the reset macros for checking.

    The real ``reset_defs.svh`` selects sync/async and polarity with compile
    flags. For a lint of one generated file the async active-low form is what
    matters, and inlining it keeps the checker independent of include paths.
    """
    lines = [
        line for line in sv_text.splitlines()
        if not line.strip().startswith('`include "reset_defs.svh"')
    ]
    # Insert after the timescale so the macros precede first use.
    for idx, line in enumerate(lines):
        if line.startswith("`timescale"):
            lines.insert(idx + 1, RESET_DEFS_INLINE)
            return "\n".join(lines)
    return RESET_DEFS_INLINE + "\n".join(lines)
