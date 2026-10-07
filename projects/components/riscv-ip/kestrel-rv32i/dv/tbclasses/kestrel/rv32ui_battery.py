# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2026 sean galloway
#
# RTL Design Sherpa - Industry-Standard RTL Design and Verification
# https://github.com/sean-galloway/RTLDesignSherpa
#
# Module: rv32ui_battery
# Purpose: riscv-tests rv32ui-p-* battery runner for kestrel_core: loads
#          every vendor image, runs it to halt/tohost/timeout, scores the
#          riscv-tests pass/fail convention (tohost == 1), and at func level
#          diffs the RVFI trace against the golden interpreter (all fields)
#          and spike's commit log (pc/insn stream + trap records).
#
# Documentation: projects/components/riscv-ip/README.md
# Subsystem: riscv-ip/kestrel-rv32i
#
# Author: sean galloway
# Created: 2026-10-06

"""rv32ui-p-* battery for the kestrel lockstep TB.

Vendor images: ``vendor/riscv-tests/isa/rv32ui-p-*.hex`` are BYTE-addressed
``objcopy -O verilog`` dumps of ELF images linked at 0x80000000 (p-env
link.ld).  ``normalize_hex.py`` (dv/tests/programs) converts them to the
word-indexed sparse form the TB backdoor loader consumes; the battery
re-keys those words into full core address space (base 0x80000000).

Pass/fail convention: the p-env ends RVTEST_PASS/FAIL with an ecall.  The
kestrel core halts ON the ecall (cause 1), so the trap vector's
``sw gp, tohost`` never executes on the DUT.  The verdict is gp's last
writeback (TESTNUM == 1 is pass, odd >1 is the fail code) — the exact
value the tohost store would have written.  The store port is still
watched for a direct tohost write (run-to-halt/tohost/timeout contract),
and spike's exit code (``tohost >> 1``, fesvr) independently confirms
tohost == 1 on the lockstep side.

Spike lockstep (func level): ``spike --isa=RV32I -l --log=<file> <elf>``
(the ``-l`` flag enables commit logging; ``--log`` alone only redirects
the disabled log).  The pinned spike 1.1.0 commit log carries
``core   0: 0x<pc> (0x<insn>) <disasm>`` per retired instruction plus
``exception <kind>, epc 0x<pc>`` (+ ``tval``) records — register and
memory payloads are NOT in this log format, so rd/mem data is locked by
the interpreter diff instead; spike locks the (pc, insn) stream, the
trap records, and the exit code.

Known spike-vs-core divergence (investigated, not silenced): the p-env
preamble's ``csrwi mnstatus, 8`` (Smrnmi CSR, not in RV32I) traps illegal
in spike while the kestrel CSR stub retires it.  The spike stream still
contains the instruction's commit record, so the 1:1 walk aligns; the
exception record is verified against the just-matched core beat and the
resume pc, counted, and reported per test.  Any OTHER mid-stream spike
exception is a hard failure.
"""

import os
import re
import struct
import subprocess
from pathlib import Path

from tbclasses.kestrel.kestrel_tb import KestrelTB
from tbclasses.kestrel.rv32i_interpreter import RV32IInterpreter

# riscv-tests p-env link base (vendor/riscv-tests/env/p/link.ld).
LINK_BASE = 0x8000_0000

# Gate-level smoke subset (Task 8 brief Step 4); func level runs all.
GATE_TESTS = ("simple", "add", "addi")

# rv32ui-p-* tests that exercise more than a retirement count in spike.
#
# The battery uses a hardware-misaligned spike build: kestrel handles
# misaligned L/S in hardware (plan Global Constraints), and the pinned
# Task-1 spike traps them (spike 1.1.0 gates misaligned support behind the
# compile-time RISCV_ENABLE_MISALIGNED).  rv32ui-p-ma_data therefore fails
# on the pinned binary (exit 156, trap_load/store_address_misaligned) and
# passes on this side-by-side 1.1.0 build (--enable-misaligned, same
# commit).  Override with KESTREL_SPIKE.
SPIKE = os.environ.get("KESTREL_SPIKE",
                       "/mnt/data/tools/spike-misaligned/bin/spike")

_TEST_CYCLES = 100_000


# ---------------------------------------------------------------------------
# Vendor image handling
# ---------------------------------------------------------------------------

def discover_tests(repo_root):
    """Sorted rv32ui-p-* test names from the vendor hex images."""
    isa_dir = Path(repo_root) / "vendor" / "riscv-tests" / "isa"
    names = sorted(p.stem[len("rv32ui-p-"):]
                   for p in isa_dir.glob("rv32ui-p-*.hex"))
    if not names:
        raise FileNotFoundError(f"no rv32ui-p-*.hex under {isa_dir}")
    return names


def normalize_image(repo_root, name):
    """Byte-addressed vendor .hex -> {full_word_address: word} (base applied).

    Reuses normalize_hex.py's loader/packer (dv/tests/programs) so the
    battery consumes exactly what the directed +imem flow produces.
    """
    from normalize_hex import load_byte_image, pack_words
    isa_dir = Path(repo_root) / "vendor" / "riscv-tests" / "isa"
    byte_mem = load_byte_image(isa_dir / f"rv32ui-p-{name}.hex")
    byte_mem = {a - LINK_BASE: v for a, v in byte_mem.items() if a >= LINK_BASE}
    words = pack_words(byte_mem)
    return {(idx + (LINK_BASE >> 2)): w for idx, w in words.items()}


# ---------------------------------------------------------------------------
# Minimal ELF32 reader: entry point and symbol table (tohost discovery)
# ---------------------------------------------------------------------------

def read_elf32(path):
    """Return (entry_pc, {symbol: value}) from a little-endian ELF32 file."""
    data = Path(path).read_bytes()
    if data[:4] != b"\x7fELF" or data[4] != 1:
        raise ValueError(f"{path}: not an ELF32 file")
    if data[5] != 1:
        raise ValueError(f"{path}: not little-endian")
    (entry,) = struct.unpack_from("<I", data, 0x18)
    (shoff,) = struct.unpack_from("<I", data, 0x20)
    (shentsize, shnum) = struct.unpack_from("<HH", data, 0x2E)
    sections = []
    for i in range(shnum):
        off = shoff + i * shentsize
        sections.append(struct.unpack_from("<IIIIIIIIII", data, off))
    symbols = {}
    for sh in sections:
        sh_type = sh[1]
        sh_offset, sh_size = sh[4], sh[5]
        sh_link, sh_entsize = sh[6], sh[9]
        if sh_type != 2 or sh_entsize == 0:      # SHT_SYMTAB only
            continue
        strtab = sections[sh_link]
        str_base = strtab[4]
        for e in range(sh_size // sh_entsize):
            eoff = sh_offset + e * sh_entsize
            st_name, st_value = struct.unpack_from("<II", data, eoff)
            end = data.index(b"\x00", str_base + st_name)
            symbols[data[str_base + st_name:end].decode()] = st_value
    return entry, symbols


# ---------------------------------------------------------------------------
# Spike commit-log parsing and lockstep diff
# ---------------------------------------------------------------------------

_COMMIT_RE = re.compile(
    r"^core\s+\d+:\s+0x([0-9a-f]{8,16})\s+\(0x([0-9a-f]+)\)\s+(.*)$")
_EXC_RE = re.compile(r"^core\s+\d+:\s+exception\s+(\S+),\s+epc\s+0x([0-9a-f]+)")
_TVAL_RE = re.compile(r"^core\s+\d+:\s+tval\s+0x([0-9a-f]+)")
_EXEC_RE = re.compile(r"^core\s+\d+:\s+Executed\s+(\d+)\s+times")


class _Commit:
    __slots__ = ("pc", "insn")

    def __init__(self, pc, insn):
        self.pc = pc
        self.insn = insn


class _Exception:
    __slots__ = ("kind", "epc", "tval")

    def __init__(self, kind, epc):
        self.kind = kind
        self.epc = epc
        self.tval = None


def parse_spike_log(path):
    """Parse a spike --log file into ordered commit/exception records."""
    records = []
    with open(path) as fh:
        for line in fh:
            m = _COMMIT_RE.match(line)
            if m:
                records.append(_Commit(int(m.group(1), 16), int(m.group(2), 16)))
                continue
            m = _EXC_RE.match(line)
            if m:
                records.append(_Exception(m.group(1), int(m.group(2), 16)))
                continue
            m = _TVAL_RE.match(line)
            if m:
                if records and isinstance(records[-1], _Exception):
                    records[-1].tval = int(m.group(1), 16)
                continue
            m = _EXEC_RE.match(line)
            if m:
                # spike collapses consecutive identical (pc, insn) commits;
                # one commit record was already emitted, expand the rest.
                n = int(m.group(1))
                if n > 1 and records and isinstance(records[-1], _Commit):
                    records.extend(_Commit(records[-1].pc, records[-1].insn)
                                   for _ in range(n - 1))
    return records


def run_spike(elf_path, log_path, timeout=120):
    """Run spike --isa=RV32I -l on an rv32ui-p-* ELF; return its exit code
    (None if the run timed out or spike could not start)."""
    try:
        proc = subprocess.run(
            [SPIKE, "--isa=RV32I", "-l", f"--log={log_path}", str(elf_path)],
            timeout=timeout, capture_output=True, text=True)
    except (subprocess.TimeoutExpired, OSError):
        return None
    return proc.returncode


def lockstep_diff(core_trace, halt_pc, entry_pc, records):
    """Diff the core RVFI trace against the parsed spike commit stream.

    Returns (ok, errors, stub_traps, term_trap): errors is a list of
    human-readable failure strings; stub_traps lists the mid-stream spike
    exceptions whose instructions the core stubbed instead of trapping (the
    mnstatus case); term_trap is the spike exception kind at the halt pc.
    """
    errors = []
    stub_traps = []
    term_trap = None

    j = 0
    while j < len(records) and not (
            isinstance(records[j], _Commit) and records[j].pc == entry_pc):
        j += 1
    if j >= len(records):
        return False, [f"no commit at ELF entry 0x{entry_pc:x} in spike log"], \
            [], None

    i = 0
    n = len(core_trace)
    while i < n:
        if j >= len(records):
            errors.append(
                f"spike stream ended at core beat {i} "
                f"(pc=0x{core_trace[i]['pc']:x})")
            break
        r = records[j]
        if isinstance(r, _Exception):
            # Spike trapped the instruction the core just retired (CSR stub).
            prev = records[j - 1] if j > 0 else None
            if isinstance(prev, _Commit) and r.epc == prev.pc and \
                    (r.tval is None or r.tval == prev.insn):
                nxt = records[j + 1] if j + 1 < len(records) else None
                if i < n and (not isinstance(nxt, _Commit) or
                              nxt.pc != core_trace[i]["pc"] or
                              nxt.insn != core_trace[i]["insn"]):
                    errors.append(
                        f"spike resumed at 0x{nxt.pc:x} after {r.kind} at "
                        f"0x{r.epc:x}, core continued at "
                        f"0x{core_trace[i]['pc']:x}")
                    break
                stub_traps.append(r)
                j += 1
                continue
            errors.append(
                f"unexpected mid-stream spike exception {r.kind} at "
                f"0x{r.epc:x} (tval "
                f"{0 if r.tval is None else hex(r.tval)})")
            break
        beat = core_trace[i]
        if r.pc != beat["pc"] or r.insn != beat["insn"]:
            errors.append(
                f"beat {i}: core(pc=0x{beat['pc']:x}, insn=0x{beat['insn']:08x}) "
                f"!= spike(pc=0x{r.pc:x}, insn=0x{r.insn:x})")
            break
        i += 1
        j += 1

    term_trap = None
    if not errors:
        # Termination: the core's final trap beat consumed the spike commit
        # of the halting instruction, so the next record must be the spike
        # exception at the halt pc (ecall or illegal-instruction trap into
        # the p-env's write_tohost tail).
        if j >= len(records) or not isinstance(records[j], _Exception) or \
                records[j].epc != halt_pc:
            if j < len(records) and isinstance(records[j], _Commit):
                got = f"commit 0x{records[j].pc:x}"
            else:
                got = "none"
            errors.append(
                f"spike took no trap at the halt pc 0x{halt_pc:x} "
                f"(next record: {got}; the core halted on an instruction "
                f"spike executed normally)")
        else:
            term_trap = records[j].kind
    return not errors, errors, stub_traps, term_trap


# ---------------------------------------------------------------------------
# Battery runner (cocotb)
# ---------------------------------------------------------------------------

class RV32UIBattery:
    """Run every rv32ui-p-* image through the DUT and score it."""

    def __init__(self, dut, repo_root, level, work_dir, tb_class=None,
                 tests=None):
        self.dut = dut
        self.repo_root = str(repo_root)
        self.level = level
        self.work_dir = Path(work_dir)
        self.work_dir.mkdir(parents=True, exist_ok=True)
        self.results = []
        # Task 11 board path: the same runner with a different TB class (the
        # image loads through the AXIL port instead of the TB backdoor).
        # `tests` pins an explicit subset of image names, overriding both
        # discovery and the gate-level smoke filter.
        self.tb_class = tb_class or KestrelTB
        self.tests = tests

    async def run(self):
        tb = self.tb_class(self.dut, reset_addr=LINK_BASE)
        await tb.ensure_clock()

        names = discover_tests(self.repo_root)
        if self.tests is not None:
            wanted = set(self.tests)
            names = [n for n in names if n in wanted]
        elif self.level == "gate":
            names = [n for n in names if n in GATE_TESTS]
        self.dut._log.info(
            f"rv32ui battery ({self.level} level): {len(names)} tests")

        for name in names:
            result = await self._run_one(tb, name)
            self.results.append(result)
            status = "PASS" if result["passed"] else "FAIL"
            lock = (f" lockstep={'ok' if result['lockstep_ok'] else 'FAIL'}"
                    if result["lockstep_ran"] else "")
            self.dut._log.info(
                f"rv32ui-p-{name}: {status} cause={result['halt_cause']} "
                f"gp={result['gp']} beats={result['beats']}{lock} "
                f"{result['detail']}")

        failures = [r["name"] for r in self.results if not r["passed"]]
        passed = len(self.results) - len(failures)
        self.dut._log.info(
            f"rv32ui battery summary: {passed}/{len(self.results)} passed"
            + (f", failures: {failures}" if failures else ""))
        self._write_summary()
        assert not failures, f"rv32ui battery failures: {failures}"
        return self.results

    def _write_summary(self):
        """Per-test result table to <work_dir>/rv32ui_battery_summary.txt."""
        lines = [
            f"rv32ui battery ({self.level} level) "
            f"{sum(r['passed'] for r in self.results)}/{len(self.results)}",
            f"{'test':<12} {'status':<6} {'cause':<5} {'gp':<10} {'beats':<6} "
            f"{'lockstep':<8} detail",
        ]
        for r in self.results:
            lock = ("ok" if r["lockstep_ok"] else
                    ("FAIL" if r["lockstep_ran"] else "-"))
            lines.append(
                f"rv32ui-p-{r['name']:<5} {'PASS' if r['passed'] else 'FAIL'}"
                f"  {r['halt_cause'] if r['halt_cause'] is not None else 'N/A':<5}"
                f" {r['gp']:#010x} {r['beats']:<6} {lock:<8} {r['detail']}")
        (self.work_dir / f"rv32ui_battery_summary_{self.level}.txt").write_text(
            "\n".join(lines) + "\n")

    async def _run_one(self, tb, name):
        result = {
            "name": name, "passed": False, "halt_cause": None, "gp": 0,
            "beats": 0, "detail": "", "lockstep_ran": False,
            "lockstep_ok": False, "stub_traps": [],
        }
        words = normalize_image(self.repo_root, name)
        elf = Path(self.repo_root) / "vendor" / "riscv-tests" / "isa" / \
            f"rv32ui-p-{name}"
        entry, symbols = read_elf32(elf)
        tohost = symbols.get("tohost")
        if tohost is None:
            raise ValueError(f"{elf}: no tohost symbol")
        result["tohost"] = tohost

        await tb.assert_reset()
        await tb.backdoor_load(words)
        await tb.release_reset()
        try:
            await tb.run_to_halt(max_cycles=_TEST_CYCLES,
                                 watch_tohost=tohost)
        except AssertionError as exc:
            result["detail"] = f"timeout: {exc}"
            return result

        result["halt_cause"] = tb.halt_cause
        result["beats"] = len(tb.trace)
        gp = tb.gp_at_halt()
        result["gp"] = gp
        # riscv-tests convention: 1 = pass.  On this core the tohost store
        # never executes (halt on ecall), so gp-at-halt is the verdict; a
        # direct tohost write of 1 (should one ever commit) also passes.
        passed = (tb.halt_cause == 1 and gp == 1) or (1 in tb.tohost_writes)

        if self.level == "func":
            result["lockstep_ran"] = True
            ok, detail = self._lockstep(tb, name, words, entry, tohost)
            if not ok:
                result["detail"] = detail
                return result
            result["lockstep_ok"] = True
            result["detail"] = detail

        result["passed"] = passed
        if passed and not result["detail"]:
            result["detail"] = "tohost convention (gp==1 at ecall halt)"
        return result

    def _lockstep(self, tb, name, words, entry, tohost):
        """Golden interpreter full-field diff + spike (pc, insn) lockstep.

        Returns (ok, detail).  Raises on interpreter NotImplementedError so
        a core/golden model divergence fails loudly (M2 contract).
        """
        golden = RV32IInterpreter(words, reset_addr=LINK_BASE)
        golden.run()
        try:
            tb.check_halt(expected_cause=golden.halt_cause,
                          expected_halt_pc=golden.halt_pc)
            tb.check_order_sequence()
            tb.check_x0_rd_zero()
            tb.check_trace(golden.trace)
        except AssertionError as exc:
            return False, f"golden diff: {exc}"

        log_path = self.work_dir / f"spike_{name}.log"
        rc = run_spike(
            Path(self.repo_root) / "vendor" / "riscv-tests" / "isa" /
            f"rv32ui-p-{name}", log_path)
        records = parse_spike_log(log_path)
        ok, errors, stub_traps, term_trap = lockstep_diff(
            tb.trace, tb.halt_pc, entry, records)
        stub_kinds = ",".join(sorted({t.kind for t in stub_traps}))
        detail = (f"spike rc={rc} stream ok, {len(records)} records, "
                  f"{len(stub_traps)} stub trap(s) [{stub_kinds}], "
                  f"term trap {term_trap}")
        if rc != 0:
            ok = False
            if rc is None:
                errors.append("spike timed out or failed to start")
            else:
                errors.append(f"spike exit code {rc} (tohost != 1)")
        if not ok:
            return False, "; ".join(errors)
        return True, detail
