# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2026 sean galloway
#
# RTL Design Sherpa - Industry-Standard RTL Design and Verification
# https://github.com/sean-galloway/RTLDesignSherpa
#
# Module: battery
# Purpose: riscv-tests battery runner for peregrine_core: every image of a
#          suite (rv32ui, rv32mi, rv32um) runs to its tohost store,
#          passes on tohost == 1, and at func level is locked against
#          spike's commit stream, traps included.
#
# Documentation: projects/components/riscv-ip/peregrine-rv32im/PRD.md
# Subsystem: riscv-ip/peregrine-rv32im
#
# Author: sean galloway
# Created: 2026-11-23

"""riscv-tests batteries for peregrine.

Images are the ``vendor/riscv-tests/isa/<suite>-p-<name>`` ELFs (linked at
0x80000000); the battery reads their PT_LOAD segments into the word image
the TB backdoor loads, so no suite needs a pre-built hex.

Verdict: the p-env ends every test in ``write_tohost`` with
``tohost = (TESTNUM << 1) | 1`` on failure and 1 on pass.  peregrine traps
the final ecall like any other exception, so the store really happens and
the TB reads it off the store port.

Spike lockstep (func level): ``spike --isa=<isa> --priv=m -l``.  The pinned
spike 1.1.0 is built without the commit log, so the ``-l`` log carries
``core 0: 0x<pc> (0x<insn>)`` per executed instruction and
``exception <kind>, epc <pc>`` (+ ``tval``) per trap: the lockstep locks
the (pc, insn) stream, every trap's kind and epc, and its tval.  A trap the
core takes and spike does not, or the reverse, is a failure.  ``--priv=m``
gives spike peregrine's machine-mode-only hart; without it spike has S and
U modes and the tests take different paths.
"""

import os
import re
import struct
import subprocess
from pathlib import Path
from typing import Optional

LINK_BASE = 0x8000_0000

SPIKE = os.environ.get("PEREGRINE_SPIKE", "/mnt/data/tools/spike/bin/spike")

GATE_TESTS = {
    "rv32ui": ("simple", "add", "addi"),
    "rv32mi": ("csr", "scall", "illegal"),
    "rv32um": ("mul", "div", "remu"),
}

# Tests that need hardware peregrine does not have (PRD P6): they are
# reported as excluded, with the reason, never run as passes.
EXCLUDED = {
    "rv32mi": {
        "zicntr": "Zicntr counters (PRD P6: no counters)",
        "instret_overflow": "minstret (PRD P6: no counters)",
        "pmpaddr": "PMP (PRD non-goal)",
        "breakpoint": "debug trigger module (tselect/tdata1), not in P6",
    },
}

# Tests whose expected tohost is a failure that spike reproduces exactly:
# name -> (failing TESTNUM, why).  The core passes such a test only when it
# fails at that TESTNUM AND spike fails there too AND the lockstep matches.
EXPECTED_FAIL = {
    "rv32ui": {
        "ma_data": (668, "needs misaligned loads in hardware; RV32I lets them "
                         "trap, and spike traps at the same TESTNUM"),
    },
}

# spike exception kind for each mcause (exceptions only).
SPIKE_KIND = {
    0: "trap_instruction_address_misaligned",
    1: "trap_instruction_access_fault",       # TASK-005: I$ fill error
    2: "trap_illegal_instruction",
    3: "trap_breakpoint",
    4: "trap_load_address_misaligned",
    5: "trap_load_access_fault",              # TASK-005: SLVERR / DECERR
    6: "trap_store_address_misaligned",
    7: "trap_store_access_fault",             # TASK-005
    11: "trap_machine_ecall",
}

_TEST_CYCLES = 200_000


# ---------------------------------------------------------------------------
# Images and ELF symbols
# ---------------------------------------------------------------------------

def isa_dir(repo_root) -> Path:
    return Path(repo_root) / "vendor" / "riscv-tests" / "isa"


def discover(repo_root, suite: str) -> list:
    """Every <suite>-p-<name> ELF (no extension) in the vendor isa dir."""
    names = sorted(p.name[len(f"{suite}-p-"):]
                   for p in isa_dir(repo_root).glob(f"{suite}-p-*")
                   if p.suffix == "" and p.is_file())
    if not names:
        raise FileNotFoundError(f"no {suite}-p-* ELFs under {isa_dir(repo_root)}")
    return names


def elf_image(path) -> dict:
    """{word_index: word} from an ELF32's PT_LOAD segments (bss zero-filled).

    Read straight from the ELF, so a suite needs no pre-built hex image.
    """
    data = Path(path).read_bytes()
    (phoff,) = struct.unpack_from("<I", data, 0x1C)
    (phentsize, phnum) = struct.unpack_from("<HH", data, 0x2A)
    byte_mem = {}
    for i in range(phnum):
        p_type, p_offset, _, p_paddr, p_filesz, p_memsz = struct.unpack_from(
            "<IIIIII", data, phoff + i * phentsize)
        if p_type != 1:                          # PT_LOAD
            continue
        for k in range(p_memsz):
            byte_mem[p_paddr + k] = data[p_offset + k] if k < p_filesz else 0
    words = {}
    for addr, val in byte_mem.items():
        idx = addr >> 2
        words[idx] = words.get(idx, 0) | (val << (8 * (addr & 3)))
    return words


def read_elf32(path) -> tuple:
    """(entry_pc, {symbol: value}) from a little-endian ELF32 file."""
    data = Path(path).read_bytes()
    if data[:4] != b"\x7fELF" or data[4] != 1 or data[5] != 1:
        raise ValueError(f"{path}: not a little-endian ELF32 file")
    (entry,) = struct.unpack_from("<I", data, 0x18)
    (shoff,) = struct.unpack_from("<I", data, 0x20)
    (shentsize, shnum) = struct.unpack_from("<HH", data, 0x2E)
    sections = [struct.unpack_from("<IIIIIIIIII", data, shoff + i * shentsize)
                for i in range(shnum)]
    symbols = {}
    for sh in sections:
        if sh[1] != 2 or sh[9] == 0:            # SHT_SYMTAB only
            continue
        str_base = sections[sh[6]][4]
        for e in range(sh[5] // sh[9]):
            st_name, st_value = struct.unpack_from("<II", data, sh[4] + e * sh[9])
            end = data.index(b"\x00", str_base + st_name)
            symbols[data[str_base + st_name:end].decode()] = st_value
    return entry, symbols


# ---------------------------------------------------------------------------
# Spike log and lockstep
# ---------------------------------------------------------------------------

_COMMIT_RE = re.compile(r"^core\s+\d+:\s+0x([0-9a-f]+)\s+\(0x([0-9a-f]+)\)")
_EXC_RE = re.compile(r"^core\s+\d+:\s+exception\s+(\S+),\s+epc\s+0x([0-9a-f]+)")
_TVAL_RE = re.compile(r"^core\s+\d+:\s+tval\s+0x([0-9a-f]+)")
_EXEC_RE = re.compile(r"^core\s+\d+:\s+Executed\s+(\d+)\s+times")


def parse_spike_log(path) -> list:
    """Ordered records: ('c', pc, insn) and ('x', kind, epc, tval)."""
    records = []
    with open(path) as fh:
        for line in fh:
            m = _COMMIT_RE.match(line)
            if m:
                records.append(["c", int(m.group(1), 16), int(m.group(2), 16)])
                continue
            m = _EXC_RE.match(line)
            if m:
                records.append(["x", m.group(1), int(m.group(2), 16), None])
                continue
            m = _TVAL_RE.match(line)
            if m and records and records[-1][0] == "x":
                records[-1][3] = int(m.group(1), 16)
                continue
            m = _EXEC_RE.match(line)
            if m and records and records[-1][0] == "c":
                records.extend([list(records[-1])] * (int(m.group(1)) - 1))
    return records


def run_spike(isa: str, elf: Path, log: Path, timeout: int = 120) -> Optional[int]:
    try:
        proc = subprocess.run(
            [SPIKE, f"--isa={isa}", "--priv=m", "-l", f"--log={log}", str(elf)],
            timeout=timeout, capture_output=True, text=True)
    except (subprocess.TimeoutExpired, OSError):
        return None
    return proc.returncode


# Access faults (TASK-005): spike reaches them on addresses it does not map,
# the TB memory by its error windows.  Their tval is checked too.
ACCESS_FAULTS = (1, 5, 7)


def _imm(insn: int) -> int:
    """The I- or S-type immediate of a load or store, sign-extended."""
    if (insn & 0x7F) == 0x23:                         # STORE
        imm = ((insn >> 25) << 5) | ((insn >> 7) & 0x1F)
    else:
        imm = insn >> 20
    return imm - (1 << 12) if imm & 0x800 else imm


def expected_tval(beat: dict) -> Optional[int]:
    """mtval the privileged spec requires for an access-fault trap beat:
    the fetch PC for an instruction access fault, the access's byte address
    (rs1 + imm, from RVFI) for a load or store access fault."""
    cause = beat["trap_cause"]
    if cause == 1:
        return beat["pc"]
    if cause in (5, 7):
        return (beat["rs1_rdata"] + _imm(beat["insn"])) & 0xFFFF_FFFF
    return None


def lockstep(trace: list, entry: int, records: list) -> list:
    """Errors (empty when the core's trace matches spike's stream).

    An instruction access fault has no commit line in spike's log (nothing
    was fetched): the core's trap beat for it (insn 0) is matched against
    the exception record alone.  Access faults also lock their tval.
    """
    j = 0
    while j < len(records) and not (records[j][0] == "c" and records[j][1] == entry):
        j += 1
    if j >= len(records):
        return [f"no spike commit at the ELF entry 0x{entry:x}"]
    for i, beat in enumerate(trace):
        if j >= len(records):
            return [f"spike stream ended at core beat {i} (pc=0x{beat['pc']:x})"]
        rec = records[j]
        if beat["trap"] and beat["trap_cause"] == 1:
            if rec[0] != "x" or rec[1] != SPIKE_KIND[1] or rec[2] != beat["pc"]:
                return [f"beat {i}: core instruction access fault at "
                        f"0x{beat['pc']:x}, spike {rec}"]
            if rec[3] != beat["pc"]:
                return [f"beat {i}: instruction access fault tval: spike "
                        f"{rec[3]}, expected 0x{beat['pc']:x}"]
            j += 1
            continue
        if rec[0] != "c" or rec[1] != beat["pc"] or rec[2] != beat["insn"]:
            return [f"beat {i}: core (pc=0x{beat['pc']:x}, insn=0x{beat['insn']:08x})"
                    f" vs spike {rec}"]
        j += 1
        # (an instruction access fault record belongs to the next beat:
        # its epc is the fetch target, not this instruction)
        spike_exc = (j < len(records) and records[j][0] == "x"
                     and not (records[j][1] == SPIKE_KIND[1]
                              and records[j][2] != beat["pc"]))
        if beat["trap"] and not spike_exc:
            return [f"beat {i}: core trapped (mcause 0x{beat['trap_cause']:x}) at "
                    f"0x{beat['pc']:x}, spike did not"]
        if spike_exc and not beat["trap"]:
            return [f"beat {i}: spike took {records[j][1]} at 0x{beat['pc']:x}, "
                    f"the core did not"]
        if beat["trap"]:
            _, kind, epc, tval = records[j]
            want = SPIKE_KIND.get(beat["trap_cause"], f"mcause 0x{beat['trap_cause']:x}")
            if kind != want or epc != beat["pc"]:
                return [f"beat {i}: core trap {want} at 0x{beat['pc']:x}, spike "
                        f"{kind} at 0x{epc:x}"]
            want_tval = expected_tval(beat)
            if want_tval is not None and tval != want_tval:
                return [f"beat {i}: {kind} tval: spike {tval}, core's access "
                        f"0x{want_tval:x}"]
            j += 1
    return []


# ---------------------------------------------------------------------------
# Battery runner (cocotb)
# ---------------------------------------------------------------------------

class Battery:
    """Run every image of one riscv-tests suite through the core."""

    def __init__(self, tb, repo_root, suite: str, isa: str, level: str,
                 work_dir) -> None:
        self.tb = tb
        self.repo_root = str(repo_root)
        self.suite = suite
        self.isa = isa
        self.level = level
        self.work_dir = Path(work_dir)
        self.work_dir.mkdir(parents=True, exist_ok=True)
        self.results: list = []

    def names(self) -> list:
        names = discover(self.repo_root, self.suite)
        if self.level == "gate":
            names = [n for n in names if n in GATE_TESTS.get(self.suite, ())]
        return names

    async def run(self) -> list:
        log = self.tb.dut._log
        excluded = ({} if os.environ.get("PEREGRINE_RUN_EXCLUDED") == "1"
                    else EXCLUDED.get(self.suite, {}))
        names = self.names()
        log.info(f"peregrine {self.suite} battery ({self.level}): {len(names)} images")
        for name in names:
            if name in excluded:
                self.results.append({"name": name, "status": "EXCLUDED",
                                     "detail": excluded[name]})
                log.info(f"{name}: EXCLUDED ({excluded[name]})")
                continue
            res = await self._run_one(name)
            self.results.append(res)
            log.info(f"{name}: {res['status']} beats={res.get('beats', 0)} "
                     f"traps={res.get('traps', 0)} {res['detail']}")
        self._write_summary()
        failures = [r["name"] for r in self.results if r["status"] == "FAIL"]
        ran = [r for r in self.results if r["status"] != "EXCLUDED"]
        log.info(f"peregrine {self.suite} summary: {len(ran) - len(failures)}/"
                 f"{len(ran)} passed, {len(self.results) - len(ran)} excluded"
                 + (f", failures: {failures}" if failures else ""))
        assert ran, f"{self.suite}: nothing ran"
        assert not failures, f"{self.suite} failures: {failures}"
        return self.results

    async def _run_one(self, name: str) -> dict:
        tb = self.tb
        elf = isa_dir(self.repo_root) / f"{self.suite}-p-{name}"
        entry, symbols = read_elf32(elf)
        tohost = symbols["tohost"]
        await tb.assert_reset()
        await tb.backdoor_load(elf_image(elf))
        await tb.release_reset()
        res = {"name": name, "status": "FAIL", "detail": ""}
        try:
            value = await tb.run_to_tohost(tohost, max_cycles=_TEST_CYCLES)
        except AssertionError as exc:
            res["detail"] = f"timeout: {exc}"
            return res
        res["beats"] = len(tb.trace)
        res["traps"] = sum(b["trap"] for b in tb.trace)
        try:
            tb.check_order_sequence()
            tb.check_x0_rd_zero()
            tb.check_trap_beats()
            tb.check_mem_side_effects()
        except AssertionError as exc:
            res["detail"] = f"trace: {exc}"
            return res
        expected = EXPECTED_FAIL.get(self.suite, {}).get(name)
        want_value = 1 if expected is None else (expected[0] << 1) | 1
        if value != want_value:
            res["detail"] = f"tohost=0x{value:x} (failing TESTNUM {value >> 1})"
            return res
        if self.level != "gate":
            log_path = self.work_dir / f"spike_{self.suite}_{name}.log"
            rc = run_spike(self.isa, elf, log_path)
            want_rc = 0 if expected is None else expected[0] & 0xFF   # exit code, 8 bits
            if rc != want_rc:
                res["detail"] = f"spike rc={rc}, expected {want_rc}"
                return res
            errors = lockstep(tb.trace, entry, parse_spike_log(log_path))
            if errors:
                res["detail"] = "lockstep: " + "; ".join(errors)
                return res
            res["detail"] = ("tohost=1, spike lockstep ok" if expected is None else
                             f"expected fail at TESTNUM {expected[0]}, same as "
                             f"spike, lockstep ok ({expected[1]})")
        else:
            res["detail"] = "tohost=1"
        res["status"] = "PASS"
        return res

    def _write_summary(self) -> None:
        lines = [f"peregrine {self.suite} battery ({self.level})"]
        for r in self.results:
            lines.append(f"{r['name']:<18} {r['status']:<8} {r['detail']}")
        (self.work_dir / f"{self.suite}_summary_{self.level}.txt").write_text(
            "\n".join(lines) + "\n")
