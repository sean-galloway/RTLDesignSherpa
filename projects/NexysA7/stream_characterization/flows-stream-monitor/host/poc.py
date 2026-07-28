#!/usr/bin/env python3
"""Proof-of-concept for each host routine against the programmed Genesys 2
monitor-coverage bitstream, over the real UART (/dev/ttyUSB2).

Run BEFORE building the full testplan sequences: prove the primitives work on
silicon (link, desc_ram, and especially the NEW cfg AXIL slave -- profile-CAM
load + dense-bin read). Once these pass, the testplan sequences compose them.

Usage:  source env_python && python3 poc.py [--port /dev/ttyUSB2]
"""
import os
import sys
import argparse

_REPO = os.environ.get("REPO_ROOT") or os.path.abspath(
    os.path.join(os.path.dirname(__file__), *[".."] * 5))
sys.path.insert(0, os.path.join(_REPO, "projects/components/converters/bin"))
from uart_axi_bridge import UARTAxiBridge  # noqa: E402

# --- address map (see stream_mon_harness + the bridge TOML) ---
HCSR             = 0x0001_0000
CTRL             = HCSR + 0x00
STATUS           = HCSR + 0x04
SCRATCH          = HCSR + 0x20
BUILD_ID         = HCSR + 0x24
DESC_RAM         = 0x0002_0000
STREAM_TALLY_CFG = 0x0010_0000        # read bins; write config
SLAVE_TALLY_CFG  = 0x0014_0000
PROFILE_CLEAR    = 0x0100             # cfg-slave offset: clear the legal-set CAM
PROFILE_ENTRY    = 0x0200             # cfg-slave offset + idx*4: load a legal key
UNEXPECTED_BIN   = 64                 # dense bin index for out-of-profile packets


def profile_key(agent, proto, ptype, ec):
    return (((agent & 0xFFFF) << 16) | ((proto & 0xF) << 12)
            | ((ptype & 0xF) << 8) | (ec & 0xFF))


class PoC:
    def __init__(self, port):
        self.b = UARTAxiBridge(port=port)
        self.ok = True

    def _chk(self, name, cond, detail=""):
        self.ok = self.ok and bool(cond)
        print(f"  [{'PASS' if cond else 'FAIL'}] {name}{(' ' + detail) if detail else ''}")

    def _hx(self, v):
        return f"0x{v:08X}" if isinstance(v, int) else str(v)

    def r1_link(self):
        print("=== R1: link / ping (scratch R/W + build id) ===")
        for v in (0xDEADBEEF, 0x12345678, 0x00000000, 0xFFFFFFFF):
            self.b.write(SCRATCH, v)
            rb = self.b.read(SCRATCH)
            self._chk(f"scratch {self._hx(v)}", rb == v, f"-> {self._hx(rb)}")
        bid = self.b.read(BUILD_ID)
        self._chk("build id == 'STRC'", bid == 0x53545243, f"-> {self._hx(bid)}")

    def r2_desc_ram(self):
        print("=== R2: desc_ram round-trip (host -> bridge -> desc_ram) ===")
        pat = {0x00: 0xCAFEBABE, 0x04: 0x0BADF00D, 0x20: 0x8BADF00D, 0x24: 0xFEEDFACE}
        for off, v in pat.items():
            self.b.write(DESC_RAM + off, v)
        for off, v in pat.items():
            rb = self.b.read(DESC_RAM + off)
            self._chk(f"desc_ram+0x{off:02x}", rb == v, f"-> {self._hx(rb)}")

    def r3_cfg_slave(self):
        print("=== R3: cfg AXIL slave (NEW) -- profile CAM load + dense-bin read ===")
        # Clear then load two legal tuples (rd/wr AddrMatch).
        self.b.write(STREAM_TALLY_CFG + PROFILE_CLEAR, 0)
        for i, tup in enumerate([(9, 0, 8, 1), (10, 0, 8, 1)]):
            okw = self.b.write(STREAM_TALLY_CFG + PROFILE_ENTRY + i * 4, profile_key(*tup))
            self._chk(f"profile load idx{i} {tup} -> {self._hx(profile_key(*tup))}", okw)
        # Dense bins must be READABLE (pre-DMA they read 0, incl UNEXPECTED).
        for bn in (0, 1, UNEXPECTED_BIN):
            rb = self.b.read(STREAM_TALLY_CFG + bn * 4)
            self._chk(f"stream bin[{bn}] readable (pre-DMA==0)", rb == 0, f"-> {rb}")
        rb = self.b.read(SLAVE_TALLY_CFG + 0)
        self._chk("slave  bin[0] readable", rb is not None, f"-> {rb}")

    def r4_csr(self):
        print("=== R4: harness CSR status read ===")
        st = self.b.read(STATUS)
        self._chk("STATUS readable", st is not None, f"-> {self._hx(st)}")

    def run(self):
        self.r1_link()
        self.r2_desc_ram()
        self.r3_cfg_slave()
        self.r4_csr()
        print(f"\n=== OVERALL: {'PASS' if self.ok else 'FAIL'} ===")
        try:
            self.b.ser.close()
        except Exception:
            pass
        return 0 if self.ok else 1


if __name__ == "__main__":
    ap = argparse.ArgumentParser()
    ap.add_argument("--port", default=os.environ.get("MON_UART", "/dev/ttyUSB2"))
    a = ap.parse_args()
    print(f"[poc] UART {a.port} @ 115200")
    sys.exit(PoC(a.port).run())
