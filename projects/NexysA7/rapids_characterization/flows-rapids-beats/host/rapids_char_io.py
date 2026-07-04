# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2026 sean galloway
#
# Module: rapids_char_io
# Purpose: Host-side UART transport + AXIL region map for rapids_char_top.
#          Reuses the repo's existing UARTAxiBridge (the SAME wire protocol the
#          stream_char host uses) to drive the FPGA over 115200-8N1, and layers
#          the rapids_char_top word-address region map on top of it.
#
# Wire protocol (uart_axil_bridge.sv, ASCII, verified by its README/TB):
#   write:  "W <addr_hex8> <data_hex8>\n"  -> "OK\n"
#   read:   "R <addr_hex8>\n"              -> "0x<data_hex>\n"
# UARTAxiBridge (projects/components/converters/bin/uart_axi_bridge.py) already
# implements this exactly, so we do NOT re-implement byte framing here.
#
# Host word-address map (region = addr[19:16]), from rapids_char_top.sv header:
#   0x0_0000  DUT-REG   : AXIL -> apb_master -> harness s_apb (addr[12:0]=APB byte)
#   0x1_0000  DESC-LOAD : DESC_WORD[0..7] + DESC_ADDR + DESC_KICK + DESC_STATUS
#   0x2_0000  HARNESS CSR: gen/chk/mem/mon control + status readback
#
# Author: sean galloway
# Created: 2026-07-04

"""UART transport and AXIL region map for the RAPIDS beats char board."""

import os
import sys
import time

# The UART/AXIL wire driver lives with the converter RTL it talks to. Reuse it
# rather than re-rolling serial framing (single source of truth for the protocol).
_CONVERTERS_BIN = os.path.join(
    os.environ.get('REPO_ROOT', ''),
    'projects/components/converters/bin')
if _CONVERTERS_BIN and _CONVERTERS_BIN not in sys.path:
    sys.path.insert(0, _CONVERTERS_BIN)

try:
    from uart_axi_bridge import UARTAxiBridge
except ImportError:  # pragma: no cover - only hit without REPO_ROOT / pyserial
    UARTAxiBridge = None


# ---------------------------------------------------------------------------
# Region bases (region = host word-address bits [19:16]).
# ---------------------------------------------------------------------------
REGION_APB = 0x0        # DUT-REG
REGION_DESC = 0x1       # DESC-LOAD
REGION_CSR = 0x2        # HARNESS CSR
_REGION_SHIFT = 16


def region_base(region: int) -> int:
    return region << _REGION_SHIFT


# ---------------------------------------------------------------------------
# DUT-REG (region 0) sub-addresses: 13-bit APB byte address. The half is
# selected by APB addr bit[12] (SRC=0x0000, SNK=0x1000), matching the two
# RegisterMap start_addresses used by rapids_char_harness_tb.py.
# ---------------------------------------------------------------------------
APB_SRC_BASE = 0x0000
APB_SNK_BASE = 0x1000


# ---------------------------------------------------------------------------
# DESC-LOAD (region 1) byte offsets (rapids_char_top.sv).
# ---------------------------------------------------------------------------
DESC_WORD0 = 0x000       # DESC_WORD[0..7] at 0x000..0x01C (word i = desc[32i+31:32i])
DESC_ADDR = 0x020        # target byte address in the descriptor RAM
DESC_KICK = 0x024        # write issues the AXI4 desc write; data[0]=half (0=SRC,1=SNK)
DESC_STATUS = 0x028      # read: [0]=last descriptor write BRESP OK


# ---------------------------------------------------------------------------
# HARNESS CSR (region 2) byte offsets (rapids_char_top.sv).
# ---------------------------------------------------------------------------
# Writable
CSR_CTRL = 0x000         # [0] cam_clear pulse
CSR_GEN_CTRL = 0x010     # [0] cfg_gen_start (level)
CSR_GEN_SEED = 0x014
CSR_GEN_NBEATS = 0x018
CSR_GEN_BPP = 0x01C
CSR_GEN_CHMASK = 0x020
CSR_GEN_TDEST = 0x024
CSR_CHK_CTRL = 0x030     # [0] chk_cfg_start (level) [1] chk_ready_en (level)
CSR_CHK_SEED = 0x034
CSR_MEM_CTRL = 0x040     # [0] rd_crc_lfsr_reset pulse  [1] wr_crc_reset pulse
CSR_MON_BASE = 0x050
CSR_MON_LIMIT = 0x054
CSR_MON_FLUSHWM = 0x058
CSR_CH_SEL = 0x060       # selects channel for indexed per-channel reads
# Readable
CSR_ID = 0x000           # 0x52415031 ("RAP1")
CSR_STATUS = 0x080
CSR_GEN_BEATS_T = 0x084
CSR_CHK_BEATS_T = 0x088
CSR_PKT_CNT = 0x08C
CSR_RD_BEATS_T = 0x090
CSR_WR_BEATS_T = 0x094
CSR_SRC_SCHERR = 0x098
CSR_SNK_SCHERR = 0x09C
CSR_GEN_EXP_CRC = 0x0A0  # GEN_EXPECTED_CRC[CH_SEL]
CSR_CHK_ACT_CRC = 0x0A4  # CHK_ACTUAL_CRC[CH_SEL]
CSR_RD_CRC = 0x0A8       # RD_CRC_VALUE[CH_SEL]
CSR_WR_CRC = 0x0AC       # WR_CRC_VALUE[CH_SEL]
CSR_GEN_EXP_VLD = 0x0B0
CSR_CHK_ACT_VLD = 0x0B4
CSR_RD_CRC_VLD = 0x0B8
CSR_WR_CRC_VLD = 0x0BC

CSR_ID_EXPECTED = 0x5241_5031  # "RAP1"

# STATUS bitfield (CSR_STATUS).
STATUS_MON_IRQ = 1 << 0
STATUS_SRC_IDLE = 1 << 1
STATUS_SNK_IDLE = 1 << 2
STATUS_GEN_BUSY = 1 << 3
STATUS_GEN_DONE = 1 << 4
STATUS_DATA_ERROR = 1 << 5
STATUS_RD_MEM_BUSY = 1 << 6
STATUS_WR_MEM_BUSY = 1 << 7


class RapidsCharIO:
    """AXIL region-aware transport over the rapids_char_top UART link."""

    def __init__(self, port='/dev/ttyUSB1', baudrate=115200, timeout=1.0,
                 bridge=None):
        """Open the UART link (or wrap an existing UARTAxiBridge).

        Pass an already-open `bridge` to share a session with other host tools.
        """
        if bridge is not None:
            self.bridge = bridge
            self._owns_bridge = False
        else:
            if UARTAxiBridge is None:
                raise RuntimeError(
                    "UARTAxiBridge unavailable: set REPO_ROOT and `pip install "
                    "pyserial` (it lives in projects/components/converters/bin).")
            self.bridge = UARTAxiBridge(port=port, baudrate=baudrate,
                                        timeout=timeout)
            self._owns_bridge = True

    # ---- Raw 32-bit AXIL primitives (delegated to the UART bridge) ----------

    def axil_write(self, addr: int, data: int) -> bool:
        """32-bit AXIL write. Returns True when the bridge acked with 'OK'."""
        return bool(self.bridge.write(addr & 0xFFFF_FFFF, data & 0xFFFF_FFFF))

    def axil_read(self, addr: int) -> int:
        """32-bit AXIL read. Returns the data word (or None on parse error)."""
        return self.bridge.read(addr & 0xFFFF_FFFF)

    # ---- Region helpers -----------------------------------------------------

    def dut_reg_write(self, apb_byte_addr: int, data: int) -> bool:
        return self.axil_write(region_base(REGION_APB) | apb_byte_addr, data)

    def dut_reg_read(self, apb_byte_addr: int) -> int:
        return self.axil_read(region_base(REGION_APB) | apb_byte_addr)

    def desc_write(self, offset: int, data: int) -> bool:
        return self.axil_write(region_base(REGION_DESC) | offset, data)

    def desc_read(self, offset: int) -> int:
        return self.axil_read(region_base(REGION_DESC) | offset)

    def csr_write(self, offset: int, data: int) -> bool:
        return self.axil_write(region_base(REGION_CSR) | offset, data)

    def csr_read(self, offset: int, retries: int = 3) -> int:
        """Robust 32-bit CSR read.

        The underlying UARTAxiBridge occasionally returns a malformed/short
        frame (parsed as None, or raises mid-frame). Re-issue the read a couple
        of times before giving up rather than propagating a spurious None into
        the scoreboard (which would look like a false failure). The wire
        protocol is unchanged — this is a pure host-side retry.
        """
        addr = region_base(REGION_CSR) | offset
        result = None
        for attempt in range(max(1, retries)):
            try:
                result = self.axil_read(addr)
            except Exception:  # noqa: BLE001 - bad frame surfaces as an exception
                result = None
            if result is not None:
                return result
            if attempt + 1 < retries:
                time.sleep(0.005)  # let the UART line settle before retrying
        return result

    # ---- Convenience: CSR pulses / selected-channel reads -------------------

    def cam_clear(self) -> None:
        self.csr_write(CSR_CTRL, 0x1)

    def select_channel(self, channel: int) -> None:
        """Point the indexed per-channel CSR reads (0xA0-0xAC) at `channel`."""
        self.csr_write(CSR_CH_SEL, channel)

    def read_status(self) -> int:
        return self.csr_read(CSR_STATUS)

    def ping(self) -> bool:
        """Verify the UART link + CSR block are alive via the ID register."""
        return self.csr_read(CSR_ID) == CSR_ID_EXPECTED

    # ---- Descriptor load into on-chip descriptor RAM ------------------------

    def load_descriptor(self, half: str, ram_byte_addr: int, desc_words) -> bool:
        """Assemble a 256-bit descriptor in the DESC-LOAD holding registers and
        issue ONE single-beat AXI4 write into the SRC/SNK descriptor RAM.

        This mirrors the cocotb TB's load_descriptor() (which drives the same
        desc_src_*/desc_snk_* host-write port directly). `half` is 'src' or 'snk';
        `ram_byte_addr` is where the DUT will fetch the descriptor when kicked;
        `desc_words` is the 8-word list from descriptor_to_words().
        Returns the DESC_STATUS OK bit after the write.
        """
        if len(desc_words) != 8:
            raise ValueError(f"expected 8 descriptor words, got {len(desc_words)}")
        half_sel = 0 if half == 'src' else 1

        for i, word in enumerate(desc_words):
            self.desc_write(DESC_WORD0 + 4 * i, word)
        self.desc_write(DESC_ADDR, ram_byte_addr & 0xFFFF_FFFF)
        self.desc_write(DESC_KICK, half_sel)          # issues the AXI4 write
        status = self.desc_read(DESC_STATUS)
        return status is not None and (status & 0x1) == 1

    # ---- Cleanup ------------------------------------------------------------

    def close(self) -> None:
        if self._owns_bridge and self.bridge is not None:
            self.bridge.close()

    def __enter__(self):
        return self

    def __exit__(self, exc_type, exc_val, exc_tb):
        self.close()
