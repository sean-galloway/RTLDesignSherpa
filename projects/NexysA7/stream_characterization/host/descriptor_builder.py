#!/usr/bin/env python3
"""
descriptor_builder.py - Build STREAM descriptor chains for characterization

Pure-data module: no I/O, no serial ports, no cocotb. Produces lists of
(address, data) tuples that any transport layer (UART bridge, CocoTB TB,
or Vivado ILA) can consume.

STREAM descriptor format (256 bits = 8 x 32-bit words):
  Word 0: src_addr[31:0]
  Word 1: src_addr[63:32]
  Word 2: dst_addr[31:0]
  Word 3: dst_addr[63:32]
  Word 4: length[31:0]         (in BEATS, not bytes)
  Word 5: next_descriptor_ptr[31:0]  (AXI4-side byte address in desc_ram)
  Word 6: control flags
           [0]   valid
           [1]   last           (1 = end of chain)
           [2]   interrupt      (1 = generate IRQ on completion)
           [7:4] channel_id
  Word 7: reserved (0)

Descriptor placement in desc_ram:
  - 2048 entries max (DEPTH_256=2048, 64 KB)
  - Channel C, descriptor D → index = C * MAX_DESC_PER_CH + D
  - AXI4-side address = index * 32
  - Host AXIL address = DESC_RAM_BASE + index * 32

Usage:
    from descriptor_builder import DescriptorBuilder

    builder = DescriptorBuilder(data_width=128)
    writes = builder.build_chain(
        channel=0,
        num_descriptors=4,
        transfer_bytes=1024*1024,   # 1 MB per descriptor
    )
    # writes is a list of (host_axil_addr, 32bit_data) tuples
    for addr, data in writes:
        bridge.write(addr, data)
"""

from dataclasses import dataclass
from typing import List, Tuple

# Memory map (must match stream_char_harness)
DESC_RAM_BASE       = 0x0002_0000
HARNESS_CSR_BASE    = 0x0001_0000
STREAM_APB_BASE     = 0x0000_0000

# Descriptor field offsets (word index within 256-bit descriptor)
_W_SRC_LO   = 0
_W_SRC_HI   = 1
_W_DST_LO   = 2
_W_DST_HI   = 3
_W_LENGTH   = 4
_W_NEXT_PTR = 5
_W_CONTROL  = 6
_W_RESERVED = 7

# Control flag bits
CTRL_VALID     = 1 << 0
CTRL_LAST      = 1 << 1
CTRL_INTERRUPT = 1 << 2

# Max descriptors per channel (layout constant — not an RTL limit)
MAX_DESC_PER_CH = 32

# Descriptor index offset: STREAM's descriptor_engine rejects AXI4
# address 0 as invalid (apb_addr != 0 check). Start at index 1 so the
# first descriptor lives at AXI4 address 0x20 (32 bytes), not 0x00.
DESC_INDEX_OFFSET = 1


@dataclass
class DescriptorConfig:
    """Configuration for a single descriptor."""
    src_addr: int
    dst_addr: int
    length_beats: int
    next_ptr: int       # AXI4-side byte address of next descriptor (0 = end)
    channel_id: int
    is_last: bool
    interrupt: bool = True


@dataclass
class CharConfig:
    """A single characterization test configuration."""
    name: str
    num_channels: int           # 1..8
    descriptors_per_channel: int  # 1..16
    transfer_bytes: int         # bytes per descriptor transfer


class DescriptorBuilder:
    """
    Builds descriptor chains and AXIL write sequences for STREAM
    characterization.

    Args:
        data_width: STREAM DATA_WIDTH in bits (default 128)
        src_base: Base source address (arbitrary — pattern_gen ignores it)
        dst_base: Base destination address (arbitrary — crc_check ignores it)
    """

    def __init__(self, data_width: int = 128,
                 src_base: int = 0x8000_0000,
                 dst_base: int = 0x9000_0000):
        self.bytes_per_beat = data_width // 8
        self.src_base = src_base
        self.dst_base = dst_base

    def _desc_index(self, channel: int, desc_idx: int) -> int:
        """Flat index in desc_ram for (channel, descriptor).
        Offset by DESC_INDEX_OFFSET so no descriptor lands at AXI4 address 0
        (STREAM's descriptor_engine treats address 0 as invalid)."""
        return DESC_INDEX_OFFSET + channel * MAX_DESC_PER_CH + desc_idx

    def _axi4_addr(self, index: int) -> int:
        """AXI4-side byte address for a descriptor index."""
        return index * 32

    def _host_addr(self, index: int, word: int) -> int:
        """Host AXIL byte address for word `word` of descriptor `index`."""
        return DESC_RAM_BASE + index * 32 + word * 4

    def beats_for_bytes(self, nbytes: int) -> int:
        """Convert byte count to beat count."""
        return nbytes // self.bytes_per_beat

    # -----------------------------------------------------------------
    # Build a descriptor chain for one channel
    # -----------------------------------------------------------------

    def build_chain(self, channel: int, num_descriptors: int,
                    transfer_bytes: int) -> List[Tuple[int, int]]:
        """
        Build AXIL write list for a chained descriptor sequence on one channel.

        Args:
            channel: Channel ID (0..7)
            num_descriptors: Number of descriptors in the chain (1..MAX_DESC_PER_CH)
            transfer_bytes: Bytes per descriptor transfer

        Returns:
            List of (host_axil_address, 32bit_data) tuples to write via UART.
        """
        beats = self.beats_for_bytes(transfer_bytes)
        writes: List[Tuple[int, int]] = []

        for d in range(num_descriptors):
            idx = self._desc_index(channel, d)
            is_last = (d == num_descriptors - 1)

            # Source/dest addresses: offset per descriptor so each transfer
            # is nominally to a different region (pattern_gen/crc_check don't
            # care, but it's more realistic).
            src = self.src_base + d * transfer_bytes
            dst = self.dst_base + d * transfer_bytes

            # Next pointer: AXI4-side address of the next descriptor
            if is_last:
                next_ptr = 0
            else:
                next_idx = self._desc_index(channel, d + 1)
                next_ptr = self._axi4_addr(next_idx)

            # Control word
            ctrl = CTRL_VALID
            if is_last:
                ctrl |= CTRL_LAST | CTRL_INTERRUPT
            ctrl |= (channel & 0xF) << 4

            # Build the 8 word writes
            words = [
                src & 0xFFFF_FFFF,
                (src >> 32) & 0xFFFF_FFFF,
                dst & 0xFFFF_FFFF,
                (dst >> 32) & 0xFFFF_FFFF,
                beats & 0xFFFF_FFFF,
                next_ptr & 0xFFFF_FFFF,
                ctrl & 0xFFFF_FFFF,
                0x0000_0000,
            ]

            for w, val in enumerate(words):
                writes.append((self._host_addr(idx, w), val))

        return writes

    def kick_address(self, channel: int) -> int:
        """
        AXI4-side byte address of the first descriptor for this channel.
        This is what software writes to the APB kick-off register.
        """
        return self._axi4_addr(self._desc_index(channel, 0))

    # -----------------------------------------------------------------
    # Build a full multi-channel test
    # -----------------------------------------------------------------

    def build_test(self, config: CharConfig) -> dict:
        """
        Build everything needed for one characterization run.

        Returns dict with:
            'descriptor_writes': list of (addr, data) for all channels
            'kick_addresses':    dict {channel: axi4_start_addr}
            'config':            the CharConfig
            'total_descriptors': total descriptor count across all channels
            'total_bytes':       total transfer bytes across all channels
        """
        all_writes: List[Tuple[int, int]] = []
        kick_addrs = {}

        for ch in range(config.num_channels):
            chain = self.build_chain(
                channel=ch,
                num_descriptors=config.descriptors_per_channel,
                transfer_bytes=config.transfer_bytes,
            )
            all_writes.extend(chain)
            kick_addrs[ch] = self.kick_address(ch)

        total_desc = config.num_channels * config.descriptors_per_channel
        total_bytes = total_desc * config.transfer_bytes

        return {
            'descriptor_writes': all_writes,
            'kick_addresses': kick_addrs,
            'config': config,
            'total_descriptors': total_desc,
            'total_bytes': total_bytes,
        }


# =====================================================================
# Characterization test matrix
# =====================================================================

def build_char_matrix(transfer_bytes: int = 1024 * 1024) -> List[CharConfig]:
    """
    Build the full 40-configuration characterization matrix.

    Phase 1: 1 descriptor/channel, 1..8 channels  (8 configs)
    Phase 2: {2,4,8,16} desc/ch, 1..8 channels    (32 configs)

    Args:
        transfer_bytes: Bytes per descriptor transfer (default 1 MB).
                        Pass e.g. 4096 for quick smoke tests or
                        4*1024*1024 for 4 MB stress runs.

    Returns:
        List of 40 CharConfig objects.
    """
    size_label = _size_label(transfer_bytes)
    configs = []

    # Phase 1: single descriptor per channel
    for num_ch in range(1, 9):
        configs.append(CharConfig(
            name=f"1desc_{num_ch}ch_{size_label}",
            num_channels=num_ch,
            descriptors_per_channel=1,
            transfer_bytes=transfer_bytes,
        ))

    # Phase 2: multiple descriptors per channel
    for num_desc in [2, 4, 8, 16]:
        for num_ch in range(1, 9):
            configs.append(CharConfig(
                name=f"{num_desc}desc_{num_ch}ch_{size_label}",
                num_channels=num_ch,
                descriptors_per_channel=num_desc,
                transfer_bytes=transfer_bytes,
            ))

    return configs


def _size_label(nbytes: int) -> str:
    """Human-readable label for a byte count (e.g. '1MB', '4KB')."""
    if nbytes >= 1024 * 1024 and nbytes % (1024 * 1024) == 0:
        return f"{nbytes // (1024 * 1024)}MB"
    elif nbytes >= 1024 and nbytes % 1024 == 0:
        return f"{nbytes // 1024}KB"
    else:
        return f"{nbytes}B"


def _parse_size(s: str) -> int:
    """Parse a human-readable size string to bytes (e.g., '4KB' -> 4096)."""
    s = s.strip().upper()
    if s.endswith('MB'):
        return int(s[:-2]) * 1024 * 1024
    elif s.endswith('KB'):
        return int(s[:-2]) * 1024
    elif s.endswith('B'):
        return int(s[:-1])
    else:
        return int(s)


def load_configs_from_csv(csv_path: str) -> List[CharConfig]:
    """
    Load test configurations from a CSV file.

    Lines starting with '#' are skipped (comments). This makes it easy
    to comment out tests during bring-up and uncomment them later.

    Format: name, num_channels, descriptors_per_channel, transfer_bytes
    transfer_bytes supports suffixes: KB, MB (e.g., 8KB, 1MB, 4MB)

    Args:
        csv_path: Path to the CSV file.

    Returns:
        List of CharConfig objects for non-commented lines.
    """
    configs = []
    with open(csv_path, 'r') as f:
        for lineno, raw in enumerate(f, 1):
            line = raw.strip()
            if not line or line.startswith('#'):
                continue
            parts = [p.strip() for p in line.split(',')]
            if len(parts) != 4:
                raise ValueError(
                    f"{csv_path}:{lineno}: expected 4 columns, got {len(parts)}: {line!r}")
            name = parts[0]
            num_ch = int(parts[1])
            desc_per_ch = int(parts[2])
            xfer_bytes = _parse_size(parts[3])
            configs.append(CharConfig(
                name=name,
                num_channels=num_ch,
                descriptors_per_channel=desc_per_ch,
                transfer_bytes=xfer_bytes,
            ))
    return configs


# =====================================================================
# Quick self-test / preview
# =====================================================================

if __name__ == '__main__':
    import argparse
    ap = argparse.ArgumentParser(description="Preview characterization matrix")
    ap.add_argument('--size', type=str, default='1MB',
                    help='Transfer size per descriptor (e.g., 4KB, 1MB, default 1MB)')
    cli = ap.parse_args()

    # Parse size string
    s = cli.size.strip().upper()
    if s.endswith('MB'):
        xfer_bytes = int(s[:-2]) * 1024 * 1024
    elif s.endswith('KB'):
        xfer_bytes = int(s[:-2]) * 1024
    elif s.endswith('B'):
        xfer_bytes = int(s[:-1])
    else:
        xfer_bytes = int(s)

    builder = DescriptorBuilder(data_width=128)
    matrix = build_char_matrix(transfer_bytes=xfer_bytes)

    print(f"Characterization matrix: {len(matrix)} configurations "
          f"(transfer_bytes={xfer_bytes}, {_size_label(xfer_bytes)})\n")
    print(f"{'Name':<28} {'Channels':>8} {'Desc/Ch':>8} {'Total Desc':>10} "
          f"{'Total Data':>12} {'UART Writes':>12}")
    print("-" * 88)

    for cfg in matrix:
        test = builder.build_test(cfg)
        total_label = _size_label(test['total_bytes'])
        print(f"{cfg.name:<28} {cfg.num_channels:>8} "
              f"{cfg.descriptors_per_channel:>8} "
              f"{test['total_descriptors']:>10} "
              f"{total_label:>12} "
              f"{len(test['descriptor_writes']):>12}")

    # Show first config in detail
    print(f"\nDetail for '{matrix[0].name}':")
    test = builder.build_test(matrix[0])
    for addr, data in test['descriptor_writes']:
        print(f"  W {addr:08X} {data:08X}")
    print(f"  Kick channel 0 at AXI4 address: 0x{test['kick_addresses'][0]:08X}")
