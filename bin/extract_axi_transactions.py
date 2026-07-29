#!/usr/bin/env python3
"""
AXI Transaction Extractor v2.2

Features:
1. Parse entire log into separate queues (AR/AW, R/W, B)
2. Match data beats to transactions in FIFO order
3. Assemble complete transactions with all beats
4. Extract and parse 256-bit descriptor fields with full field breakdown
5. Show id/user as decimal numbers for readability
6. Clean W beat output (no strb field in reports)

Usage:
    ./extract_axi_transactions.py <logfile> <rdeng|wreng> [--channel N]
    ./extract_axi_transactions.py <logfile> rdeng --interface descr  # Extract descriptors
"""

import sys
import re
import argparse
from collections import deque
from dataclasses import dataclass, field
from typing import List, Optional, Deque


@dataclass
class ARTransaction:
    """AXI Read Address Channel Transaction"""
    timestamp: float
    addr: str
    len: int
    size: int
    id: int
    # Data beats (filled during matching)
    r_beats: List['RBeat'] = field(default_factory=list)

    def is_complete(self) -> bool:
        """Check if all expected R beats received"""
        expected_beats = self.len + 1
        return len(self.r_beats) == expected_beats

    def __str__(self):
        return f"{self.timestamp:7.1f}: AR[id={self.id}] addr=0x{self.addr} len={self.len} size={self.size}"


@dataclass
class RBeat:
    """AXI Read Data Beat"""
    timestamp: float
    data: str
    last: bool
    id: int

    def __str__(self):
        last_marker = " LAST" if self.last else ""
        return f"{self.timestamp:7.1f}: R[id={self.id}] data=0x{self.data}{last_marker}"


@dataclass
class AWTransaction:
    """AXI Write Address Channel Transaction"""
    timestamp: float
    addr: str
    len: int
    size: int
    id: int
    # Data beats (filled during matching)
    w_beats: List['WBeat'] = field(default_factory=list)
    # Response (filled during matching)
    b_response: Optional['BResponse'] = None

    def is_complete(self) -> bool:
        """Check if all expected W beats received"""
        expected_beats = self.len + 1
        return len(self.w_beats) == expected_beats

    def __str__(self):
        return f"{self.timestamp:7.1f}: AW[id={self.id}] addr=0x{self.addr} len={self.len} size={self.size}"


@dataclass
class WBeat:
    """AXI Write Data Beat"""
    timestamp: float
    data: str
    last: bool
    strb: str
    user: int = 0  # USER field carries channel ID

    def __str__(self):
        last_marker = " LAST" if self.last else ""
        return f"{self.timestamp:7.1f}: W[user={self.user}] data=0x{self.data}{last_marker}"


@dataclass
class BResponse:
    """AXI Write Response"""
    timestamp: float
    id: int
    resp: str

    def __str__(self):
        return f"{self.timestamp:7.1f}: B[id={self.id}] resp={self.resp}"


@dataclass
class Descriptor:
    """256-bit STREAM Descriptor"""
    timestamp: float
    channel_id: int
    # Parsed fields from 256-bit descriptor
    src_addr: int       # bits[63:0]
    dst_addr: int       # bits[127:64]
    length: int         # bits[159:128]
    next_ptr: int       # bits[191:160]
    valid: bool         # bit[192]
    interrupt: bool     # bit[193]
    last: bool          # bit[194]
    error: bool         # bit[195]
    priority: int       # bits[207:200]
    reserved: int       # bits[255:208]

    @classmethod
    def from_r_beats(cls, r_beats: List[RBeat], timestamp: float, channel_id: int):
        """Parse 256-bit descriptor from 4x 64-bit R beats"""
        if len(r_beats) != 4:
            raise ValueError(f"Descriptor requires 4 R beats, got {len(r_beats)}")

        # Concatenate 4x 64-bit beats into 256-bit value (little-endian)
        # Beat 0 = bits[63:0], Beat 1 = bits[127:64], etc.
        desc_val = 0
        for i, beat in enumerate(r_beats):
            beat_val = int(beat.data, 16)
            desc_val |= (beat_val << (i * 64))

        # Extract fields
        return cls(
            timestamp=timestamp,
            channel_id=channel_id,
            src_addr=(desc_val >> 0) & ((1 << 64) - 1),
            dst_addr=(desc_val >> 64) & ((1 << 64) - 1),
            length=(desc_val >> 128) & ((1 << 32) - 1),
            next_ptr=(desc_val >> 160) & ((1 << 32) - 1),
            valid=bool((desc_val >> 192) & 1),
            interrupt=bool((desc_val >> 193) & 1),
            last=bool((desc_val >> 194) & 1),
            error=bool((desc_val >> 195) & 1),
            priority=(desc_val >> 200) & 0xFF,
            reserved=(desc_val >> 208) & ((1 << 48) - 1)
        )

    def __str__(self):
        return (f"    Timestamp:     {self.timestamp:7.1f} ns\n"
                f"    Channel ID:    {self.channel_id}\n"
                f"    Source Addr:   0x{self.src_addr:016x}\n"
                f"    Dest Addr:     0x{self.dst_addr:016x}\n"
                f"    Length:        {self.length} beats (0x{self.length:08x})\n"
                f"    Next Ptr:      0x{self.next_ptr:08x}\n"
                f"    Valid:         {self.valid}\n"
                f"    Interrupt:     {self.interrupt}\n"
                f"    Last:          {self.last}\n"
                f"    Error:         {self.error}\n"
                f"    Priority:      {self.priority} (0x{self.priority:02x})\n"
                f"    Reserved:      0x{self.reserved:012x}")


class AXITransactionExtractor:
    """
    Two-phase AXI transaction extraction:
    Phase 1: Parse log into separate queues
    Phase 2: Match data beats to address transactions
    """

    def __init__(self, logfile: str, engine_type: str, interface_filter: Optional[str] = None):
        self.logfile = logfile
        self.engine_type = engine_type.lower()
        self.interface_filter = interface_filter

        # Phase 1 storage: Raw parsed data
        self.ar_queue: Deque[ARTransaction] = deque()
        self.r_queue: Deque[RBeat] = deque()
        self.aw_queue: Deque[AWTransaction] = deque()
        self.w_queue: Deque[WBeat] = deque()
        self.b_queue: Deque[BResponse] = deque()

        # Phase 2 storage: Matched transactions by channel
        self.completed_read_transactions: dict[int, List[ARTransaction]] = {}
        self.completed_write_transactions: dict[int, List[AWTransaction]] = {}

        # Descriptor storage by channel
        self.descriptors: dict[int, List[Descriptor]] = {}

        # Compile regex patterns
        self.patterns = self._compile_patterns()

    def _compile_patterns(self):
        """Compile regex patterns for log parsing"""
        patterns = {}

        # AR: Read Address
        patterns['ar'] = re.compile(
            r'GAXIMonitorBase\(AR_.*Transaction at\s+(\d+\.\d+)ns:.*'
            r'size=(\d+).*len=\s*(\d+).*addr=0x([0-9A-Fa-f]+).*id=0x([0-9A-Fa-f]+)',
            re.IGNORECASE
        )

        # R: Read Data
        patterns['r_data'] = re.compile(
            r'Master\(R_Master.*Transaction.*at\s+(\d+\.\d+)ns:.*'
            r'last=(Last|Not Last).*data=0x([0-9A-Fa-f]+).*id=0x([0-9A-Fa-f]+)',
            re.IGNORECASE
        )

        # AW: Write Address
        patterns['aw'] = re.compile(
            r'GAXIMonitorBase\(AW_.*Transaction at\s+(\d+\.\d+)ns:.*'
            r'size=(\d+).*len=\s*(\d+).*addr=0x([0-9A-Fa-f]+).*id=0x([0-9A-Fa-f]+)',
            re.IGNORECASE
        )

        # W: Write Data (with optional user field for channel ID)
        patterns['w_data'] = re.compile(
            r'GAXIMonitorBase\(W_.*Transaction at\s+(\d+\.\d+)ns:.*'
            r'user=0[xb]([0-9A-Fa-f]+).*last=(Last|Not Last).*strb=0[xb]([0-9A-Fa-f]+).*data=0x([0-9A-Fa-f]+)',
            re.IGNORECASE
        )

        # B: Write Response
        patterns['b_resp'] = re.compile(
            r'Master\(B_Master.*Transaction.*@\s+(\d+\.\d+)ns:.*'
            r'resp=(\w+).*id=0x([0-9A-Fa-f]+)',
            re.IGNORECASE
        )

        return patterns

    def extract_transactions(self):
        """Phase 1: Parse entire log file into queues"""
        print(f"Phase 1: Parsing {self.logfile}...")

        with open(self.logfile, 'r') as f:
            for line in f:
                if self.engine_type == 'rdeng':
                    self._parse_read_line(line)
                elif self.engine_type == 'wreng':
                    self._parse_write_line(line)

        print(f"  AR transactions: {len(self.ar_queue)}")
        print(f"  R beats: {len(self.r_queue)}")
        print(f"  AW transactions: {len(self.aw_queue)}")
        print(f"  W beats: {len(self.w_queue)}")
        print(f"  B responses: {len(self.b_queue)}")

    def _parse_read_line(self, line: str):
        """Parse read engine line (AR, R)"""
        # Apply interface filter if specified
        if self.interface_filter and self.interface_filter not in line:
            return

        # Try AR pattern
        match = self.patterns['ar'].search(line)
        if match:
            timestamp, size, length, addr, id_hex = match.groups()
            ar = ARTransaction(
                timestamp=float(timestamp),
                addr=addr,
                len=int(length),
                size=int(size),
                id=int(id_hex, 16)
            )
            self.ar_queue.append(ar)
            return

        # Try R data pattern
        match = self.patterns['r_data'].search(line)
        if match:
            timestamp, last_str, data, id_hex = match.groups()
            r = RBeat(
                timestamp=float(timestamp),
                data=data,
                last=(last_str.lower() == 'last'),
                id=int(id_hex, 16)
            )
            self.r_queue.append(r)
            return

    def _parse_write_line(self, line: str):
        """Parse write engine line (AW, W, B)"""
        # Try AW pattern (with interface filter)
        match = self.patterns['aw'].search(line)
        if match:
            if self.interface_filter and self.interface_filter not in line:
                return

            timestamp, size, length, addr, id_hex = match.groups()
            aw = AWTransaction(
                timestamp=float(timestamp),
                addr=addr,
                len=int(length),
                size=int(size),
                id=int(id_hex, 16)
            )
            self.aw_queue.append(aw)
            return

        # Try W data pattern (no interface filter - W has no interface name)
        match = self.patterns['w_data'].search(line)
        if match:
            timestamp, user_hex, last_str, strb, data = match.groups()

            # Detect format from original line to parse correctly
            # Line contains either "user=0xN" or "user=0bN"
            user_match = re.search(r'user=(0[xb][0-9A-Fa-f]+)', line, re.IGNORECASE)
            if user_match:
                user_str = user_match.group(1)
                # Python's int() auto-detects 0x and 0b prefixes
                user_val = int(user_str, 0)  # base=0 means auto-detect from prefix
            else:
                # Fallback: assume hex if no prefix found
                user_val = int(user_hex, 16)

            w = WBeat(
                timestamp=float(timestamp),
                data=data,
                last=(last_str.lower() == 'last'),
                strb=strb,
                user=user_val  # Channel ID from USER field
            )
            self.w_queue.append(w)
            return

        # Try B response pattern (no interface filter)
        match = self.patterns['b_resp'].search(line)
        if match:
            timestamp, resp, id_hex = match.groups()
            b = BResponse(
                timestamp=float(timestamp),
                id=int(id_hex, 16),
                resp=resp
            )
            self.b_queue.append(b)
            return

    def match_read_transactions(self):
        """
        Phase 2: Match R beats to AR transactions

        Algorithm:
        1. For each R beat (in order):
        2. Find first incomplete AR transaction with matching ID
        3. Add R beat to that transaction
        4. When transaction complete, move to completed list
        """
        print(f"\nPhase 2: Matching R beats to AR transactions...")

        # Working list of AR transactions (FIFO order for each ID)
        pending_ar: dict[int, Deque[ARTransaction]] = {}

        # Populate pending AR transactions
        for ar in self.ar_queue:
            if ar.id not in pending_ar:
                pending_ar[ar.id] = deque()
            pending_ar[ar.id].append(ar)

        # Match R beats to AR transactions
        matched_count = 0
        unmatched_count = 0

        for r_beat in self.r_queue:
            r_id = r_beat.id

            # Find first incomplete AR transaction with this ID
            if r_id in pending_ar and pending_ar[r_id]:
                ar_txn = pending_ar[r_id][0]  # FIFO: always first in queue
                ar_txn.r_beats.append(r_beat)
                matched_count += 1

                # If transaction complete, move to completed list
                if ar_txn.is_complete():
                    pending_ar[r_id].popleft()  # Remove from pending
                    if r_id not in self.completed_read_transactions:
                        self.completed_read_transactions[r_id] = []
                    self.completed_read_transactions[r_id].append(ar_txn)
            else:
                unmatched_count += 1
                print(f"  WARNING: R beat at {r_beat.timestamp}ns has no matching AR (id={r_id})")

        # Check for incomplete transactions
        for ch_id, ar_list in pending_ar.items():
            for ar_txn in ar_list:
                if not ar_txn.is_complete():
                    expected = ar_txn.len + 1
                    actual = len(ar_txn.r_beats)
                    print(f"  WARNING: AR[id={ch_id}] addr=0x{ar_txn.addr} incomplete: "
                          f"{actual}/{expected} beats")

        print(f"  Matched {matched_count} R beats")
        print(f"  Unmatched {unmatched_count} R beats")
        print(f"  Completed transactions: {sum(len(v) for v in self.completed_read_transactions.values())}")

    def extract_descriptors(self):
        """
        Extract and parse descriptor fields from completed read transactions.
        Descriptor format: 256-bit (single 256-bit R beat OR 4x 64-bit R beats)
        """
        print(f"\nPhase 3: Extracting descriptor fields...")

        descriptor_count = 0

        for ch_id, ar_transactions in self.completed_read_transactions.items():
            if ch_id not in self.descriptors:
                self.descriptors[ch_id] = []

            for ar_txn in ar_transactions:
                # Check if this is a descriptor fetch
                # Case 1: Single 256-bit beat (len=0, size=6 with 256-bit data)
                # Case 2: Four 64-bit beats (len=3, size=3)
                if len(ar_txn.r_beats) == 1:
                    # Single beat - check if data is 256 bits (64 hex chars)
                    r_beat = ar_txn.r_beats[0]
                    if len(r_beat.data) == 64:  # 256 bits = 64 hex chars
                        try:
                            # Parse as single 256-bit value
                            desc_val = int(r_beat.data, 16)
                            desc = Descriptor(
                                timestamp=ar_txn.timestamp,
                                channel_id=ch_id,
                                src_addr=(desc_val >> 0) & ((1 << 64) - 1),
                                dst_addr=(desc_val >> 64) & ((1 << 64) - 1),
                                length=(desc_val >> 128) & ((1 << 32) - 1),
                                next_ptr=(desc_val >> 160) & ((1 << 32) - 1),
                                valid=bool((desc_val >> 192) & 1),
                                interrupt=bool((desc_val >> 193) & 1),
                                last=bool((desc_val >> 194) & 1),
                                error=bool((desc_val >> 195) & 1),
                                priority=(desc_val >> 200) & 0xFF,
                                reserved=(desc_val >> 208) & ((1 << 48) - 1)
                            )
                            self.descriptors[ch_id].append(desc)
                            descriptor_count += 1
                        except Exception as e:
                            print(f"  WARNING: Failed to parse single-beat descriptor at {ar_txn.timestamp}ns: {e}")
                elif len(ar_txn.r_beats) == 4:
                    # Four 64-bit beats
                    try:
                        desc = Descriptor.from_r_beats(
                            r_beats=ar_txn.r_beats,
                            timestamp=ar_txn.timestamp,
                            channel_id=ch_id
                        )
                        self.descriptors[ch_id].append(desc)
                        descriptor_count += 1
                    except Exception as e:
                        print(f"  WARNING: Failed to parse multi-beat descriptor at {ar_txn.timestamp}ns: {e}")

        print(f"  Extracted {descriptor_count} descriptors across {len(self.descriptors)} channels")
        for ch_id in sorted(self.descriptors.keys()):
            print(f"    Channel {ch_id}: {len(self.descriptors[ch_id])} descriptors")

    def match_write_transactions(self):
        """
        Phase 2: Match W beats and B responses to AW transactions

        Algorithm (USER-based channel separation):
        1. Separate W beats into per-channel lists by USER field
        2. Separate AW transactions into per-channel lists by ID field
        3. For each channel, match W beats to AW in FIFO order using wlast
        4. Match B responses by ID (may be out of order)
        """
        print(f"\nPhase 2: Matching W beats and B responses to AW transactions...")

        # Step 1: Separate W beats by channel (USER field)
        w_beats_by_channel: dict[int, list[WBeat]] = {}
        for w_beat in self.w_queue:
            ch_id = w_beat.user
            if ch_id not in w_beats_by_channel:
                w_beats_by_channel[ch_id] = []
            w_beats_by_channel[ch_id].append(w_beat)

        # Step 2: Separate AW transactions by channel (ID field)
        aw_by_channel: dict[int, list[AWTransaction]] = {}
        for aw in self.aw_queue:
            ch_id = aw.id
            if ch_id not in aw_by_channel:
                aw_by_channel[ch_id] = []
            aw_by_channel[ch_id].append(aw)

        # Debug: Show organization
        print(f"  DEBUG: Organized by channel:")
        for ch_id in sorted(aw_by_channel.keys()):
            w_count = len(w_beats_by_channel.get(ch_id, []))
            aw_count = len(aw_by_channel[ch_id])
            print(f"    Channel {ch_id}: {aw_count} AW transactions, {w_count} W beats")

        # Step 3: Match W beats to AW for each channel separately
        matched_w_count = 0
        unmatched_w_count = 0

        for ch_id in sorted(aw_by_channel.keys()):
            aw_list = aw_by_channel[ch_id]
            w_list = w_beats_by_channel.get(ch_id, [])

            aw_idx = 0
            w_idx = 0

            while w_idx < len(w_list) and aw_idx < len(aw_list):
                w_beat = w_list[w_idx]
                aw_txn = aw_list[aw_idx]

                # Append W beat to current AW transaction
                aw_txn.w_beats.append(w_beat)
                matched_w_count += 1
                w_idx += 1

                # Move to next AW when we see wlast
                if w_beat.last:
                    aw_idx += 1

            # Report any unmatched W beats for this channel
            if w_idx < len(w_list):
                unmatched_w_count += len(w_list) - w_idx
                print(f"  WARNING: Channel {ch_id} has {len(w_list) - w_idx} unmatched W beats")

        # Flatten back to single list for compatibility
        pending_aw = []
        for ch_id in sorted(aw_by_channel.keys()):
            pending_aw.extend(aw_by_channel[ch_id])

        # Match B responses by ID (can be out of order)
        matched_b_count = 0
        unmatched_b_count = 0

        for b_resp in self.b_queue:
            b_id = b_resp.id

            # Find AW transaction with this ID that needs a B response
            matched = False
            for aw_txn in pending_aw:
                if aw_txn.id == b_id and aw_txn.b_response is None:
                    aw_txn.b_response = b_resp
                    matched_b_count += 1
                    matched = True
                    break

            if not matched:
                unmatched_b_count += 1
                print(f"  WARNING: B response at {b_resp.timestamp}ns has no matching AW (id={b_id})")

        # Move completed transactions to final list
        for aw_txn in pending_aw:
            ch_id = aw_txn.id
            if ch_id not in self.completed_write_transactions:
                self.completed_write_transactions[ch_id] = []
            self.completed_write_transactions[ch_id].append(aw_txn)

            # Warn if incomplete
            if not aw_txn.is_complete():
                expected = aw_txn.len + 1
                actual = len(aw_txn.w_beats)
                print(f"  WARNING: AW[id={ch_id}] addr=0x{aw_txn.addr} incomplete: "
                      f"{actual}/{expected} W beats")
            if aw_txn.b_response is None:
                print(f"  WARNING: AW[id={ch_id}] addr=0x{aw_txn.addr} has no B response")

        print(f"  Matched {matched_w_count} W beats")
        print(f"  Unmatched {unmatched_w_count} W beats")
        print(f"  Matched {matched_b_count} B responses")
        print(f"  Unmatched {unmatched_b_count} B responses")
        print(f"  Completed transactions: {len(pending_aw)}")

    def print_report(self, channel_filter: Optional[int] = None, output_file: Optional[str] = None):
        """Print formatted report of transactions"""

        # Determine output stream
        if output_file:
            f = open(output_file, 'w')
        else:
            f = sys.stdout

        try:
            f.write("=" * 100 + "\n")
            f.write(f"AXI {self.engine_type.upper()} Transaction Report\n")
            f.write(f"Log file: {self.logfile}\n")
            f.write("=" * 100 + "\n")

            if self.engine_type == 'rdeng':
                self._print_read_report(f, channel_filter)
            else:
                self._print_write_report(f, channel_filter)

        finally:
            if output_file:
                f.close()

    def _print_read_report(self, f, channel_filter):
        """Print read transaction report"""
        channels = sorted(self.completed_read_transactions.keys())
        if channel_filter is not None:
            channels = [ch for ch in channels if ch == channel_filter]

        for ch_id in channels:
            transactions = self.completed_read_transactions[ch_id]
            descriptors = self.descriptors.get(ch_id, [])

            f.write("\n\n")
            f.write("=" * 100 + "\n")
            f.write(f"CHANNEL {ch_id}\n")
            f.write("=" * 100 + "\n")

            # Print descriptors first (if available)
            if descriptors:
                f.write("\n" + "=" * 100 + "\n")
                f.write(f"DESCRIPTORS ({len(descriptors)})\n")
                f.write("=" * 100 + "\n")
                for desc_num, desc in enumerate(descriptors, start=1):
                    f.write(f"\nDescriptor {desc_num}:\n")
                    f.write(f"{desc}\n")

            # Group transactions into descriptors using descriptor length info
            descriptor_groups = self._group_by_descriptor(transactions, descriptors)

            # Print each descriptor group
            for desc_num, desc_transactions in enumerate(descriptor_groups, start=1):
                f.write("\n")
                f.write("-" * 100 + "\n")
                f.write(f"DESCRIPTOR {desc_num} - AXI TRANSACTIONS\n")
                f.write("-" * 100 + "\n")

                # AR transactions
                f.write(f"\nAR Transactions ({len(desc_transactions)}):\n")
                for ar in desc_transactions:
                    f.write(f"  {ar}\n")

                # R data beats
                total_r_beats = sum(len(ar.r_beats) for ar in desc_transactions)
                f.write(f"\nR Data Beats ({total_r_beats}):\n")

                burst_num = 0
                for ar in desc_transactions:
                    burst_num += 1
                    for beat_num, r_beat in enumerate(ar.r_beats, 1):
                        f.write(f"  Burst {burst_num:4d}, Beat {beat_num:2d}: {r_beat}\n")

    def _print_write_report(self, f, channel_filter):
        """Print write transaction report"""
        channels = sorted(self.completed_write_transactions.keys())
        if channel_filter is not None:
            channels = [ch for ch in channels if ch == channel_filter]

        for ch_id in channels:
            transactions = self.completed_write_transactions[ch_id]
            descriptors = self.descriptors.get(ch_id, [])

            f.write("\n\n")
            f.write("=" * 100 + "\n")
            f.write(f"CHANNEL {ch_id}\n")
            f.write("=" * 100 + "\n")

            # Print descriptors first (if available)
            if descriptors:
                f.write("\n" + "=" * 100 + "\n")
                f.write(f"DESCRIPTORS ({len(descriptors)})\n")
                f.write("=" * 100 + "\n")
                for desc_num, desc in enumerate(descriptors, start=1):
                    f.write(f"\nDescriptor {desc_num}:\n")
                    f.write(f"{desc}\n")

            # Group transactions into descriptors using descriptor length info
            descriptor_groups = self._group_by_descriptor(transactions, descriptors)

            # Print each descriptor group
            for desc_num, desc_transactions in enumerate(descriptor_groups, start=1):
                f.write("\n")
                f.write("-" * 100 + "\n")
                f.write(f"DESCRIPTOR {desc_num} - AXI TRANSACTIONS\n")
                f.write("-" * 100 + "\n")

                # AW transactions
                f.write(f"\nAW Transactions ({len(desc_transactions)}):\n")
                for aw in desc_transactions:
                    f.write(f"  {aw}\n")

                # W data beats
                total_w_beats = sum(len(aw.w_beats) for aw in desc_transactions)
                f.write(f"\nW Data Beats ({total_w_beats}):\n")

                burst_num = 0
                for aw in desc_transactions:
                    burst_num += 1
                    for beat_num, w_beat in enumerate(aw.w_beats, 1):
                        f.write(f"  Burst {burst_num:4d}, Beat {beat_num:2d}: {w_beat}\n")

                # B responses
                f.write(f"\nB Responses ({len(desc_transactions)}):\n")
                for aw in desc_transactions:
                    if aw.b_response:
                        f.write(f"  {aw.b_response}\n")

    def _group_by_descriptor(self, transactions, descriptors) -> List:
        """
        Group AR/AW transactions into descriptors using descriptor length information.

        For asymmetric bursts (rd_burst != wr_burst), the number of transactions
        per descriptor varies based on burst size:
        - Descriptor length = total beats (from descriptor.length field)
        - Read: length ÷ rd_burst = number of AR transactions
        - Write: length ÷ wr_burst = number of AW transactions

        Example for rd16/wr8 with 6 descriptors of 64 beats each:
        - Descriptor 1: 64 beats → 4 AR transactions (64÷16), 8 AW transactions (64÷8)
        - Descriptor 2: 64 beats → 4 AR transactions, 8 AW transactions
        - ...

        Args:
            transactions: List of AR or AW transactions
            descriptors: List of descriptor objects with length field

        Returns:
            List of transaction groups, one per descriptor
        """
        if not transactions:
            return []

        # If no descriptor info available, fall back to showing all transactions
        if not descriptors:
            return [transactions]

        descriptor_groups = []
        txn_idx = 0

        # Group transactions based on descriptor lengths
        for desc in descriptors:
            desc_length = desc.length  # Total beats for this descriptor
            current_group = []
            accumulated_beats = 0

            # Accumulate transactions until we've seen desc_length beats
            while txn_idx < len(transactions) and accumulated_beats < desc_length:
                txn = transactions[txn_idx]
                txn_beats = txn.len + 1  # AXI len field: 0=1 beat, 1=2 beats, etc.
                current_group.append(txn)
                accumulated_beats += txn_beats
                txn_idx += 1

            descriptor_groups.append(current_group)

        # Handle any remaining transactions (shouldn't happen in well-formed tests)
        if txn_idx < len(transactions):
            remaining = transactions[txn_idx:]
            descriptor_groups.append(remaining)

        return descriptor_groups


def main():
    parser = argparse.ArgumentParser(
        description='Extract and group AXI transactions from CocoTB log files (v2.0)',
        formatter_class=argparse.RawDescriptionHelpFormatter,
        epilog="""
Examples:
  %(prog)s logs/test.log rdeng
  %(prog)s logs/test.log wreng --channel 1
  %(prog)s logs/test.log rdeng --output ar_transactions.txt
        """
    )

    parser.add_argument('logfile', help='Path to CocoTB log file')
    parser.add_argument('engine', choices=['rdeng', 'wreng'],
                       help='Engine type: rdeng (read) or wreng (write)')
    parser.add_argument('--channel', type=int, metavar='N',
                       help='Filter to show only specific channel')
    parser.add_argument('--interface', '-i', metavar='NAME',
                       help='Filter to specific interface (e.g., rdeng, wreng, descr)')
    parser.add_argument('--output', '-o', metavar='FILE',
                       help='Write report to file instead of stdout')

    args = parser.parse_args()

    # Use --interface if specified, otherwise use engine type as filter
    interface_filter = args.interface if args.interface else args.engine

    # Create extractor
    extractor = AXITransactionExtractor(
        logfile=args.logfile,
        engine_type=args.engine,
        interface_filter=interface_filter
    )

    # Phase 1: Parse log
    extractor.extract_transactions()

    # Phase 2: Match transactions
    if args.engine == 'rdeng':
        extractor.match_read_transactions()
    else:
        extractor.match_write_transactions()

    # Phase 3: Extract descriptor fields for all engine types
    # Parse descriptor transactions separately to show in reports
    saved_filter = extractor.interface_filter
    saved_ar_queue = list(extractor.ar_queue)
    saved_r_queue = list(extractor.r_queue)
    saved_completed = dict(extractor.completed_read_transactions)

    extractor.interface_filter = 'descr'  # Look for descriptor interface
    extractor.ar_queue.clear()
    extractor.r_queue.clear()
    extractor.completed_read_transactions.clear()

    # Re-parse log to get descriptor transactions
    with open(args.logfile, 'r') as f:
        for line in f:
            extractor._parse_read_line(line)

    # Match descriptor transactions
    pending_ar = {}
    for ar in extractor.ar_queue:
        if ar.id not in pending_ar:
            pending_ar[ar.id] = []
        pending_ar[ar.id].append(ar)

    for r_beat in extractor.r_queue:
        if r_beat.id in pending_ar and pending_ar[r_beat.id]:
            ar_txn = pending_ar[r_beat.id][0]
            ar_txn.r_beats.append(r_beat)
            if ar_txn.is_complete():
                pending_ar[r_beat.id].pop(0)
                if r_beat.id not in extractor.completed_read_transactions:
                    extractor.completed_read_transactions[r_beat.id] = []
                extractor.completed_read_transactions[r_beat.id].append(ar_txn)

    # Extract descriptors
    extractor.extract_descriptors()

    # Restore original queues and filter
    extractor.interface_filter = saved_filter
    extractor.ar_queue = saved_ar_queue
    extractor.r_queue = saved_r_queue
    if args.engine == 'rdeng':
        extractor.completed_read_transactions = saved_completed

    # Print report
    extractor.print_report(channel_filter=args.channel, output_file=args.output)


if __name__ == '__main__':
    main()
