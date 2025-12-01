# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2025 sean galloway
#
# RTL Design Sherpa - Industry-Standard RTL Design and Verification
# https://github.com/sean-galloway/RTLDesignSherpa
#
# Module: smbus_packet
# Purpose: SMBus Packet dataclass for transaction representation
#
# Documentation: projects/components/retro_legacy_blocks/rtl/smbus/README.md
# Subsystem: CocoTBFramework/components/smbus
#
# Created: 2025-11-29

"""
SMBus Packet Dataclass

Represents SMBus/I2C transactions for verification purposes.
Supports all SMBus 2.0 transaction types including:
- Quick Command
- Send/Receive Byte
- Write/Read Byte Data
- Write/Read Word Data
- Block Write/Read
- Block Process Call
"""

from dataclasses import dataclass, field
from typing import Optional, List
from enum import IntEnum


class SMBusTransactionType(IntEnum):
    """SMBus 2.0 Transaction Types"""
    QUICK_CMD = 0       # 0 bytes
    SEND_BYTE = 1       # 1 byte, no command
    RECV_BYTE = 2       # 1 byte, no command
    WRITE_BYTE = 3      # 1 cmd + 1 data
    READ_BYTE = 4       # 1 cmd + 1 data
    WRITE_WORD = 5      # 1 cmd + 2 data
    READ_WORD = 6       # 1 cmd + 2 data
    BLOCK_WRITE = 7     # 1 cmd + count + data
    BLOCK_READ = 8      # 1 cmd + count + data
    BLOCK_PROC = 9      # Block write-read


class SMBusCondition(IntEnum):
    """SMBus Bus Conditions"""
    IDLE = 0
    START = 1
    STOP = 2
    REPEATED_START = 3
    ACK = 4
    NAK = 5


@dataclass
class SMBusPacket:
    """
    SMBus Transaction Packet

    Represents a complete SMBus transaction including address, command,
    data, and protocol information.

    Attributes:
        start_time: Simulation time when transaction started (ns)
        end_time: Simulation time when transaction completed (ns)
        trans_type: SMBus transaction type
        slave_addr: 7-bit slave address
        read_write: Read (1) or Write (0) operation
        command: Command byte (for byte/word/block transactions)
        data: Data bytes (list for block transfers)
        byte_count: Number of data bytes (for block transfers)
        pec: Packet Error Checking byte (CRC-8)
        pec_valid: True if PEC was verified correct
        pec_enabled: True if PEC was used in this transaction
        ack_received: True if slave acknowledged address
        completed: True if transaction completed normally
        timeout: True if transaction timed out
        arbitration_lost: True if arbitration was lost
        direction: 'TX' for master transmit, 'RX' for master receive
    """
    # Timing information
    start_time: float = 0.0
    end_time: float = 0.0

    # Transaction type
    trans_type: SMBusTransactionType = SMBusTransactionType.QUICK_CMD

    # Address and direction
    slave_addr: int = 0         # 7-bit address (0x00-0x7F)
    read_write: int = 0         # 0=write, 1=read

    # Command and data
    command: int = 0            # Command byte
    data: List[int] = field(default_factory=list)  # Data bytes
    byte_count: int = 0         # Block transfer count

    # PEC (Packet Error Checking)
    pec: int = 0                # CRC-8 value
    pec_valid: bool = True      # PEC verification result
    pec_enabled: bool = False   # Was PEC used?

    # Status flags
    ack_received: bool = True   # Address acknowledged
    completed: bool = True      # Transaction completed normally
    timeout: bool = False       # Timeout occurred
    arbitration_lost: bool = False  # Lost arbitration

    # Direction for logging
    direction: str = 'TX'       # TX=master transmit, RX=master receive

    def formatted(self, compact: bool = True) -> str:
        """
        Format packet for display.

        Args:
            compact: If True, use single-line format; otherwise multi-line

        Returns:
            Formatted string representation
        """
        trans_names = {
            SMBusTransactionType.QUICK_CMD: "QuickCmd",
            SMBusTransactionType.SEND_BYTE: "SendByte",
            SMBusTransactionType.RECV_BYTE: "RecvByte",
            SMBusTransactionType.WRITE_BYTE: "WriteByte",
            SMBusTransactionType.READ_BYTE: "ReadByte",
            SMBusTransactionType.WRITE_WORD: "WriteWord",
            SMBusTransactionType.READ_WORD: "ReadWord",
            SMBusTransactionType.BLOCK_WRITE: "BlockWrite",
            SMBusTransactionType.BLOCK_READ: "BlockRead",
            SMBusTransactionType.BLOCK_PROC: "BlockProc",
        }

        trans_name = trans_names.get(self.trans_type, f"Unknown({self.trans_type})")
        rw_str = "R" if self.read_write else "W"
        addr_str = f"0x{self.slave_addr:02X}"

        # Build data string
        if self.data:
            if len(self.data) <= 4:
                data_str = " ".join(f"{b:02X}" for b in self.data)
            else:
                data_str = f"{self.data[0]:02X}..{self.data[-1]:02X} ({len(self.data)} bytes)"
        else:
            data_str = "-"

        # Status string
        status_parts = []
        if not self.ack_received:
            status_parts.append("NAK")
        if self.timeout:
            status_parts.append("TIMEOUT")
        if self.arbitration_lost:
            status_parts.append("ARB_LOST")
        if self.pec_enabled:
            pec_status = "PEC_OK" if self.pec_valid else "PEC_ERR"
            status_parts.append(pec_status)
        if not self.completed:
            status_parts.append("INCOMPLETE")

        status_str = ",".join(status_parts) if status_parts else "OK"

        if compact:
            # Single line format
            time_str = f"@{self.start_time:.1f}ns"
            if self.trans_type in [SMBusTransactionType.QUICK_CMD]:
                return f"{time_str} {trans_name} {addr_str}/{rw_str} [{status_str}]"
            elif self.trans_type in [SMBusTransactionType.SEND_BYTE,
                                     SMBusTransactionType.RECV_BYTE]:
                return f"{time_str} {trans_name} {addr_str}/{rw_str} data={data_str} [{status_str}]"
            else:
                return (f"{time_str} {trans_name} {addr_str}/{rw_str} "
                        f"cmd=0x{self.command:02X} data={data_str} [{status_str}]")
        else:
            # Multi-line format
            lines = [
                f"SMBus Transaction: {trans_name}",
                f"  Time: {self.start_time:.1f}ns - {self.end_time:.1f}ns",
                f"  Address: {addr_str} ({rw_str})",
            ]
            if self.trans_type not in [SMBusTransactionType.QUICK_CMD,
                                       SMBusTransactionType.SEND_BYTE,
                                       SMBusTransactionType.RECV_BYTE]:
                lines.append(f"  Command: 0x{self.command:02X}")

            if self.data:
                lines.append(f"  Data: [{' '.join(f'0x{b:02X}' for b in self.data)}]")
                if self.trans_type in [SMBusTransactionType.BLOCK_WRITE,
                                       SMBusTransactionType.BLOCK_READ,
                                       SMBusTransactionType.BLOCK_PROC]:
                    lines.append(f"  Byte Count: {self.byte_count}")

            if self.pec_enabled:
                lines.append(f"  PEC: 0x{self.pec:02X} ({'valid' if self.pec_valid else 'INVALID'})")

            lines.append(f"  Status: {status_str}")
            return "\n".join(lines)

    def __str__(self) -> str:
        return self.formatted(compact=True)

    def __repr__(self) -> str:
        return (f"SMBusPacket(type={self.trans_type.name}, "
                f"addr=0x{self.slave_addr:02X}, rw={self.read_write}, "
                f"cmd=0x{self.command:02X}, data={self.data})")

    @property
    def is_read(self) -> bool:
        """Return True if this is a read transaction"""
        return self.read_write == 1

    @property
    def is_write(self) -> bool:
        """Return True if this is a write transaction"""
        return self.read_write == 0

    @property
    def data_length(self) -> int:
        """Return number of data bytes"""
        return len(self.data)

    @property
    def word_data(self) -> Optional[int]:
        """Return word value (16-bit) if applicable, LSB first"""
        if len(self.data) >= 2:
            return self.data[0] | (self.data[1] << 8)
        elif len(self.data) == 1:
            return self.data[0]
        return None

    def copy(self) -> 'SMBusPacket':
        """Create a copy of this packet"""
        return SMBusPacket(
            start_time=self.start_time,
            end_time=self.end_time,
            trans_type=self.trans_type,
            slave_addr=self.slave_addr,
            read_write=self.read_write,
            command=self.command,
            data=self.data.copy(),
            byte_count=self.byte_count,
            pec=self.pec,
            pec_valid=self.pec_valid,
            pec_enabled=self.pec_enabled,
            ack_received=self.ack_received,
            completed=self.completed,
            timeout=self.timeout,
            arbitration_lost=self.arbitration_lost,
            direction=self.direction,
        )
