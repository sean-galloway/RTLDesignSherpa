# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2025 sean galloway
#
# RTL Design Sherpa - Industry-Standard RTL Design and Verification
# https://github.com/sean-galloway/RTLDesignSherpa
#
# Module: SignalNaming
# Purpose: Complete signal definition database - single source of truth
#
# Author: sean galloway
# Created: 2025-11-05

"""
Signal Definition Database for Bridge Generator

This module is the SINGLE SOURCE OF TRUTH for all signal properties:
- Signal names (industry-standard naming convention)
- Signal direction (input/output from interface perspective)
- Signal widths (parameterized expressions)
- Bus ranges [max:min]
- Signal types (scalar vs vector)

Key Design Principles:
1. Complete signal specification in one place
2. Protocol-aware (AXI4, APB, etc.)
3. Direction from interface perspective (master outputs awvalid, slave inputs awvalid)
4. Parameterized widths (ID_WIDTH, ADDR_WIDTH, DATA_WIDTH, etc.)
5. Easy to query for code generation

Naming Convention (Industry Standard):
Master AXI4: <port>_m_axi_<channel><signal>
Slave AXI4:  <port>_s_axi_<channel><signal>
APB:         <port>_<signal>

Examples:
cpu_m_axi_awid[7:0]    - Master AXI4 write address ID (8-bit vector, output)
ddr_s_axi_rdata[31:0]  - Slave AXI4 read data (32-bit vector, output)
apb0_psel              - APB select (scalar, output)
"""

from enum import Enum
from typing import Dict, List, Tuple, Optional
from dataclasses import dataclass


class Protocol(Enum):
    """Supported protocols"""
    AXI4 = "axi4"
    APB = "apb"


class Direction(Enum):
    """Port direction (from bridge perspective)"""
    MASTER = "master"  # Bridge has master interface (receives from external master)
    SLAVE = "slave"    # Bridge has slave interface (drives to external slave)


class AXI4Channel(Enum):
    """AXI4 channel identifiers"""
    AW = "aw"  # Write Address
    W = "w"    # Write Data
    B = "b"    # Write Response
    AR = "ar"  # Read Address
    R = "r"    # Read Data


class PortDirection(Enum):
    """Signal direction (input/output from interface perspective)"""
    INPUT = "input"
    OUTPUT = "output"


@dataclass
class SignalInfo:
    """
    Complete signal information - single source of truth.

    Attributes:
        name: Signal base name (e.g., "id", "addr", "valid")
        direction: PortDirection (INPUT/OUTPUT from interface perspective)
        width_expr: Width expression (e.g., "ID_WIDTH", "ADDR_WIDTH", "1")
        width_param: Parameter name if parameterized (e.g., "ID_WIDTH")
        is_vector: True if signal is a bus, False if scalar
        description: Human-readable description
    """
    name: str
    direction: PortDirection
    width_expr: str
    width_param: Optional[str] = None
    is_vector: bool = True
    description: str = ""

    def get_range(self, width_values: Dict[str, int]) -> str:
        """
        Get bus range string [max:min] with actual values.

        Args:
            width_values: Dict mapping parameter names to actual values
                        (e.g., {"ID_WIDTH": 8, "ADDR_WIDTH": 32})

        Returns:
            Range string like "[7:0]" for vectors, "" for scalars
        """
        if not self.is_vector:
            return ""

        # Evaluate width expression
        if self.width_param and self.width_param in width_values:
            width = width_values[self.width_param]
        else:
            # Try to evaluate as integer
            try:
                width = int(self.width_expr)
            except ValueError:
                # Unknown parameter, return expression
                return f"[{self.width_expr}-1:0]"

        if width == 1:
            return ""  # Scalar
        else:
            return f"[{width-1}:0]"

    def get_declaration(self, signal_name: str, width_values: Dict[str, int]) -> str:
        """
        Get complete SystemVerilog signal declaration.

        Args:
            signal_name: Full signal name (e.g., "cpu_m_axi_awid")
            width_values: Dict mapping parameter names to values

        Returns:
            Declaration string like "input logic [7:0] cpu_m_axi_awid"
        """
        dir_str = self.direction.value
        range_str = self.get_range(width_values)

        if range_str:
            return f"{dir_str}  logic {range_str}  {signal_name}"
        else:
            return f"{dir_str}  logic         {signal_name}"


# ============================================================================
# AXI4 Signal Definitions (Industry Standard)
# ============================================================================

# AXI4 Master interface signal definitions
# Direction is from MASTER perspective (what master drives vs accepts)
AXI4_MASTER_SIGNALS = {
    AXI4Channel.AW: [
        SignalInfo("id", PortDirection.OUTPUT, "ID_WIDTH", "ID_WIDTH", True, "Write transaction ID"),
        SignalInfo("addr", PortDirection.OUTPUT, "ADDR_WIDTH", "ADDR_WIDTH", True, "Write address"),
        SignalInfo("len", PortDirection.OUTPUT, "8", None, True, "Burst length (beats - 1)"),
        SignalInfo("size", PortDirection.OUTPUT, "3", None, True, "Burst size (bytes per beat)"),
        SignalInfo("burst", PortDirection.OUTPUT, "2", None, True, "Burst type (FIXED/INCR/WRAP)"),
        SignalInfo("lock", PortDirection.OUTPUT, "1", None, False, "Lock type (deprecated in AXI4)"),
        SignalInfo("cache", PortDirection.OUTPUT, "4", None, True, "Memory type/cacheable"),
        SignalInfo("prot", PortDirection.OUTPUT, "3", None, True, "Protection type"),
        SignalInfo("qos", PortDirection.OUTPUT, "4", None, True, "Quality of Service"),
        SignalInfo("region", PortDirection.OUTPUT, "4", None, True, "Region identifier"),
        SignalInfo("user", PortDirection.OUTPUT, "USER_WIDTH", "USER_WIDTH", True, "User-defined sideband"),
        SignalInfo("valid", PortDirection.OUTPUT, "1", None, False, "Write address valid"),
        SignalInfo("ready", PortDirection.INPUT, "1", None, False, "Write address ready"),
    ],
    AXI4Channel.W: [
        SignalInfo("data", PortDirection.OUTPUT, "DATA_WIDTH", "DATA_WIDTH", True, "Write data"),
        SignalInfo("strb", PortDirection.OUTPUT, "DATA_WIDTH/8", "STRB_WIDTH", True, "Write strobes (byte enables)"),
        SignalInfo("last", PortDirection.OUTPUT, "1", None, False, "Write last beat"),
        SignalInfo("user", PortDirection.OUTPUT, "USER_WIDTH", "USER_WIDTH", True, "User-defined sideband"),
        SignalInfo("valid", PortDirection.OUTPUT, "1", None, False, "Write data valid"),
        SignalInfo("ready", PortDirection.INPUT, "1", None, False, "Write data ready"),
    ],
    AXI4Channel.B: [
        SignalInfo("id", PortDirection.INPUT, "ID_WIDTH", "ID_WIDTH", True, "Write response ID"),
        SignalInfo("resp", PortDirection.INPUT, "2", None, True, "Write response (OKAY/EXOKAY/SLVERR/DECERR)"),
        SignalInfo("user", PortDirection.INPUT, "USER_WIDTH", "USER_WIDTH", True, "User-defined sideband"),
        SignalInfo("valid", PortDirection.INPUT, "1", None, False, "Write response valid"),
        SignalInfo("ready", PortDirection.OUTPUT, "1", None, False, "Write response ready"),
    ],
    AXI4Channel.AR: [
        SignalInfo("id", PortDirection.OUTPUT, "ID_WIDTH", "ID_WIDTH", True, "Read transaction ID"),
        SignalInfo("addr", PortDirection.OUTPUT, "ADDR_WIDTH", "ADDR_WIDTH", True, "Read address"),
        SignalInfo("len", PortDirection.OUTPUT, "8", None, True, "Burst length (beats - 1)"),
        SignalInfo("size", PortDirection.OUTPUT, "3", None, True, "Burst size (bytes per beat)"),
        SignalInfo("burst", PortDirection.OUTPUT, "2", None, True, "Burst type (FIXED/INCR/WRAP)"),
        SignalInfo("lock", PortDirection.OUTPUT, "1", None, False, "Lock type (deprecated in AXI4)"),
        SignalInfo("cache", PortDirection.OUTPUT, "4", None, True, "Memory type/cacheable"),
        SignalInfo("prot", PortDirection.OUTPUT, "3", None, True, "Protection type"),
        SignalInfo("qos", PortDirection.OUTPUT, "4", None, True, "Quality of Service"),
        SignalInfo("region", PortDirection.OUTPUT, "4", None, True, "Region identifier"),
        SignalInfo("user", PortDirection.OUTPUT, "USER_WIDTH", "USER_WIDTH", True, "User-defined sideband"),
        SignalInfo("valid", PortDirection.OUTPUT, "1", None, False, "Read address valid"),
        SignalInfo("ready", PortDirection.INPUT, "1", None, False, "Read address ready"),
    ],
    AXI4Channel.R: [
        SignalInfo("id", PortDirection.INPUT, "ID_WIDTH", "ID_WIDTH", True, "Read transaction ID"),
        SignalInfo("data", PortDirection.INPUT, "DATA_WIDTH", "DATA_WIDTH", True, "Read data"),
        SignalInfo("resp", PortDirection.INPUT, "2", None, True, "Read response (OKAY/EXOKAY/SLVERR/DECERR)"),
        SignalInfo("last", PortDirection.INPUT, "1", None, False, "Read last beat"),
        SignalInfo("user", PortDirection.INPUT, "USER_WIDTH", "USER_WIDTH", True, "User-defined sideband"),
        SignalInfo("valid", PortDirection.INPUT, "1", None, False, "Read data valid"),
        SignalInfo("ready", PortDirection.OUTPUT, "1", None, False, "Read data ready"),
    ],
}

# AXI4 Slave interface signal definitions
# Direction is INVERTED from master (slave receives what master sends)
AXI4_SLAVE_SIGNALS = {
    AXI4Channel.AW: [
        SignalInfo("id", PortDirection.INPUT, "ID_WIDTH", "ID_WIDTH", True, "Write transaction ID"),
        SignalInfo("addr", PortDirection.INPUT, "ADDR_WIDTH", "ADDR_WIDTH", True, "Write address"),
        SignalInfo("len", PortDirection.INPUT, "8", None, True, "Burst length (beats - 1)"),
        SignalInfo("size", PortDirection.INPUT, "3", None, True, "Burst size (bytes per beat)"),
        SignalInfo("burst", PortDirection.INPUT, "2", None, True, "Burst type (FIXED/INCR/WRAP)"),
        SignalInfo("lock", PortDirection.INPUT, "1", None, False, "Lock type (deprecated in AXI4)"),
        SignalInfo("cache", PortDirection.INPUT, "4", None, True, "Memory type/cacheable"),
        SignalInfo("prot", PortDirection.INPUT, "3", None, True, "Protection type"),
        SignalInfo("qos", PortDirection.INPUT, "4", None, True, "Quality of Service"),
        SignalInfo("region", PortDirection.INPUT, "4", None, True, "Region identifier"),
        SignalInfo("user", PortDirection.INPUT, "USER_WIDTH", "USER_WIDTH", True, "User-defined sideband"),
        SignalInfo("valid", PortDirection.INPUT, "1", None, False, "Write address valid"),
        SignalInfo("ready", PortDirection.OUTPUT, "1", None, False, "Write address ready"),
    ],
    AXI4Channel.W: [
        SignalInfo("data", PortDirection.INPUT, "DATA_WIDTH", "DATA_WIDTH", True, "Write data"),
        SignalInfo("strb", PortDirection.INPUT, "DATA_WIDTH/8", "STRB_WIDTH", True, "Write strobes (byte enables)"),
        SignalInfo("last", PortDirection.INPUT, "1", None, False, "Write last beat"),
        SignalInfo("user", PortDirection.INPUT, "USER_WIDTH", "USER_WIDTH", True, "User-defined sideband"),
        SignalInfo("valid", PortDirection.INPUT, "1", None, False, "Write data valid"),
        SignalInfo("ready", PortDirection.OUTPUT, "1", None, False, "Write data ready"),
    ],
    AXI4Channel.B: [
        SignalInfo("id", PortDirection.OUTPUT, "ID_WIDTH", "ID_WIDTH", True, "Write response ID"),
        SignalInfo("resp", PortDirection.OUTPUT, "2", None, True, "Write response (OKAY/EXOKAY/SLVERR/DECERR)"),
        SignalInfo("user", PortDirection.OUTPUT, "USER_WIDTH", "USER_WIDTH", True, "User-defined sideband"),
        SignalInfo("valid", PortDirection.OUTPUT, "1", None, False, "Write response valid"),
        SignalInfo("ready", PortDirection.INPUT, "1", None, False, "Write response ready"),
    ],
    AXI4Channel.AR: [
        SignalInfo("id", PortDirection.INPUT, "ID_WIDTH", "ID_WIDTH", True, "Read transaction ID"),
        SignalInfo("addr", PortDirection.INPUT, "ADDR_WIDTH", "ADDR_WIDTH", True, "Read address"),
        SignalInfo("len", PortDirection.INPUT, "8", None, True, "Burst length (beats - 1)"),
        SignalInfo("size", PortDirection.INPUT, "3", None, True, "Burst size (bytes per beat)"),
        SignalInfo("burst", PortDirection.INPUT, "2", None, True, "Burst type (FIXED/INCR/WRAP)"),
        SignalInfo("lock", PortDirection.INPUT, "1", None, False, "Lock type (deprecated in AXI4)"),
        SignalInfo("cache", PortDirection.INPUT, "4", None, True, "Memory type/cacheable"),
        SignalInfo("prot", PortDirection.INPUT, "3", None, True, "Protection type"),
        SignalInfo("qos", PortDirection.INPUT, "4", None, True, "Quality of Service"),
        SignalInfo("region", PortDirection.INPUT, "4", None, True, "Region identifier"),
        SignalInfo("user", PortDirection.INPUT, "USER_WIDTH", "USER_WIDTH", True, "User-defined sideband"),
        SignalInfo("valid", PortDirection.INPUT, "1", None, False, "Read address valid"),
        SignalInfo("ready", PortDirection.OUTPUT, "1", None, False, "Read address ready"),
    ],
    AXI4Channel.R: [
        SignalInfo("id", PortDirection.OUTPUT, "ID_WIDTH", "ID_WIDTH", True, "Read transaction ID"),
        SignalInfo("data", PortDirection.OUTPUT, "DATA_WIDTH", "DATA_WIDTH", True, "Read data"),
        SignalInfo("resp", PortDirection.OUTPUT, "2", None, True, "Read response (OKAY/EXOKAY/SLVERR/DECERR)"),
        SignalInfo("last", PortDirection.OUTPUT, "1", None, False, "Read last beat"),
        SignalInfo("user", PortDirection.OUTPUT, "USER_WIDTH", "USER_WIDTH", True, "User-defined sideband"),
        SignalInfo("valid", PortDirection.OUTPUT, "1", None, False, "Read data valid"),
        SignalInfo("ready", PortDirection.INPUT, "1", None, False, "Read data ready"),
    ],
}

# ============================================================================
# APB Signal Definitions (AMBA APB Protocol v2.0)
# ============================================================================

APB_MASTER_SIGNALS = [
    SignalInfo("PSEL", PortDirection.OUTPUT, "1", None, False, "Peripheral select"),
    SignalInfo("PADDR", PortDirection.OUTPUT, "ADDR_WIDTH", "ADDR_WIDTH", True, "APB address bus"),
    SignalInfo("PENABLE", PortDirection.OUTPUT, "1", None, False, "APB enable (setup/access phase)"),
    SignalInfo("PWRITE", PortDirection.OUTPUT, "1", None, False, "Write enable (1=write, 0=read)"),
    SignalInfo("PWDATA", PortDirection.OUTPUT, "DATA_WIDTH", "DATA_WIDTH", True, "Write data bus"),
    SignalInfo("PSTRB", PortDirection.OUTPUT, "DATA_WIDTH/8", "STRB_WIDTH", True, "Write strobes (byte lanes)"),
    SignalInfo("PPROT", PortDirection.OUTPUT, "3", None, True, "Protection type"),
    SignalInfo("PRDATA", PortDirection.INPUT, "DATA_WIDTH", "DATA_WIDTH", True, "Read data bus"),
    SignalInfo("PREADY", PortDirection.INPUT, "1", None, False, "Transfer ready (wait states)"),
    SignalInfo("PSLVERR", PortDirection.INPUT, "1", None, False, "Transfer error"),
]

APB_SLAVE_SIGNALS = [
    SignalInfo("PSEL", PortDirection.INPUT, "1", None, False, "Peripheral select"),
    SignalInfo("PADDR", PortDirection.INPUT, "ADDR_WIDTH", "ADDR_WIDTH", True, "APB address bus"),
    SignalInfo("PENABLE", PortDirection.INPUT, "1", None, False, "APB enable (setup/access phase)"),
    SignalInfo("PWRITE", PortDirection.INPUT, "1", None, False, "Write enable (1=write, 0=read)"),
    SignalInfo("PWDATA", PortDirection.INPUT, "DATA_WIDTH", "DATA_WIDTH", True, "Write data bus"),
    SignalInfo("PSTRB", PortDirection.INPUT, "DATA_WIDTH/8", "STRB_WIDTH", True, "Write strobes (byte lanes)"),
    SignalInfo("PPROT", PortDirection.INPUT, "3", None, True, "Protection type"),
    SignalInfo("PRDATA", PortDirection.OUTPUT, "DATA_WIDTH", "DATA_WIDTH", True, "Read data bus"),
    SignalInfo("PREADY", PortDirection.OUTPUT, "1", None, False, "Transfer ready (wait states)"),
    SignalInfo("PSLVERR", PortDirection.OUTPUT, "1", None, False, "Transfer error"),
]


# ============================================================================
# SignalNaming Class - Main API
# ============================================================================

class SignalNaming:
    """
    Centralized signal naming and definition utility.

    Single source of truth for all signal properties:
    - Names, directions, widths, ranges
    """

    @staticmethod
    def axi4_signal_name(port_name: str, direction: Direction,
                        channel: AXI4Channel, signal: str) -> str:
        """
        Generate AXI4 signal name following bridge convention.

        Format: <port>_axi_<channel><signal>

        Args:
            port_name: Port name (e.g., "cpu", "ddr_controller")
            direction: Direction.MASTER or Direction.SLAVE (used for port direction, not signal naming)
            channel: AXI4 channel (AW, W, B, AR, R)
            signal: Signal name within channel (e.g., "id", "addr", "valid")

        Returns:
            Complete signal name (e.g., "cpu_axi_awid")

        Examples:
            >>> SignalNaming.axi4_signal_name("cpu", Direction.MASTER, AXI4Channel.AW, "id")
            'cpu_axi_awid'
            >>> SignalNaming.axi4_signal_name("ddr", Direction.SLAVE, AXI4Channel.R, "data")
            'ddr_axi_rdata'

        Naming Convention Rationale:
            - NO direction prefix (m_/s_) - Port name already identifies endpoint
            - Protocol identifier (_axi_) retained for easy signal tracing in waveforms
            - User requirement: "the _m_axi should be just _axi" (signal naming session)

        Format: <port>_axi_<channel><signal>
            ✅ CORRECT: cpu_axi_awaddr, ddr_axi_rdata
            ❌ WRONG:   cpu_m_axi_awaddr (redundant direction prefix)
        """
        # Implementation note: No direction prefix in signal names
        # Port name (cpu, ddr, m0, s1) is sufficient to identify master vs slave
        # Adding _m_ or _s_ prefix creates redundant naming (cpu_m_axi_awaddr)
        return f"{port_name}_axi_{channel.value}{signal}"

    @staticmethod
    def apb_signal_name(port_name: str, signal: str) -> str:
        """
        Generate APB signal name following industry standard convention.

        Format: <port>_<signal>

        Args:
            port_name: Port name (e.g., "apb0", "apb_periph")
            signal: APB signal name (e.g., "psel", "paddr", "pready")

        Returns:
            Complete signal name (e.g., "apb0_psel")

        Examples:
            >>> SignalNaming.apb_signal_name("apb0", "PSEL")
            'apb0_PSEL'
            >>> SignalNaming.apb_signal_name("apb_periph", "PADDR")
            'apb_periph_PADDR'
        """
        return f"{port_name}_{signal}"

    @staticmethod
    def get_axi4_signal_info(direction: Direction, channel: AXI4Channel,
                            signal: str) -> Optional[SignalInfo]:
        """
        Get complete signal information for an AXI4 signal.

        Args:
            direction: Direction.MASTER or Direction.SLAVE
            channel: AXI4 channel
            signal: Signal name within channel

        Returns:
            SignalInfo object with complete signal properties, or None if not found
        """
        signal_db = AXI4_MASTER_SIGNALS if direction == Direction.MASTER else AXI4_SLAVE_SIGNALS

        if channel not in signal_db:
            return None

        for sig_info in signal_db[channel]:
            if sig_info.name == signal:
                return sig_info

        return None

    @staticmethod
    def get_apb_signal_info(direction: Direction, signal: str) -> Optional[SignalInfo]:
        """
        Get complete signal information for an APB signal.

        Args:
            direction: Direction.MASTER or Direction.SLAVE
            signal: APB signal name

        Returns:
            SignalInfo object with complete signal properties, or None if not found
        """
        signal_db = APB_MASTER_SIGNALS if direction == Direction.MASTER else APB_SLAVE_SIGNALS

        for sig_info in signal_db:
            if sig_info.name == signal:
                return sig_info

        return None

    @staticmethod
    def get_all_axi4_signals(port_name: str, direction: Direction,
                            channels: List[AXI4Channel]) -> Dict[AXI4Channel, List[Tuple[str, SignalInfo]]]:
        """
        Get all signal names and info for specified AXI4 channels.

        Args:
            port_name: Port name
            direction: Direction.MASTER or Direction.SLAVE
            channels: List of channels to generate (e.g., [AW, W, B] for write-only)

        Returns:
            Dictionary mapping channel to list of (signal_name, SignalInfo) tuples

        Example:
            >>> signals = SignalNaming.get_all_axi4_signals("cpu", Direction.MASTER, [AXI4Channel.AW])
            >>> for sig_name, sig_info in signals[AXI4Channel.AW]:
            ...     print(f"{sig_name}: {sig_info.direction.value} {sig_info.get_range({'ID_WIDTH': 8})}")
            cpu_m_axi_awid: output [7:0]
            cpu_m_axi_awaddr: output [31:0]
            cpu_m_axi_awvalid: output
        """
        signal_db = AXI4_MASTER_SIGNALS if direction == Direction.MASTER else AXI4_SLAVE_SIGNALS
        result = {}

        for channel in channels:
            if channel not in signal_db:
                continue

            channel_signals = []
            for sig_info in signal_db[channel]:
                sig_name = SignalNaming.axi4_signal_name(port_name, direction, channel, sig_info.name)
                channel_signals.append((sig_name, sig_info))

            result[channel] = channel_signals

        return result

    @staticmethod
    def get_all_apb_signals(port_name: str, direction: Direction) -> List[Tuple[str, SignalInfo]]:
        """
        Get all APB signal names and info for a port.

        Args:
            port_name: Port name
            direction: Direction.MASTER or Direction.SLAVE

        Returns:
            List of (signal_name, SignalInfo) tuples

        Example:
            >>> signals = SignalNaming.get_all_apb_signals("apb0", Direction.MASTER)
            >>> for sig_name, sig_info in signals:
            ...     print(f"{sig_name}: {sig_info.direction.value}")
            apb0_psel: output
            apb0_paddr: output
            apb0_prdata: input
        """
        signal_db = APB_MASTER_SIGNALS if direction == Direction.MASTER else APB_SLAVE_SIGNALS

        return [(SignalNaming.apb_signal_name(port_name, sig_info.name), sig_info)
                for sig_info in signal_db]

    @staticmethod
    def channels_from_type(channel_type: str) -> List[AXI4Channel]:
        """
        Convert channel type string to list of AXI4 channels.

        Args:
            channel_type: "rw", "wr", or "rd"

        Returns:
            List of AXI4Channel enums

        Examples:
            >>> SignalNaming.channels_from_type("rw")
            [AXI4Channel.AW, AXI4Channel.W, AXI4Channel.B, AXI4Channel.AR, AXI4Channel.R]
            >>> SignalNaming.channels_from_type("wr")
            [AXI4Channel.AW, AXI4Channel.W, AXI4Channel.B]
            >>> SignalNaming.channels_from_type("rd")
            [AXI4Channel.AR, AXI4Channel.R]
        """
        if channel_type == "rw":
            return [AXI4Channel.AW, AXI4Channel.W, AXI4Channel.B,
                    AXI4Channel.AR, AXI4Channel.R]
        elif channel_type == "wr":
            return [AXI4Channel.AW, AXI4Channel.W, AXI4Channel.B]
        elif channel_type == "rd":
            return [AXI4Channel.AR, AXI4Channel.R]
        else:
            raise ValueError(f"Unknown channel type: {channel_type}")


# ============================================================================
# Example usage and verification
# ============================================================================

if __name__ == "__main__":
    # Test signal information database
    print("=== AXI4 Signal Information Database ===")

    # Example width values
    widths = {
        "ID_WIDTH": 8,
        "ADDR_WIDTH": 32,
        "DATA_WIDTH": 64,
        "STRB_WIDTH": 8,
        "USER_WIDTH": 1
    }

    # Get AW channel signals for master
    print("\nAW Channel Signals (Master):")
    signals = SignalNaming.get_all_axi4_signals("cpu", Direction.MASTER, [AXI4Channel.AW])
    for sig_name, sig_info in signals[AXI4Channel.AW]:
        decl = sig_info.get_declaration(sig_name, widths)
        print(f"  {decl}")

    # Get R channel signals for slave
    print("\nR Channel Signals (Slave):")
    signals = SignalNaming.get_all_axi4_signals("ddr", Direction.SLAVE, [AXI4Channel.R])
    for sig_name, sig_info in signals[AXI4Channel.R]:
        decl = sig_info.get_declaration(sig_name, widths)
        print(f"  {decl}")

    # Get APB signals
    print("\nAPB Signals (Master):")
    apb_widths = {
        "ADDR_WIDTH": 32,
        "DATA_WIDTH": 32,
        "STRB_WIDTH": 4
    }
    signals = SignalNaming.get_all_apb_signals("apb0", Direction.MASTER)
    for sig_name, sig_info in signals[:5]:  # Show first 5
        decl = sig_info.get_declaration(sig_name, apb_widths)
        print(f"  {decl}")
    print(f"  ... ({len(signals)} total signals)")

    # Show signal query
    print("\n=== Signal Query Example ===")
    sig_info = SignalNaming.get_axi4_signal_info(Direction.MASTER, AXI4Channel.AW, "id")
    if sig_info:
        print(f"Signal: awid")
        print(f"  Direction: {sig_info.direction.value}")
        print(f"  Width: {sig_info.width_expr}")
        print(f"  Range: {sig_info.get_range(widths)}")
        print(f"  Is Vector: {sig_info.is_vector}")
        print(f"  Description: {sig_info.description}")
