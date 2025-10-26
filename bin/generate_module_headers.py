#!/usr/bin/env python3
# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2025 sean galloway
#
# RTL Design Sherpa - Industry-Standard RTL Design and Verification
# https://github.com/sean-galloway/RTLDesignSherpa
#
# Module: Parameter
# Purpose: Module Header Generator
#
# Documentation: rtl/common/PRD.md
# Subsystem: common
#
# Author: sean galloway
# Created: 2025-10-18

"""
Module Header Generator

Automatically generates comprehensive header documentation for SystemVerilog
modules based on the DOCUMENTATION_STYLE_GUIDE.md standard.

Features:
- Parses module parameters and ports
- Generates standardized header blocks
- Adds Wavedrom timing diagrams for Priority 1 modules
- Preserves existing RTL code
- Creates backup before modification
"""

import re
import sys
from pathlib import Path
from typing import Dict, List, Tuple, Optional
from dataclasses import dataclass, field

@dataclass
class Parameter:
    name: str
    type: str = "int"
    default: str = ""
    range: str = ""
    description: str = ""

@dataclass
class Port:
    name: str
    direction: str  # input, output, inout
    width: str = ""
    description: str = ""

@dataclass
class ModuleInfo:
    name: str
    file_path: Path
    parameters: List[Parameter] = field(default_factory=list)
    ports: List[Port] = field(default_factory=list)
    has_clk: bool = False
    has_rst: bool = False
    category: str = ""
    priority: int = 3  # 1=high, 2=medium, 3=low

# Module categorization and descriptions
MODULE_DESCRIPTIONS = {
    # Counters
    "counter_bin": "Binary counter with FIFO-optimized wraparound (MSB inversion)",
    "counter_load_clear": "Binary counter with load and clear control",
    "counter_freq_invariant": "Frequency-invariant counter for time-based delays (ms/us)",
    "counter_bingray": "Binary to Gray code counter for CDC-safe pointer management",
    "counter_ring": "Ring counter with one-hot shifting",
    "counter_johnson": "Johnson counter providing 2N states from N flip-flops",
    "counter": "Basic parameterized binary counter",

    # Arbiters
    "arbiter_round_robin": "Round-robin arbiter with grant acknowledgment and pipelining",
    "arbiter_round_robin_simple": "Simplified round-robin arbiter without acknowledgment",
    "arbiter_round_robin_weighted": "Weighted round-robin arbiter for QoS prioritization",
    "arbiter_priority_encoder": "Priority encoder based arbiter (fixed priority)",

    # Data Integrity
    "dataint_crc": "Configurable CRC calculator supporting 300+ polynomial standards",
    "dataint_crc_xor_shift": "Optimized CRC using XOR-shift architecture",
    "dataint_crc_xor_shift_cascade": "Cascaded XOR-shift CRC for parallel processing",
    "dataint_ecc_hamming_encode_secded": "Hamming SECDED encoder (Single Error Correction, Double Error Detection)",
    "dataint_ecc_hamming_decode_secded": "Hamming SECDED decoder with error correction",
    "dataint_parity": "Parameterized parity generator (even/odd)",
    "dataint_checksum": "Simple byte-wise checksum calculator",

    # Synchronizers
    "glitch_free_n_dff_arn": "N-stage synchronizer for CDC with active-low reset",
    "reset_sync": "Reset synchronizer for safe clock domain crossing",
    "debounce": "Button debouncer with configurable settle time",

    # Clock Utilities
    "clock_divider": "Parameterized clock frequency divider",
    "clock_gate_ctrl": "Clock gating controller for power management",
    "clock_pulse": "Single-cycle pulse generator",
    "icg": "Integrated clock gate cell",

    # FIFOs
    "fifo_sync": "Synchronous FIFO with configurable depth",
    "fifo_async": "Asynchronous FIFO for clock domain crossing",
    "fifo_async_div2": "Optimized async FIFO for 2:1 clock ratio",
    "fifo_control": "FIFO control logic (pointer management)",

    # Encoders/Decoders
    "encoder": "Binary encoder (one-hot to binary)",
    "encoder_priority_enable": "Priority encoder with enable",
    "decoder": "Binary decoder (binary to one-hot)",
    "hex_to_7seg": "Hexadecimal to 7-segment display decoder",

    # Math - Basic
    "bin2gray": "Binary to Gray code converter",
    "gray2bin": "Gray to binary code converter",
    "grayj2bin": "Johnson counter Gray code to binary",
    "count_leading_zeros": "Leading zero counter (CLZ)",
    "find_first_set": "Find first set bit position (FFS)",
    "find_last_set": "Find last set bit position (FLS)",
    "leading_one_trailing_one": "Leading/trailing one detection",
    "reverse_vector": "Bit vector reversal",
    "bin_to_bcd": "Binary to BCD converter",

    # Shifters
    "shifter_barrel": "Barrel shifter for arbitrary bit shifts",
    "shifter_universal": "Universal shift register (left/right/parallel)",
    "shifter_lfsr": "Linear Feedback Shift Register (generic)",
    "shifter_lfsr_fibonacci": "Fibonacci LFSR configuration",
    "shifter_lfsr_galois": "Galois LFSR configuration",

    # Other
    "pwm": "Pulse Width Modulation generator",
    "sort": "Parallel sorting network",
    "cam_tag": "Content Addressable Memory tag lookup",
}

# Modules that benefit from Wavedrom diagrams
WAVEDROM_MODULES = {
    "counter_bin", "counter_load_clear", "counter_freq_invariant",
    "arbiter_round_robin", "arbiter_round_robin_weighted", "arbiter_priority_encoder",
    "dataint_crc", "glitch_free_n_dff_arn", "reset_sync",
    "clock_divider", "fifo_sync", "fifo_async"
}


class ModuleParser:
    """Parse SystemVerilog module to extract structure"""

    def __init__(self, file_path: Path):
        self.file_path = file_path
        self.content = file_path.read_text()

    def parse(self) -> Optional[ModuleInfo]:
        """Parse module and extract information"""
        # Find module declaration
        module_match = re.search(r'^\s*module\s+(\w+)', self.content, re.MULTILINE)
        if not module_match:
            return None

        info = ModuleInfo(
            name=module_match.group(1),
            file_path=self.file_path
        )

        # Extract parameters
        info.parameters = self._extract_parameters()

        # Extract ports
        info.ports = self._extract_ports()

        # Detect clock and reset
        info.has_clk = any(p.name in ['clk', 'i_clk', 'aclk'] for p in info.ports)
        info.has_rst = any('rst' in p.name.lower() for p in info.ports)

        # Categorize and prioritize
        info.category = self._categorize(info.name)
        info.priority = self._get_priority(info.name)

        return info

    def _extract_parameters(self) -> List[Parameter]:
        """Extract parameter declarations"""
        params = []

        # Find parameter block in module header
        param_pattern = r'parameter\s+(?:(int|logic|bit)\s+)?(\w+)\s*=\s*([^,\)]+)'
        matches = re.finditer(param_pattern, self.content)

        for match in matches:
            param = Parameter(
                name=match.group(2).strip(),
                type=match.group(1).strip() if match.group(1) else "int",
                default=match.group(3).strip()
            )
            params.append(param)

        return params

    def _extract_ports(self) -> List[Port]:
        """Extract port declarations"""
        ports = []

        # Find port declarations
        port_pattern = r'(input|output|inout)\s+(?:logic\s+)?(?:\[([^\]]+)\]\s+)?(\w+)'
        matches = re.finditer(port_pattern, self.content)

        for match in matches:
            port = Port(
                direction=match.group(1),
                width=match.group(2) if match.group(2) else "",
                name=match.group(3)
            )
            ports.append(port)

        return ports

    def _categorize(self, name: str) -> str:
        """Determine module category"""
        if 'counter' in name:
            return 'Counter'
        elif 'arbiter' in name:
            return 'Arbiter'
        elif 'dataint' in name or 'crc' in name or 'ecc' in name:
            return 'Data Integrity'
        elif 'sync' in name or 'cdc' in name or 'glitch' in name or 'debounce' in name:
            return 'Synchronizer'
        elif 'clock' in name or 'icg' in name:
            return 'Clock Utility'
        elif 'fifo' in name:
            return 'FIFO'
        elif 'encoder' in name or 'decoder' in name:
            return 'Encoder/Decoder'
        elif 'adder' in name or 'multiplier' in name or 'subtractor' in name:
            return 'Math'
        elif 'shifter' in name or 'lfsr' in name:
            return 'Shifter'
        else:
            return 'Utility'

    def _get_priority(self, name: str) -> int:
        """Determine documentation priority"""
        # Priority 1: High-value, frequently used
        priority_1 = [
            'counter_bin', 'counter_load_clear', 'counter_freq_invariant',
            'arbiter_round_robin', 'arbiter_priority_encoder', 'arbiter_round_robin_weighted',
            'dataint_crc', 'dataint_ecc_hamming_encode_secded', 'dataint_ecc_hamming_decode_secded',
            'glitch_free_n_dff_arn', 'reset_sync',
            'clock_divider', 'fifo_sync', 'fifo_async'
        ]

        if name in priority_1:
            return 1

        # Priority 2: Important but simple
        priority_2 = [
            'bin2gray', 'gray2bin', 'count_leading_zeros',
            'encoder', 'decoder', 'pwm', 'clock_gate_ctrl'
        ]

        if name in priority_2:
            return 2

        # Priority 3: Supporting/internal
        return 3


class HeaderGenerator:
    """Generate module header documentation"""

    def __init__(self, info: ModuleInfo):
        self.info = info

    def generate(self) -> str:
        """Generate complete header block"""
        lines = []

        # Banner
        lines.append("=" * 78)
        lines.append(f"Module: {self.info.name}")
        lines.append("=" * 78)

        # Description
        lines.extend(self._generate_description())

        # Parameters
        if self.info.parameters:
            lines.append("-" * 78)
            lines.append("Parameters:")
            lines.append("-" * 78)
            lines.extend(self._generate_parameters())

        # Ports
        lines.append("-" * 78)
        lines.append("Ports:")
        lines.append("-" * 78)
        lines.extend(self._generate_ports())

        # Timing
        lines.append("-" * 78)
        lines.append("Timing:")
        lines.append("-" * 78)
        lines.extend(self._generate_timing())

        # Behavior
        lines.append("-" * 78)
        lines.append("Behavior:")
        lines.append("-" * 78)
        lines.extend(self._generate_behavior())

        # Usage Example
        lines.append("-" * 78)
        lines.append("Usage Example:")
        lines.append("-" * 78)
        lines.extend(self._generate_usage())

        # Notes
        lines.append("-" * 78)
        lines.append("Notes:")
        lines.append("-" * 78)
        lines.extend(self._generate_notes())

        # Related Modules
        lines.append("-" * 78)
        lines.append("Related Modules:")
        lines.append("-" * 78)
        lines.extend(self._generate_related())

        # Test Reference
        lines.append("-" * 78)
        lines.append("Test:")
        lines.append("-" * 78)
        lines.extend(self._generate_test())

        lines.append("=" * 78)

        # Format as comment block
        return "\n".join(f"// {line}" if line else "//" for line in lines)

    def _generate_description(self) -> List[str]:
        """Generate description section"""
        desc = MODULE_DESCRIPTIONS.get(self.info.name, "TODO: Add module description")

        return [
            "Description:",
            f"  {desc}",
            "",
        ]

    def _generate_parameters(self) -> List[str]:
        """Generate parameter documentation"""
        lines = []
        for param in self.info.parameters:
            lines.append(f"  {param.name}:")
            lines.append(f"    Description: TODO: Describe {param.name}")
            lines.append(f"    Type: {param.type}")
            lines.append(f"    Default: {param.default}")
            lines.append(f"    Range: TODO: Specify valid range")
            lines.append("")
        return lines

    def _generate_ports(self) -> List[str]:
        """Generate port documentation"""
        lines = []

        # Group by direction
        inputs = [p for p in self.info.ports if p.direction == 'input']
        outputs = [p for p in self.info.ports if p.direction == 'output']
        inouts = [p for p in self.info.ports if p.direction == 'inout']

        if inputs:
            lines.append("  Inputs:")
            for port in inputs:
                width_str = f"[{port.width}]" if port.width else ""
                lines.append(f"    {port.name}{width_str}:")
                lines.append(f"      TODO: Describe {port.name}")
            lines.append("")

        if outputs:
            lines.append("  Outputs:")
            for port in outputs:
                width_str = f"[{port.width}]" if port.width else ""
                lines.append(f"    {port.name}{width_str}:")
                lines.append(f"      TODO: Describe {port.name}")
            lines.append("")

        if inouts:
            lines.append("  Inouts:")
            for port in inouts:
                width_str = f"[{port.width}]" if port.width else ""
                lines.append(f"    {port.name}{width_str}:")
                lines.append(f"      TODO: Describe {port.name}")
            lines.append("")

        return lines

    def _generate_timing(self) -> List[str]:
        """Generate timing information"""
        if self.info.has_clk:
            return [
                "  Latency: TODO: Specify cycle count",
                "  Combinational: TODO: Specify if any",
                ""
            ]
        else:
            return [
                "  Combinational module (no clock)",
                ""
            ]

    def _generate_behavior(self) -> List[str]:
        """Generate behavior description"""
        lines = [
            "  TODO: Describe operational behavior",
            "  1. Step 1",
            "  2. Step 2",
            ""
        ]

        # Add Wavedrom for priority modules
        if self.info.name in WAVEDROM_MODULES:
            lines.extend([
                "  Timing Diagram:",
                "  TODO: Add Wavedrom diagram",
                ""
            ])

        return lines

    def _generate_usage(self) -> List[str]:
        """Generate usage example"""
        lines = [f"  {self.info.name} #("]

        for i, param in enumerate(self.info.parameters):
            comma = "," if i < len(self.info.parameters) - 1 else ""
            lines.append(f"      .{param.name}(value{i}){comma}")

        lines.append("  ) u_instance (")

        for i, port in enumerate(self.info.ports):
            comma = "," if i < len(self.info.ports) - 1 else ""
            lines.append(f"      .{port.name}(signal{i}){comma}")

        lines.append("  );")
        lines.append("")

        return lines

    def _generate_notes(self) -> List[str]:
        """Generate notes section"""
        return [
            "  - TODO: Add important usage notes",
            "  - TODO: Document constraints or limitations",
            ""
        ]

    def _generate_related(self) -> List[str]:
        """Generate related modules"""
        return [
            "  - TODO: List related modules",
            ""
        ]

    def _generate_test(self) -> List[str]:
        """Generate test reference"""
        return [
            f"  Location: val/common/test_{self.info.name}.py",
            f"  Run: pytest val/common/test_{self.info.name}.py -v",
            ""
        ]


def main():
    """Main entry point"""
    repo_root = Path(__file__).parent.parent
    rtl_dir = repo_root / "rtl" / "common"

    if not rtl_dir.exists():
        print(f"Error: {rtl_dir} not found", file=sys.stderr)
        sys.exit(1)

    # Parse all modules
    modules = []
    for sv_file in sorted(rtl_dir.glob("*.sv")):
        if "testcode" in str(sv_file):
            continue

        parser = ModuleParser(sv_file)
        info = parser.parse()
        if info:
            modules.append(info)

    print(f"Found {len(modules)} modules")
    print(f"Priority 1 (high-value): {sum(1 for m in modules if m.priority == 1)}")
    print(f"Priority 2 (important): {sum(1 for m in modules if m.priority == 2)}")
    print(f"Priority 3 (supporting): {sum(1 for m in modules if m.priority == 3)}")
    print()
    print("To generate headers for all modules, this script would need to:")
    print("1. Create backups of existing files")
    print("2. Generate comprehensive headers")
    print("3. Preserve existing RTL code")
    print("4. Write updated files")
    print()
    print("Use --generate flag to proceed with generation (not implemented yet)")


if __name__ == "__main__":
    main()
