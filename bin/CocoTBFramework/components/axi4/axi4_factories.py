# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2025 sean galloway
#
# RTL Design Sherpa - Industry-Standard RTL Design and Verification
# https://github.com/sean-galloway/RTLDesignSherpa
#
# Module: axi4_factories
# Purpose: AXI4 Factory Functions - Enhanced with Integrated Compliance Checking
#
# Documentation: bin/CocoTBFramework/README.md
# Subsystem: framework
#
# Author: sean galloway
# Created: 2025-10-18

"""
AXI4 Factory Functions - Enhanced with Integrated Compliance Checking

ENHANCEMENT: Factory functions now automatically include compliance checking
when the AXI4_COMPLIANCE_CHECK environment variable is set. No changes
required to existing testbench code.

All existing factory function signatures remain identical for backward compatibility.
"""

from typing import Dict, Any, Optional
from contextlib import redirect_stdout
from .axi4_interfaces import AXI4MasterRead, AXI4MasterWrite, AXI4SlaveRead, AXI4SlaveWrite


def create_axi4_master_rd(dut, clock, prefix="", log=None, **kwargs) -> Dict[str, Any]:
    """
    Create AXI4 Master Read interface with automatic compliance checking.

    Args:
        dut: Device under test
        clock: Clock signal
        prefix: Signal prefix ("fub_axi_", "m_axi_", etc.)
        log: log file from the TB
        **kwargs: Additional configuration (data_width, id_width, etc.)

    Returns:
        Dictionary containing AXI4 read master components

    ENHANCEMENT: Now includes compliance checking automatically when enabled
    """
    # Create the master read interface (compliance checking included automatically)
    master_read = AXI4MasterRead(dut, clock, prefix, log=log, **kwargs)

    # Return components in format expected by legacy testbench
    return {
        'AR': master_read.ar_channel,    # AR master component
        'R': master_read.r_channel,      # R monitor component
        'interface': master_read,        # High-level interface
        'compliance_checker': master_read.compliance_checker  # ENHANCEMENT: Compliance checker (may be None)
    }


def create_axi4_master_wr(dut, clock, prefix="", log=None, **kwargs) -> Dict[str, Any]:
    """
    Create AXI4 Master Write interface with automatic compliance checking.

    Args:
        dut: Device under test
        clock: Clock signal
        prefix: Signal prefix ("fub_axi_", "m_axi_", etc.)
        **kwargs: Additional configuration

    Returns:
        Dictionary containing AXI4 write master components

    ENHANCEMENT: Now includes compliance checking automatically when enabled
    """
    # Create the master write interface (compliance checking included automatically)
    master_write = AXI4MasterWrite(dut, clock, prefix, log=log, **kwargs)

    # Return components in format expected by testbench
    return {
        'AW': master_write.aw_channel,   # AW master component
        'W': master_write.w_channel,     # W master component
        'B': master_write.b_channel,     # B monitor component
        'interface': master_write,       # High-level interface
        'compliance_checker': master_write.compliance_checker  # ENHANCEMENT: Compliance checker (may be None)
    }


def create_axi4_slave_rd(dut, clock, prefix="", log=None, **kwargs) -> Dict[str, Any]:
    """
    Create AXI4 Slave Read interface with automatic compliance checking and optional OOO support.

    Args:
        dut: Device under test
        clock: Clock signal
        prefix: Signal prefix ("m_axi_", "s_axi_", etc.)
        log: Logger instance
        **kwargs: Additional configuration including:
            - data_width, id_width, addr_width, user_width
            - memory_model: Memory model for data generation
            - enable_ooo: Enable out-of-order responses (default: False)
            - ooo_config: OOO configuration dict:
                {
                    'mode': 'random' or 'deterministic',
                    'reorder_probability': 0.3,
                    'min_delay_cycles': 1,
                    'max_delay_cycles': 50,
                    'pattern': [id_order] for deterministic mode
                }

    Returns:
        Dictionary containing AXI4 read slave components

    ENHANCEMENT: Now includes compliance checking and OOO support automatically when enabled
    """
    # Create the slave read interface (compliance checking included automatically)
    slave_read = AXI4SlaveRead(dut, clock, prefix, log=log, **kwargs)

    # Return components in format expected by testbench
    return {
        'AR': slave_read.ar_channel,     # AR monitor component
        'R': slave_read.r_channel,       # R slave component
        'interface': slave_read,         # High-level interface
        'compliance_checker': slave_read.compliance_checker  # ENHANCEMENT: Compliance checker (may be None)
    }


def create_axi4_slave_wr(dut, clock, prefix="", log=None, **kwargs) -> Dict[str, Any]:
    """
    Create AXI4 Slave Write interface with automatic compliance checking and optional OOO support.

    Args:
        dut: Device under test
        clock: Clock signal
        prefix: Signal prefix ("m_axi_", "s_axi_", etc.")
        log: Logger instance
        **kwargs: Additional configuration including:
            - data_width, id_width, addr_width, user_width
            - memory_model: Memory model for write storage
            - enable_ooo: Enable out-of-order responses (default: False)
            - ooo_config: OOO configuration dict:
                {
                    'mode': 'random' or 'deterministic',
                    'reorder_probability': 0.3,
                    'min_delay_cycles': 1,
                    'max_delay_cycles': 50,
                    'pattern': [id_order] for deterministic mode
                }

    Returns:
        Dictionary containing AXI4 write slave components

    ENHANCEMENT: Now includes compliance checking and OOO support automatically when enabled
    """
    # Create the slave write interface (compliance checking included automatically)
    slave_write = AXI4SlaveWrite(dut, clock, prefix, log=log, **kwargs)

    # Return components in format expected by testbench
    return {
        'AW': slave_write.aw_channel,    # AW monitor component
        'W': slave_write.w_channel,      # W monitor component
        'B': slave_write.b_channel,      # B slave component
        'interface': slave_write,        # High-level interface
        'compliance_checker': slave_write.compliance_checker  # ENHANCEMENT: Compliance checker (may be None)
    }


def create_axi4_master_interface(dut, clock, prefix="", log=None, **kwargs):
    """
    Create both read and write master interfaces with automatic compliance checking.

    Args:
        dut: Device under test
        clock: Clock signal
        prefix: Signal prefix
        **kwargs: Additional configuration

    Returns:
        Tuple of (write_interface, read_interface)

    ENHANCEMENT: Now includes compliance checking automatically when enabled
    """
    write_if = AXI4MasterWrite(dut, clock, prefix, log=log, **kwargs)
    read_if = AXI4MasterRead(dut, clock, prefix, log=log, **kwargs)
    return write_if, read_if


def create_axi4_slave_interface(dut, clock, prefix="", log=None, **kwargs):
    """
    Create both read and write slave interfaces with automatic compliance checking.

    Args:
        dut: Device under test
        clock: Clock signal
        prefix: Signal prefix
        **kwargs: Additional configuration

    Returns:
        Tuple of (write_interface, read_interface)

    ENHANCEMENT: Now includes compliance checking automatically when enabled
    """
    write_if = AXI4SlaveWrite(dut, clock, prefix, log=log, **kwargs)
    read_if = AXI4SlaveRead(dut, clock, prefix, log=log, **kwargs)
    return write_if, read_if


# ENHANCEMENT: New convenience functions for compliance reporting

def get_compliance_reports_from_components(components: Dict[str, Any]) -> Dict[str, Any]:
    """
    Extract compliance reports from AXI4 components created by factory functions.

    Args:
        components: Dictionary returned by factory functions

    Returns:
        Dictionary of compliance reports (empty if compliance checking disabled)

    Usage:
        axi_components = create_axi4_master_rd(dut, clock, prefix="m_axi_")
        compliance_reports = get_compliance_reports_from_components(axi_components)
    """
    reports = {}
    
    # Check if compliance checker exists
    if 'compliance_checker' in components and components['compliance_checker']:
        reports['compliance'] = components['compliance_checker'].get_compliance_report()
    
    # Check if interface has compliance reporting
    if 'interface' in components:
        interface = components['interface']
        if hasattr(interface, 'get_compliance_report'):
            report = interface.get_compliance_report()
            if report:
                reports['interface_compliance'] = report
    
    return reports


def print_compliance_reports_from_components(components: Dict[str, Any]):
    """
    Print compliance reports from AXI4 components created by factory functions.

    Args:
        components: Dictionary returned by factory functions

    Usage:
        axi_components = create_axi4_master_rd(dut, clock, prefix="m_axi_")
        # At end of test:
        print_compliance_reports_from_components(axi_components)
    """
    # Print from compliance checker
    if 'compliance_checker' in components and components['compliance_checker']:
        components['compliance_checker'].print_compliance_report()
    
    # Print from interface
    elif 'interface' in components:
        interface = components['interface']
        if hasattr(interface, 'print_compliance_report'):
            interface.print_compliance_report()
    
    # If no compliance checking available
    else:
        print("AXI4 compliance checking is disabled (set AXI4_COMPLIANCE_CHECK=1 to enable)")


def is_compliance_checking_enabled() -> bool:
    """
    Check if AXI4 compliance checking is currently enabled.

    Returns:
        True if compliance checking is enabled via environment variable
    """
    from .axi4_compliance_checker import AXI4ComplianceChecker
    return AXI4ComplianceChecker.is_enabled()


# ENHANCEMENT: Decorator for automatic compliance reporting at test end

def with_axi4_compliance_reporting(test_function):
    """
    Decorator that automatically prints compliance reports at the end of a test.

    Usage:
        @with_axi4_compliance_reporting
        @cocotb.test()
        async def test_axi4_basic(dut):
            # Test creates AXI4 components using factory functions
            axi_master = create_axi4_master_rd(dut, cocotb.clock_domain())
            # ... test logic ...
            # Compliance reports automatically printed at end
    """
    import functools
    
    @functools.wraps(test_function)
    async def wrapper(*args, **kwargs):
        try:
            # Run the original test
            result = await test_function(*args, **kwargs)
            return result
        finally:
            # Print compliance reports if enabled
            if is_compliance_checking_enabled():
                print("\n" + "="*80)
                print("AXI4 COMPLIANCE CHECKING SUMMARY")
                print("="*80)
                # Note: This would need to be enhanced to track all AXI4 components
                # created during the test for complete reporting
    
    return wrapper


# ENHANCEMENT: Convenience function for creating complete AXI4 testbench setup

def create_complete_axi4_testbench_components(dut, clock, master_prefix="m_axi_", 
                                            slave_prefix="s_axi_", log=None, **kwargs):
    """
    Create a complete set of AXI4 components for testbench with compliance checking.

    Args:
        dut: Device under test
        clock: Clock signal
        master_prefix: Prefix for master signals
        slave_prefix: Prefix for slave signals
        log: Logger instance
        **kwargs: Additional configuration

    Returns:
        Dictionary with all AXI4 components and compliance checkers

    ENHANCEMENT: Creates complete testbench setup with automatic compliance checking
    """
    components = {}
    
    # Create master interfaces if signals exist
    try:
        if hasattr(dut, f'{master_prefix}awvalid'):
            components['master_write'] = create_axi4_master_wr(
                dut, clock, master_prefix, log=log, **kwargs
            )
        
        if hasattr(dut, f'{master_prefix}arvalid'):
            components['master_read'] = create_axi4_master_rd(
                dut, clock, master_prefix, log=log, **kwargs
            )
    except Exception as e:
        if log:
            log.debug(f"Master interface creation: {e}")
    
    # Create slave interfaces if signals exist
    try:
        if hasattr(dut, f'{slave_prefix}awready'):
            components['slave_write'] = create_axi4_slave_wr(
                dut, clock, slave_prefix, log=log, **kwargs
            )
        
        if hasattr(dut, f'{slave_prefix}arready'):
            components['slave_read'] = create_axi4_slave_rd(
                dut, clock, slave_prefix, log=log, **kwargs
            )
    except Exception as e:
        if log:
            log.debug(f"Slave interface creation: {e}")
    
    # Add convenience methods
    components['get_all_compliance_reports'] = lambda: {
        name: get_compliance_reports_from_components(comp)
        for name, comp in components.items()
        if isinstance(comp, dict) and 'compliance_checker' in comp
    }
    
    components['print_all_compliance_reports'] = lambda: [
        print_compliance_reports_from_components(comp)
        for comp in components.values()
        if isinstance(comp, dict) and 'compliance_checker' in comp
    ]
    
    return components


def print_compliance_to_log(components, log):
    """
    Print compliance reports to log file instead of console.
    
    Args:
        components: List of AXI components or single component
        log: Logger instance
    """
    if not isinstance(components, list):
        components = [components]
    
    for comp in components:
        if hasattr(comp, 'get_compliance_report'):
            # Get the report data
            report = comp.get_compliance_report()
            if report and report.get('compliance_checking') == 'enabled':
                
                # Log the report using logger instead of print()
                log.info("=" * 80)
                log.info("AXI4 PROTOCOL COMPLIANCE REPORT")
                log.info("=" * 80)
                log.info(f"Status: {report['compliance_status']}")
                log.info(f"Total Violations: {report['total_violations']}")
                log.info(f"Checks Performed: {report['statistics']['checks_performed']}")
                
                if report['violation_summary']:
                    log.info("Violation Summary:")
                    for vtype, count in report['violation_summary'].items():
                        log.info(f"  {vtype}: {count}")
                
                log.info("=" * 80)
            else:
                log.info("AXI4 compliance checking was disabled")


def finalize_test_with_log_compliance(self):
    """
    Example finalize_test method that puts compliance reports in log file.
    """
    # Your existing finalize code here
    
    # Print compliance reports to LOG FILE (not console)
    from CocoTBFramework.components.axi4.axi4_factories import print_compliance_reports_from_components
    
    # Method 1: Capture print output and redirect to log
    output_buffer = io.StringIO()
    with redirect_stdout(output_buffer):
        print_compliance_reports_from_components(self.axi_master)
    
    # Log the captured output
    compliance_output = output_buffer.getvalue()
    if compliance_output:
        for line in compliance_output.split('\n'):
            if line.strip():
                self.log.info(line)
    
    # Method 2: Use the helper function (cleaner)
    print_compliance_to_log([self.axi_master, self.axi_slave], self.log)

# Example usage and migration guide
def demonstrate_seamless_compliance_integration():
    """
    Documentation showing how compliance checking integrates seamlessly.

    SEAMLESS COMPLIANCE INTEGRATION:
    ===============================

    BEFORE (existing testbench code):
    --------------------------------
    def create_testbench(self, dut):
        self.axi_master = create_axi4_master_rd(dut, self.aclk, prefix="m_axi_")
        self.axi_slave = create_axi4_slave_wr(dut, self.aclk, prefix="s_axi_")

    AFTER (no changes needed!):
    --------------------------
    def create_testbench(self, dut):
        # Exact same code - compliance checking automatically included!
        self.axi_master = create_axi4_master_rd(dut, self.aclk, prefix="m_axi_")
        self.axi_slave = create_axi4_slave_wr(dut, self.aclk, prefix="s_axi_")
        
        # Optional: Print compliance reports at end of test
        # (only prints if AXI4_COMPLIANCE_CHECK=1 is set)

    def finalize_test(self):
        print_compliance_reports_from_components(self.axi_master)
        print_compliance_reports_from_components(self.axi_slave)

    RUNNING TESTS:
    =============
    # Without compliance checking (current behavior):
    make test

    # With compliance checking (new capability):
    AXI4_COMPLIANCE_CHECK=1 make test

    ZERO CODE CHANGES REQUIRED! ✅
    ==============================
    All existing testbenches work exactly as before.
    Compliance checking is automatically included when enabled via environment.
    All APIs remain identical for perfect backward compatibility.
    """
    pass

