# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2025 sean galloway
#
# RTL Design Sherpa - Industry-Standard RTL Design and Verification
# https://github.com/sean-galloway/RTLDesignSherpa
#
# Host programs for the Retro Legacy Blocks subsystem.
#
# The modules in this package are plain Python with no cocotb dependency:
# they speak to a `bus` object exposing `write32(addr, value)` and
# `read32(addr) -> int`. In simulation a thin adapter binds those methods
# to the testbench's APB master; on a board the same binding goes over a
# UARTAxiBridge. The shape follows the reed-solomon host programs
# (projects/fpga-systems/Genesys2/reed-solomon/build-loop/host/).
