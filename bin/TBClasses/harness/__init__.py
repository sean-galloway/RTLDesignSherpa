# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2026 sean galloway
"""Reusable UART-AXIL characterization-harness transport.

Central home for the pieces that let one host program run byte-for-byte
identically against an FPGA (pyserial) or a cocotb sim, over the shared
`uart_axil_bridge` (projects/components/converters). Used by the NexysA7
characterization flows (ddr2, stream, cdc, ...) — the register map + programs
differ per project; this transport spine is common.

  byte_channel       ByteChannel / SerialChannel / TracingChannel (host)
  uart_register_map  UartRegisterMap — by-name register access over a bridge
  cocotb_axil_bridge CocotbUartChannel + make_uart_channel (sim transport)
"""
