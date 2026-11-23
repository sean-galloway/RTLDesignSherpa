// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2026 sean galloway

`define AXI4_INTF_SLAVE_OBSERVER_PORTS_ONLY
`define AXI4_INTF_SLAVE_OBSERVER_MODULE axi4_intf_slave_observer_full
`define AXI4_INTF_SLAVE_OBSERVER_WRAPPER_FULL 1'b1
`include "axi4_intf_slave_observer_core.sv"
`undef AXI4_INTF_SLAVE_OBSERVER_PORTS_ONLY
