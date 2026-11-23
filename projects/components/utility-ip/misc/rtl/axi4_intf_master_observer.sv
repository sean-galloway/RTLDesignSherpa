// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2026 sean galloway

`define AXI4_INTF_MASTER_OBSERVER_PORTS_ONLY
`define AXI4_INTF_MASTER_OBSERVER_MODULE axi4_intf_master_observer
`define AXI4_INTF_MASTER_OBSERVER_WRAPPER_FULL 1'b0
`include "axi4_intf_master_observer_core.sv"
`undef AXI4_INTF_MASTER_OBSERVER_PORTS_ONLY
