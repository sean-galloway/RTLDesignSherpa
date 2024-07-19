# APB_XBAR

The `apb_xbar` module is a parameterized APB crossbar that interconnects multiple APB master interfaces to multiple APB slave interfaces. This crossbar allows APB masters to communicate with any of the APB slaves, as long as the address falls within the decoded region for that slave. This is a heavy weight cross bar. It should work even at higher frequencies or when there is more distance between the APB ports.

## Module Parameters

- `M`: Number of APB masters.
- `S`: Number of APB slaves.
- `ADDR_WIDTH`: Width of the address bus.
- `DATA_WIDTH`: Width of the data bus.
- `STRB_WIDTH`: Width of the strobe signal. Typically, this is `DATA_WIDTH/8`.
- `MAX_THRESH`: Maximum threshold value for the weighted round-robin arbitration.
- `SKID_DEPTH`: The depth of the skid buffers used within the module.

Other internal parameters are derived from the above, such as `MID` for master ID width, `SID` for slave ID width, and various widths for command and response packets (`SLVCPW`, `SLVRPW`, `MSTCPW`, `MSTRPW`).

## Ports

### Clock and Reset

- `aclk`: Clock signal.
- `aresetn`: Active low asynchronous reset signal.

### Slave Interface Configuration

- `SLAVE_ENABLE`: Decoder enable signal for each slave.
- `SLAVE_ADDR_BASE`: Base address for each slave.
- `SLAVE_ADDR_LIMIT`: Limit address for each slave.
- `MST_THRESHOLDS`: Thresholds for the master round-robin arbiters.
- `SLV_THRESHOLDS`: Thresholds for the slave round-robin arbiters.

### Master and Slave APB Interface Signals

Each master interface (`m_apb_*`) and slave interface (`s_apb_*`) consists of standard APB signals like `psel`, `penable`, `pwrite`, `pprot`, `paddr`, `pwdata`, `pstrb`, `prdata`, and `pslverr`.

## Internal Functionality

- The crossbar uses weighted round-robin arbitration to select which masters get access to the slaves.
- Address decoding logic determines which slave a master is targeting based on the master's address.
- Skid buffers and stubs are used to handle communication nuances between the APB protocol and the internal logic, ensuring stability and correctness when dealing with back-pressure.
- The crossbar generates slave and master select signals and performs mux/demux operations to route command and response packets between the APB master and slave interfaces.
- Debugging information is periodically written to a log file (`debug_log.txt`).

## Notes

This crossbar implementation assumes that all APB signals are active high, which is standard for APB protocol. Special attention should be paid to correctly configure address base and limit for each slave to avoid address conflicts.

## Debugging

- The module writes to a debugging log at every negative clock edge, capturing the state of various signals for traceability and analysis.
- The potential for creating the log file exists, and if not successful, the simulation will finish.

Remember to manage the potential growth of the debug log file and its effect on the simulation environment.

---

[Return to Index](index.md)

---
