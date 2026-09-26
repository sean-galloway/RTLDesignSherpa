# rtl/amba/monitor-lite

The AXI transaction monitor rebuilt for gate count and timing (amba/monitor-lite TASK-001).
One module, `axi_monitor_lite`, selected inside every monitored wrapper by
`MONITOR_LITE = 1`; same packets, same monbus, 677 LUTs against `axi_monitor_base`'s 3,249 in
the same bridge fixture (21%). Page: [axi_monitor_lite.md](axi_monitor_lite.md).
Filelist: `rtl/amba/filelists/axi_monitor_lite.f`.
