# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2026 sean galloway
"""Common cocotb sim bringup for the UART-AXIL characterization harness.

Every char flow's sim (ddr2, stream, cdc, ...) wraps the FULL harness (real
`uart_axil_bridge` + `<top>_csr` + engines + DUT) and drives it over a cocotb
`UARTMaster`/`UARTMonitor` so the UNMODIFIED host program runs byte-for-byte
identically against sim and FPGA (see this package's CLAUDE.md). The clock +
reset + UART-idle + traced-channel + bridge bringup is IDENTICAL across those
flows; only the backend model (DFI PHY, clock tree, ...) and the host driver
class differ. That common part lives here so projects stop re-deriving it.

Usage (project test):

    from TBClasses.harness.harness import UartSimHarness

    h = UartSimHarness(dut, clks_per_bit=CLKS_PER_BIT,
                       idle_inputs={"phy_dfi_init_complete": 0,
                                    "phy_dfi_ctrlupd_ack": 0})
    chan = await h.start()                       # clock + reset + traced channel
    dfi_slave, mem = make_my_backend_bfm(dut)    # project-specific backend
    cocotb.start_soon(assert_init_complete(dut)) # project-specific

    # Unified by-name multi-IP over the ONE bridge (even multiple pumice):
    h.add_device("harness", base=0x01_0000, regmap_file=HARNESS_REGMAP)
    h.add_device("pumice0", base=0x00_0000, regmap_file=PUMICE_REGMAP, cls=Pumice)
    h["pumice0"].write("SCHED_TUNING", force_inorder=1)
    # ...or hand h.make_bridge() to a bespoke driver (e.g. DDR2CharDriver).

The harness owns ONLY the generic transport bringup + the DeviceBus registry;
the DUT-specific backend BFM and any IP domain ops stay in the project.
`start()` returns the (optionally traced) ByteChannel to hand to the bridge.
"""

from __future__ import annotations

import inspect
import logging
from typing import Callable, Dict, Optional, Type

import cocotb
from cocotb.clock import Clock
from cocotb.triggers import ClockCycles, Timer

from TBClasses.harness.byte_channel import TracingChannel
from TBClasses.harness.cocotb_axil_bridge import make_uart_channel
from TBClasses.harness.device import Device, DeviceBus


class UartSimHarness:
    """Generic clock/reset/UART bringup for a UART-AXIL char-harness DUT.

    Parameterized by the DUT's signal names so it fits any flow. It does NOT
    know about the backend (DFI model, clock tree) or the host driver -- those
    stay in the project, which calls start() then attaches its own BFM and
    wraps the returned channel in its driver.
    """

    def __init__(self, dut, *,
                 clk: str = "aclk", clk_period_ns: float = 10,
                 resetn: str = "aresetn", active_low_reset: bool = True,
                 reset_hold_ns: float = 100, reset_release_clocks: int = 10,
                 uart_rx: str = "i_uart_rx", uart_tx: str = "o_uart_tx",
                 clks_per_bit: int = 16,
                 idle_inputs: Optional[Dict[str, int]] = None,
                 trace: bool = True,
                 log: Optional[logging.Logger] = None):
        self.dut = dut
        self._clk_name = clk
        self._clk_period_ns = clk_period_ns
        self._resetn = resetn
        self._active_low = active_low_reset
        self._reset_hold_ns = reset_hold_ns
        self._reset_release_clocks = reset_release_clocks
        self._uart_rx = uart_rx
        self._uart_tx = uart_tx
        self._clks_per_bit = clks_per_bit
        self._idle_inputs = dict(idle_inputs or {})
        self._trace = trace
        self._log = log or getattr(dut, "_log", None)
        self.clk = getattr(dut, clk)
        self.channel = None       # set by start()
        self.bridge = None        # set by make_bridge()
        self.bus = None           # DeviceBus, set on first add_device()

    def _set_idle(self) -> None:
        # UART receive line idles high; plus any DUT tie-off inputs the backend
        # BFM does not drive yet (e.g. phy_dfi_*).
        getattr(self.dut, self._uart_rx).value = 1
        for name, val in self._idle_inputs.items():
            getattr(self.dut, name).value = val

    async def start(self, *, pre_reset: Optional[Callable] = None):
        """Start the clock, drive reset, idle the inputs, and build the
        (traced) UART ByteChannel. Returns the channel.

        `pre_reset`, if given, is called after inputs are idled and before
        reset is released (may be a coroutine); use it for any extra DUT poking
        a flow needs before it comes out of reset.
        """
        cocotb.start_soon(Clock(self.clk, self._clk_period_ns, units="ns").start())
        self._set_idle()
        if pre_reset is not None:
            res = pre_reset()
            if inspect.isawaitable(res):
                await res

        rn = getattr(self.dut, self._resetn)
        rn.value = 0 if self._active_low else 1
        await Timer(self._reset_hold_ns, units="ns")
        rn.value = 1 if self._active_low else 0
        await ClockCycles(self.clk, self._reset_release_clocks)

        inner = make_uart_channel(self.dut, self.clk, self._clks_per_bit,
                                  rx_signal=self._uart_rx,
                                  tx_signal=self._uart_tx, log=self._log)
        self.channel = TracingChannel(inner) if self._trace else inner
        return self.channel

    def make_bridge(self, factory: Optional[Callable] = None):
        """Build the AXIL bridge over the channel. `factory(channel)` lets the
        caller pick the bridge class (default: the shared UARTAxiBridge, imported
        lazily so this module has no hard dependency on the converters project)."""
        if self.channel is None:
            raise RuntimeError("call start() before make_bridge()")
        if factory is None:
            from uart_axi_bridge import UARTAxiBridge   # converters/bin on sys.path
            factory = lambda ch: UARTAxiBridge(channel=ch)   # noqa: E731
        self.bridge = factory(self.channel)
        return self.bridge

    # ----- unified by-name multi-IP registry (over the one bridge) ---------
    def add_device(self, name: str, *, base: int, regmap_file: str,
                   cls: Type[Device] = Device, **kwargs) -> Device:
        """Attach a named PeakRDL IP instance on the shared bridge (building the
        bridge with the default factory if not done). The same IP may be added
        multiple times at different bases (e.g. pumice0/pumice1). Returns the
        Device (or `cls` subclass) for by-name register access."""
        if self.bridge is None:
            self.make_bridge()
        if self.bus is None:
            self.bus = DeviceBus(self.bridge, log=self._log)
        return self.bus.add(name, base=base, regmap_file=regmap_file, cls=cls,
                            **kwargs)

    def device(self, name: str) -> Device:
        return self.bus.device(name)

    def __getitem__(self, name: str) -> Device:
        return self.bus[name]

    # ----- convenience passthroughs to the traced channel ------------------
    def tx_bytes(self) -> bytes:
        """Host->DUT bytes captured so far (requires trace=True)."""
        return self.channel.tx_bytes()

    def wire_bytes(self) -> bytes:
        return self.channel.wire_bytes()
