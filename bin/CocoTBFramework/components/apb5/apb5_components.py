# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2025 sean galloway
#
# RTL Design Sherpa - Industry-Standard RTL Design and Verification
# https://github.com/sean-galloway/RTLDesignSherpa
#
# Module: APB5Components
# Purpose: APB5 Monitor, Master and Slave BFM Classes
#
# Documentation: bin/CocoTBFramework/README.md
# Subsystem: framework
#
# Author: sean galloway
# Created: 2025-12-21

"""APB5 Monitor, Master and Slave BFM Classes with AMBA5 extensions."""

from collections import deque

import cocotb
from cocotb.utils import get_sim_time
from cocotb.triggers import RisingEdge, FallingEdge, Timer
from cocotb_bus.monitors import BusMonitor
from cocotb_bus.drivers import BusDriver

from ..shared.flex_randomizer import FlexRandomizer
from ..shared.memory_model import MemoryModel

from .apb5_packet import APB5Packet


# Define the PWRITE mapping
pwrite = ['READ', 'WRITE']

# APB5 signals - APB4 base signals plus APB5 extensions
apb5_signals = [
    "PSEL",
    "PWRITE",
    "PENABLE",
    "PADDR",
    "PWDATA",
    "PRDATA",
    "PREADY"
]

apb5_optional_signals = [
    "PPROT",
    "PSLVERR",
    "PSTRB",
    # APB5 extensions
    "PAUSER",
    "PWUSER",
    "PRUSER",
    "PBUSER",
    "PWAKEUP",
    # Parity signals (optional)
    "PWDATAPARITY",
    "PADDRPARITY",
    "PCTRLPARITY",
    "PRDATAPARITY",
    "PREADYPARITY",
    "PSLVERRPARITY",
]


class APB5Monitor(BusMonitor):
    """APB5 Monitor with AMBA5 extension support."""

    def __init__(self, entity, title, prefix, clock, signals=None,
                 bus_width=32, addr_width=12,
                 auser_width=4, wuser_width=4, ruser_width=4, buser_width=4,
                 log=None, **kwargs):

        if signals:
            self._signals = signals
        else:
            self._signals = apb5_signals + apb5_optional_signals
            self._optional_signals = apb5_optional_signals

        self.count = 0
        self.bus_width = bus_width

        # Normalize prefix
        prefix = prefix.rstrip('_')

        BusMonitor.__init__(self, entity, prefix, clock, **kwargs)
        self.clock = clock
        self.title = title
        self.log = log or self.entity._log
        self.bus_width = bus_width
        self.addr_width = addr_width
        self.strb_width = bus_width // 8
        self.auser_width = auser_width
        self.wuser_width = wuser_width
        self.ruser_width = ruser_width
        self.buser_width = buser_width

    def is_signal_present(self, signal_name):
        """Check if a signal is present on the bus."""
        return (hasattr(self.bus, signal_name) and
                getattr(self.bus, signal_name) is not None)

    def print(self, transaction):
        """Print transaction for debug."""
        msg = f'{self.title} - APB5 Transaction #{self.count}: '
        msg += transaction.formatted(compact=True)
        self.log.debug(msg)

    async def _monitor_recv(self):
        """Monitor APB5 transactions."""
        prev_psel = 0
        prev_penable = 0
        prev_pready = 0

        while True:
            await FallingEdge(self.clock)
            await Timer(200, units='ps')

            # Sample current bus state
            curr_psel = (self.bus.PSEL.value.integer
                         if self.bus.PSEL.value.is_resolvable else 0)
            curr_penable = self.bus.PENABLE.value.integer
            curr_pready = (self.bus.PREADY.value.integer
                           if self.bus.PREADY.value.is_resolvable else 0)

            # APB transaction completion detection
            transaction_complete = curr_psel and curr_penable and curr_pready
            valid_edge = (transaction_complete and
                          (not prev_pready or not prev_penable))

            if valid_edge:
                start_time = get_sim_time('ns')
                address = self.bus.PADDR.value.integer
                direction = pwrite[self.bus.PWRITE.value.integer]
                loc_pwrite = self.bus.PWRITE.value.integer
                error = (self.bus.PSLVERR.value.integer
                         if self.is_signal_present('PSLVERR') else 0)

                if direction == 'READ':
                    if self.bus.PRDATA.value.is_resolvable:
                        data = self.bus.PRDATA.value.integer
                    else:
                        data = self.bus.PRDATA.value
                else:
                    data = self.bus.PWDATA.value.integer

                strb = (self.bus.PSTRB.value.integer
                        if self.is_signal_present('PSTRB') else 0)
                pprot = (self.bus.PPROT.value.integer
                         if self.is_signal_present('PPROT') else 0)

                # APB5 extensions
                pauser = (self.bus.PAUSER.value.integer
                          if self.is_signal_present('PAUSER') else 0)
                pwuser = (self.bus.PWUSER.value.integer
                          if self.is_signal_present('PWUSER') else 0)
                pruser = (self.bus.PRUSER.value.integer
                          if self.is_signal_present('PRUSER') else 0)
                pbuser = (self.bus.PBUSER.value.integer
                          if self.is_signal_present('PBUSER') else 0)
                wakeup = (self.bus.PWAKEUP.value.integer
                          if self.is_signal_present('PWAKEUP') else 0)

                self.count += 1

                # Create APB5Packet
                transaction = APB5Packet(
                    data_width=self.bus_width,
                    addr_width=self.addr_width,
                    strb_width=self.strb_width,
                    auser_width=self.auser_width,
                    wuser_width=self.wuser_width,
                    ruser_width=self.ruser_width,
                    buser_width=self.buser_width,
                    start_time=start_time,
                    count=self.count,
                    pwrite=loc_pwrite,
                    paddr=address,
                    pwdata=data if direction == 'WRITE' else 0,
                    prdata=data if direction == 'READ' else 0,
                    pstrb=strb,
                    pprot=pprot,
                    pslverr=error,
                    pauser=pauser,
                    pwuser=pwuser,
                    pruser=pruser,
                    pbuser=pbuser,
                    wakeup=wakeup,
                )

                self._recv(transaction)
                self.print(transaction)

            # Update previous state
            prev_psel = curr_psel
            prev_penable = curr_penable
            prev_pready = curr_pready


class APB5Slave(BusMonitor):
    """APB5 Slave BFM with AMBA5 extension support."""

    def __init__(self, entity, title, prefix, clock, registers, signals=None,
                 bus_width=32, addr_width=12,
                 auser_width=4, wuser_width=4, ruser_width=4, buser_width=4,
                 randomizer=None, log=None, error_overflow=False,
                 wakeup_generator=None, **kwargs):

        if signals:
            self._signals = signals
        else:
            self._signals = apb5_signals + apb5_optional_signals
            self._optional_signals = apb5_optional_signals

        if randomizer is None:
            self.randomizer = FlexRandomizer({
                'ready': ([(0, 1), (2, 5), (6, 10)], [5, 2, 1]),
                'error': ([(0, 0), (1, 1)], [10, 0]),
                'pruser': ([(0, (1 << ruser_width) - 1)], [1]),
                'pbuser': ([(0, (1 << buser_width) - 1)], [1]),
            })
        else:
            self.randomizer = randomizer

        prefix = prefix.rstrip('_')

        BusMonitor.__init__(self, entity, prefix, clock, **kwargs)
        self.clock = clock
        self.title = title
        self.prefix = prefix
        self.log = log or self.entity._log
        self.addr_width = addr_width
        self.bus_width = bus_width
        self.strb_bits = bus_width // 8
        self.addr_mask = (2**self.strb_bits - 1)
        self.num_lines = len(registers) // self.strb_bits
        self.count = 0
        self.error_overflow = error_overflow
        self.auser_width = auser_width
        self.wuser_width = wuser_width
        self.ruser_width = ruser_width
        self.buser_width = buser_width
        self.wakeup_generator = wakeup_generator

        # Create memory model
        self.mem = MemoryModel(
            num_lines=self.num_lines,
            bytes_per_line=self.strb_bits,
            log=self.log,
            preset_values=registers
        )
        self.sentQ = deque()

        # Initialize outputs
        self.bus.PRDATA.setimmediatevalue(0)
        self.bus.PREADY.setimmediatevalue(0)
        if self.is_signal_present('PSLVERR'):
            self.bus.PSLVERR.setimmediatevalue(0)
        if self.is_signal_present('PRUSER'):
            self.bus.PRUSER.setimmediatevalue(0)
        if self.is_signal_present('PBUSER'):
            self.bus.PBUSER.setimmediatevalue(0)
        if self.is_signal_present('PWAKEUP'):
            self.bus.PWAKEUP.setimmediatevalue(0)

        msg = f'APB5 Slave {self.title} initialized'
        self.log.debug(msg)

    def is_signal_present(self, signal_name):
        """Check if a signal is present on the bus."""
        return (hasattr(self.bus, signal_name) and
                getattr(self.bus, signal_name) is not None)

    def print(self, transaction):
        """Print transaction for debug."""
        msg = f'{self.title} - APB5 Transaction #{self.count}: '
        msg += transaction.formatted(compact=True)
        self.log.debug(msg)

    async def set_wakeup(self, value):
        """Set the PWAKEUP signal."""
        if self.is_signal_present('PWAKEUP'):
            self.bus.PWAKEUP.value = value

    async def _monitor_recv(self):
        """Handle APB5 slave transactions."""
        prev_psel = 0
        prev_penable = 0

        while True:
            await RisingEdge(self.clock)

            curr_psel = (self.bus.PSEL.value.integer
                         if self.bus.PSEL.value.is_resolvable else 0)
            curr_penable = (self.bus.PENABLE.value.integer
                            if self.bus.PENABLE.value.is_resolvable else 0)

            # Detect setup phase (PSEL without PENABLE)
            if curr_psel and not curr_penable:
                pass  # Setup phase - no action needed

            # Detect access phase start (PSEL + PENABLE rising)
            if curr_psel and curr_penable and not prev_penable:
                # Get random delays and user signal values
                rand_values = self.randomizer.next()
                ready_delay = rand_values.get('ready', 0)
                error_val = rand_values.get('error', 0)
                pruser = rand_values.get('pruser', 0)
                pbuser = rand_values.get('pbuser', 0)

                address = self.bus.PADDR.value.integer
                direction = pwrite[self.bus.PWRITE.value.integer]
                loc_pwrite = self.bus.PWRITE.value.integer

                # Calculate memory line
                line = (address & ~self.addr_mask) // self.strb_bits

                # Check for address overflow
                if line >= self.num_lines and self.error_overflow:
                    error_val = 1

                # Handle read/write
                if direction == 'WRITE':
                    wdata = self.bus.PWDATA.value.integer
                    strb = (self.bus.PSTRB.value.integer
                            if self.is_signal_present('PSTRB') else
                            (1 << self.strb_bits) - 1)

                    if line < self.num_lines:
                        self.mem.write(line, wdata, strb)
                    rdata = 0
                else:
                    if line < self.num_lines:
                        rdata = self.mem.read(line)
                    else:
                        rdata = 0
                    wdata = 0
                    strb = 0

                # Get APB5 input user signals
                pauser = (self.bus.PAUSER.value.integer
                          if self.is_signal_present('PAUSER') else 0)
                pwuser = (self.bus.PWUSER.value.integer
                          if self.is_signal_present('PWUSER') else 0)
                pprot = (self.bus.PPROT.value.integer
                         if self.is_signal_present('PPROT') else 0)

                # Apply ready delay
                for _ in range(ready_delay):
                    await RisingEdge(self.clock)

                # Set outputs
                self.bus.PRDATA.value = rdata
                self.bus.PREADY.value = 1
                if self.is_signal_present('PSLVERR'):
                    self.bus.PSLVERR.value = error_val
                if self.is_signal_present('PRUSER'):
                    self.bus.PRUSER.value = pruser
                if self.is_signal_present('PBUSER'):
                    self.bus.PBUSER.value = pbuser

                self.count += 1

                # Create transaction record
                transaction = APB5Packet(
                    data_width=self.bus_width,
                    addr_width=self.addr_width,
                    strb_width=self.strb_bits,
                    auser_width=self.auser_width,
                    wuser_width=self.wuser_width,
                    ruser_width=self.ruser_width,
                    buser_width=self.buser_width,
                    start_time=get_sim_time('ns'),
                    count=self.count,
                    pwrite=loc_pwrite,
                    paddr=address,
                    pwdata=wdata,
                    prdata=rdata,
                    pstrb=strb,
                    pprot=pprot,
                    pslverr=error_val,
                    pauser=pauser,
                    pwuser=pwuser,
                    pruser=pruser,
                    pbuser=pbuser,
                )

                self.sentQ.append(transaction)
                self._recv(transaction)
                self.print(transaction)

                # Wait for transaction completion
                await RisingEdge(self.clock)
                self.bus.PREADY.value = 0
                if self.is_signal_present('PSLVERR'):
                    self.bus.PSLVERR.value = 0

            prev_psel = curr_psel
            prev_penable = curr_penable


class APB5Master(BusDriver):
    """APB5 Master BFM with AMBA5 extension support."""

    _signals = apb5_signals
    _optional_signals = apb5_optional_signals

    def __init__(self, entity, title, prefix, clock,
                 bus_width=32, addr_width=12,
                 auser_width=4, wuser_width=4, ruser_width=4, buser_width=4,
                 log=None, **kwargs):

        prefix = prefix.rstrip('_')

        BusDriver.__init__(self, entity, prefix, clock, **kwargs)
        self.clock = clock
        self.title = title
        self.prefix = prefix
        self.log = log or self.entity._log
        self.bus_width = bus_width
        self.addr_width = addr_width
        self.strb_bits = bus_width // 8
        self.auser_width = auser_width
        self.wuser_width = wuser_width
        self.ruser_width = ruser_width
        self.buser_width = buser_width
        self.count = 0
        self.sentQ = deque()

        # Initialize outputs
        self.bus.PSEL.setimmediatevalue(0)
        self.bus.PENABLE.setimmediatevalue(0)
        self.bus.PWRITE.setimmediatevalue(0)
        self.bus.PADDR.setimmediatevalue(0)
        self.bus.PWDATA.setimmediatevalue(0)
        if self.is_signal_present('PSTRB'):
            self.bus.PSTRB.setimmediatevalue(0)
        if self.is_signal_present('PPROT'):
            self.bus.PPROT.setimmediatevalue(0)
        if self.is_signal_present('PAUSER'):
            self.bus.PAUSER.setimmediatevalue(0)
        if self.is_signal_present('PWUSER'):
            self.bus.PWUSER.setimmediatevalue(0)

        msg = f'APB5 Master {self.title} initialized'
        self.log.debug(msg)

    def is_signal_present(self, signal_name):
        """Check if a signal is present on the bus."""
        return (hasattr(self.bus, signal_name) and
                getattr(self.bus, signal_name) is not None)

    async def send(self, transaction):
        """Send an APB5 transaction."""
        await self._driver_send(transaction, None)

    async def _driver_send(self, transaction, sync=True, **kwargs):
        """Drive an APB5 transaction on the bus."""
        if sync:
            await RisingEdge(self.clock)

        # Setup phase
        self.bus.PSEL.value = 1
        self.bus.PENABLE.value = 0
        self.bus.PWRITE.value = transaction.fields['pwrite']
        self.bus.PADDR.value = transaction.fields['paddr']
        self.bus.PWDATA.value = transaction.fields['pwdata']

        if self.is_signal_present('PSTRB'):
            self.bus.PSTRB.value = transaction.fields['pstrb']
        if self.is_signal_present('PPROT'):
            self.bus.PPROT.value = transaction.fields['pprot']
        if self.is_signal_present('PAUSER'):
            self.bus.PAUSER.value = transaction.fields.get('pauser', 0)
        if self.is_signal_present('PWUSER'):
            self.bus.PWUSER.value = transaction.fields.get('pwuser', 0)

        # Access phase
        await RisingEdge(self.clock)
        self.bus.PENABLE.value = 1

        # Wait for PREADY
        while True:
            await RisingEdge(self.clock)
            if self.bus.PREADY.value.integer:
                break

        # Capture response
        if not transaction.fields['pwrite']:
            transaction.fields['prdata'] = self.bus.PRDATA.value.integer

        if self.is_signal_present('PSLVERR'):
            transaction.fields['pslverr'] = self.bus.PSLVERR.value.integer
        if self.is_signal_present('PRUSER'):
            transaction.fields['pruser'] = self.bus.PRUSER.value.integer
        if self.is_signal_present('PBUSER'):
            transaction.fields['pbuser'] = self.bus.PBUSER.value.integer
        if self.is_signal_present('PWAKEUP'):
            transaction.fields['wakeup'] = self.bus.PWAKEUP.value.integer

        transaction.end_time = get_sim_time('ns')
        self.count += 1

        # Deassert
        self.bus.PSEL.value = 0
        self.bus.PENABLE.value = 0

        self.sentQ.append(transaction)

        msg = f'{self.title} - APB5 Transaction #{self.count}: '
        msg += transaction.formatted(compact=True)
        self.log.debug(msg)

    async def write(self, address, data, strb=None, pprot=0, pauser=0, pwuser=0):
        """Perform an APB5 write transaction."""
        if strb is None:
            strb = (1 << self.strb_bits) - 1

        transaction = APB5Packet(
            data_width=self.bus_width,
            addr_width=self.addr_width,
            strb_width=self.strb_bits,
            auser_width=self.auser_width,
            wuser_width=self.wuser_width,
            ruser_width=self.ruser_width,
            buser_width=self.buser_width,
            pwrite=1,
            paddr=address,
            pwdata=data,
            pstrb=strb,
            pprot=pprot,
            pauser=pauser,
            pwuser=pwuser,
            start_time=get_sim_time('ns'),
        )

        await self.send(transaction)
        return transaction

    async def read(self, address, pprot=0, pauser=0):
        """Perform an APB5 read transaction."""
        transaction = APB5Packet(
            data_width=self.bus_width,
            addr_width=self.addr_width,
            strb_width=self.strb_bits,
            auser_width=self.auser_width,
            wuser_width=self.wuser_width,
            ruser_width=self.ruser_width,
            buser_width=self.buser_width,
            pwrite=0,
            paddr=address,
            pprot=pprot,
            pauser=pauser,
            start_time=get_sim_time('ns'),
        )

        await self.send(transaction)
        return transaction
