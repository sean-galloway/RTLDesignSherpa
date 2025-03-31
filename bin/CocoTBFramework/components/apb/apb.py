"""APB Sequence, APB Cycle, Transaction, Monitor, Master and Slave Classes"""

from collections import deque

import cocotb
from cocotb.utils import get_sim_time
from cocotb.triggers import RisingEdge, FallingEdge, Timer
from cocotb_bus.monitors import BusMonitor
from cocotb_bus.drivers import BusDriver

from ..flex_randomizer import FlexRandomizer
from ..memory_model import MemoryModel

from .apb_packet import APBCycle


# define the PWRITE mapping
pwrite = ['READ', 'WRITE']
apb_signals = [
    "PSEL",
    "PWRITE",
    "PENABLE",
    "PADDR",
    "PWDATA",
    "PRDATA",
    "PREADY"
]
apb_optional_signals = [
    "PPROT",
    "PSLVERR",
    "PSTRB"
]


class APBMonitor(BusMonitor):
    def __init__(self, entity, title, prefix, clock, signals=None,
                 bus_width=32, addr_width=12, log=None, **kwargs):

        if signals:
            self._signals = signals
        else:
            self._signals = apb_signals + apb_optional_signals
            self._optional_signals = apb_optional_signals

        self.count = 0
        self.bus_width = bus_width
        BusMonitor.__init__(self, entity, prefix, clock, **kwargs)
        self.clock = clock
        self.title = title
        self.log = log or self.entity._log
        self.bus_width = bus_width
        self.addr_width = addr_width
        self.strb_width = bus_width // 8
        if self.is_signal_present('PPROT'):
            msg = f'Monitor {self.title} PPROT {dir(self.bus.PPROT)}'
            self.log.debug(msg)

    def is_signal_present(self, signal_name):
        # Check if the bus has the attribute and that it is not None
        return hasattr(self.bus, signal_name) and getattr(self.bus, signal_name) is not None

    def print(self, transaction):
        msg = f'{self.title} - APB Transaction: '
        msg += transaction.formatted(compact=True)
        self.log.debug(msg)

    async def _monitor_recv(self):
        while True:
            await FallingEdge(self.clock)
            await Timer(200, units='ps')
            if self.bus.PSEL.value.is_resolvable and \
                    self.bus.PSEL.value.integer and \
                    self.bus.PENABLE.value.integer and \
                    self.bus.PREADY.value.is_resolvable and \
                    self.bus.PREADY.value.integer:
                start_time = get_sim_time('ns')
                address    = self.bus.PADDR.value.integer
                direction  = pwrite[self.bus.PWRITE.value.integer]
                loc_pwrite = self.bus.PWRITE.value.integer
                error      = self.bus.PSLVERR.value.integer if self.is_signal_present('PSLVERR') else 0

                if direction == 'READ':
                    if self.bus.PRDATA.value.is_resolvable:
                        data = self.bus.PRDATA.value.integer
                    else:
                        data = self.bus.PRDATA.value
                else:
                    data = self.bus.PWDATA.value.integer
                strb = self.bus.PSTRB.value.integer if self.is_signal_present('PSTRB') else 0
                pprot = self.bus.PPROT.value.integer if self.is_signal_present('PPROT') else 0
                self.count += 1
                transaction = APBCycle(
                                    start_time=start_time,
                                    count=self.count,
                                    direction=direction,
                                    pwrite=loc_pwrite,
                                    paddr=address,
                                    pwdata=data,
                                    pstrb=strb,
                                    prdata=data,
                                    pprot=pprot,
                                    pslverr=error)
                # signal to the callback
                self._recv(transaction)
                self.print(transaction)


class APBSlave(BusMonitor):
    """AP Slave Class"""
    def __init__(self, entity, title, prefix, clock, registers, signals=None,
                    bus_width=32, addr_width=12, randomizer=None,
                    log=None, error_overflow=False, **kwargs):
        if signals:
            self._signals = signals
        else:
            self._signals = apb_signals + apb_optional_signals
            self._optional_signals = apb_optional_signals
        if randomizer is None:
            self.randomizer = FlexRandomizer({
                'ready': ([[0, 1], [2, 5], [6, 10]], [5, 2, 1]),
                'error': ([[0, 0], [1, 1]], [10, 0]),
            })
        else:
            self.randomizer = randomizer
        BusMonitor.__init__(self, entity, prefix, clock, **kwargs)
        self.clock          = clock
        self.title          = title
        self.prefix         = prefix
        self.log = log or self.entity._log
        self.addr_width     = addr_width
        self.bus_width      = bus_width
        self.strb_bits      = bus_width // 8
        self.addr_mask      = (2**self.strb_bits - 1)
        self.num_lines      = len(registers) // self.strb_bits
        self.count          = 0
        self.error_overflow = error_overflow
        # Create the memory model
        self.mem = MemoryModel(num_lines=self.num_lines, bytes_per_line=self.strb_bits, log=self.log, preset_values=registers)
        self.sentQ = deque()

        # initialise all outputs to zero
        self.bus.PRDATA.setimmediatevalue(0)
        self.bus.PREADY.setimmediatevalue(0)
        if self.is_signal_present('PSLVERR'):
            self.bus.PSLVERR.setimmediatevalue(0)
        msg = f'Slave {self.title} {dir(self.bus)}'
        # self.log.debug(msg)
        # msg = f'Slave {self.title} PADDR {dir(self.bus.PADDR)}'
        # self.log.debug(msg)
        if self.is_signal_present('PPROT'):
            msg = f'Slave {self.title} PPROT {dir(self.bus.PPROT)}'
            self.log.debug(msg)

    def set_randomizer(self, randomizer):
        self.randomizer = randomizer
        self.log.info(f"Set new randomizer for APB Slave ({self.title})")

    def is_signal_present(self, signal_name):
        # Check if the bus has the attribute and that it is not None
        return hasattr(self.bus, signal_name) and getattr(self.bus, signal_name) is not None

    def dump_registers(self):
        msg = f"APB Slave {self.title} - Register Dump:"
        self.log.info(msg)
        self.log.info(self.mem.dump())

    async def reset_bus(self):
        msg = f'Resetting APB Bus {self.title}'
        self.log.info(msg)
        self.bus.PRDATA.value = 0
        self.bus.PREADY.value = 0
        if self.is_signal_present('PSLVERR'):
            self.bus.PSLVERR.value = 0

    def reset_registers(self):
        self.mem.reset(to_preset=True)

    async def _monitor_recv(self):
        while True:
            await RisingEdge(self.clock)
            self.bus.PREADY.value = 0
            self.bus.PRDATA.value = 0
            if self.is_signal_present('PSLVERR'):
                self.bus.PSLVERR.value = 0

            await Timer(200, units='ps')
            if self.bus.PSEL.value.is_resolvable and self.bus.PSEL.value.integer:
                rand_dict = self.randomizer.next()
                ready_delay = rand_dict['ready']
                slv_error = rand_dict['error']
                for _ in range(ready_delay):
                    await RisingEdge(self.clock)

                self.bus.PREADY.value = 1
                await Timer(200, units='ps')
                while not self.bus.PENABLE.value.integer:
                    await RisingEdge(self.clock)
                    await Timer(200, units='ps')
                self._finish_recv(slv_error)

    def _finish_recv(self, slv_error):
        address    =  self.bus.PADDR.value.integer
        word_index =  (address & ~self.addr_mask)
        pprot      =  self.bus.PPROT.value.integer if self.is_signal_present('PPROT') else 0
        self.count += 1

        if word_index >= self.num_lines:
            if self.error_overflow:
                msg = f'APB {self.title} - Memory overflow error: {word_index}'
                self.log.error(msg)
                self.bus.PSLVERR.value = 1
            else:
                expand = word_index - self.num_lines + 10
                msg = f'APB {self.title} - Memory overflow: {self.num_lines=} {word_index=}'
                self.log.warning(msg)
                # Extend the self.mem array to accommodate the overflow
                self.mem.expand(expand)
                self.num_lines += expand

        if slv_error and self.is_signal_present('PSLVERR'):
            self.bus.PSLVERR.value = 1

        if self.bus.PWRITE.value.integer:  # Write transaction
            strobes   = self.bus.PSTRB.value.integer if self.is_signal_present('PSTRB') else (1 << self.strb_bits) - 1
            pwdata    = self.bus.PWDATA.value.integer
            pwdata_ba = self.mem.integer_to_bytearray(pwdata, self.strb_bits)
            self.mem.write(address & 0xFFF, pwdata_ba, strobes)

        else:  # Read transaction
            prdata_ba = self.mem.read(address & 0xFFF, self.strb_bits)
            prdata = self.mem.bytearray_to_integer(prdata_ba)
            self.bus.PRDATA.value = prdata


class APBMaster(BusDriver):
    def __init__(self, entity, title, prefix, clock, signals=None,
                    bus_width=32, addr_width=12, randomizer=None,
                    log=None, **kwargs):
        if signals:
            self._signals = signals
        else:
            self._signals = apb_signals + apb_optional_signals
            self._optional_signals = apb_optional_signals
        if randomizer is None:
            self.constraints = FlexRandomizer({
                'psel':    ([[0, 0], [1, 5], [6, 10]], [5, 2, 1]),
                'penable': ([[0, 0], [1, 2]], [4, 1]),
            })
        else:
            self.randomizer = randomizer
        BusDriver.__init__(self, entity, prefix, clock, **kwargs)
        self.title = title
        self.prefix = prefix
        self.log = log or self.entity._log
        self.clock          = clock
        self.addr_width     = addr_width
        self.bus_width      = bus_width
        self.strb_bits      = bus_width // 8
        self.addr_mask      = (2**self.strb_bits - 1)
        self.sentQ = deque()

        # initialise all outputs to zero
        self.bus.PADDR.setimmediatevalue(0)
        self.bus.PWRITE.setimmediatevalue(0)
        self.bus.PSEL.setimmediatevalue(0)
        self.bus.PENABLE.setimmediatevalue(0)
        self.bus.PWDATA.setimmediatevalue(0)
        if self.is_signal_present('PSTRB'):
            self.bus.PSTRB.setimmediatevalue(0)
        self.transmit_queue = deque()

    def set_randomizer(self, randomizer):
        self.randomizer = randomizer
        self.log.info(f"Set new randomizer for APB Slave ({self.title})")

    def is_signal_present(self, signal_name):
        # Check if the bus has the attribute and that it is not None
        return hasattr(self.bus, signal_name) and getattr(self.bus, signal_name) is not None

    async def reset_bus(self):
        # initialise the transmit queue
        self.transmit_queue     = deque()
        self.transmit_coroutine = 0
        self.bus.PSEL.value     = 0
        self.bus.PENABLE.value  = 0
        self.bus.PWRITE.value   = 0
        self.bus.PADDR.value    = 0
        self.bus.PWDATA.value   = 0
        if self.is_signal_present('PSTRB'):
            self.bus.PSTRB.value = 0
        if self.is_signal_present('PPROT'):
            self.bus.PPROT.value    = 0

    async def busy_send(self, transaction):
        '''
            Provide a send method that waits for the transaction to complete.
        '''
        await self.send(transaction)
        while (self.transfer_busy):
            await RisingEdge(self.clock)

    async def _driver_send(self, transaction, sync=True, hold=False, **kwargs):
        '''
            Append a new transaction to be transmitted
        '''
        # add new transaction
        self.transmit_queue.append(transaction)
        msg = f'Adding to the transmit_queue: {transaction.formatted(compact=True)}'
        self.log.debug(msg)

        # launch new transmit pipeline coroutine if aren't holding for and the
        #   the coroutine isn't already running.
        #   If it is running it will just collect the transactions in the
        #   queue once it gets to them.
        if not hold and not self.transmit_coroutine:
            self.transmit_coroutine = cocotb.start_soon(self._transmit_pipeline())


    async def _transmit_pipeline(self):
        """Internal function to transmit queued transactions."""
        # default values
        self.transfer_busy = True

        # while there's data in the queue keep transmitting
        while len(self.transmit_queue):
            # clear out the bus
            self.bus.PSEL.value     = 0
            self.bus.PENABLE.value  = 0
            self.bus.PWRITE.value   = 0
            self.bus.PADDR.value    = 0
            self.bus.PWDATA.value   = 0
            if self.is_signal_present('PPROT'):
                self.bus.PPROT.value = 0
            if self.is_signal_present('PSTRB'):
                self.bus.PSTRB.value = 0

            rand_dict = self.randomizer.next()
            psel_delay = rand_dict['psel']
            penable_delay = rand_dict['penable']

            transaction = self.transmit_queue.popleft()
            transaction.start_time = cocotb.utils.get_sim_time('ns')

            # finish the packet transmit
            await self._finish_xmit(transaction, psel_delay, penable_delay)

        # clear out the bus
        self.transfer_busy      = False
        self.bus.PSEL.value     = 0
        self.bus.PENABLE.value  = 0
        self.bus.PWRITE.value   = 0
        self.bus.PADDR.value    = 0
        self.bus.PWDATA.value   = 0
        if self.is_signal_present('PPROT'):
            self.bus.PPROT.value    = 0
        if self.is_signal_present('PSTRB'):
            self.bus.PSTRB.value = 0

    async def _finish_xmit(self, transaction, psel_delay, penable_delay):
        """Completes an APB transaction.

        This method sets the APB signals, waits for the ready signal,
        and handles the transaction data and error status.
        """
        for _ in range(psel_delay):
            await RisingEdge(self.clock)

        self.bus.PSEL.value   = 1
        self.bus.PWRITE.value = transaction.pwrite
        self.bus.PADDR.value  = transaction.paddr
        if self.is_signal_present('PPROT'):
            self.bus.PPROT.value  = transaction.pprot
        if self.is_signal_present('PSTRB'):
            self.bus.PSTRB.value = transaction.pstrb
        if transaction.pwrite:
            self.bus.PWDATA.value   =  transaction.pwdata

        await RisingEdge(self.clock)
        await Timer(200, units='ps')

        for _ in range(penable_delay):
            await RisingEdge(self.clock)

        self.bus.PENABLE.value  = 1
        await FallingEdge(self.clock)

        while not self.bus.PREADY.value:
            await FallingEdge(self.clock)

        # check if the slave is asserting an error
        if self.is_signal_present('PSLVERR') and self.bus.PSLVERR.value:
            transaction.error = True

        # if this is a read we should sample the data
        if transaction.direction == 'READ':
            if self.bus.PRDATA.value.is_resolvable:
                transaction.data = self.bus.PRDATA.value.integer
            else:
                transaction.data = self.bus.PRDATA.value

        self.sentQ.append(transaction)
        await RisingEdge(self.clock)
