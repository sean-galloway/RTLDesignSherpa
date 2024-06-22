from TBBase import TBBase
import cocotb
from cocotb.clock import Clock
from cocotb.triggers import RisingEdge, FallingEdge, ClockCycles, Timer
from cocotb.handle import SimHandleBase
from cocotb_bus.monitors import BusMonitor
from cocotb_bus.drivers import BusDriver
from cocotb.utils import get_sim_time
from cocotb.queue import Queue
from cocotb.result import TestFailure
from cocotb_coverage.crv import Randomized
import logging
import os
import random
from ConstrainedRandom import ConstrainedRandom
from MemoryModel import MemoryModel
from DelayRandomizer import DelayRandomizer
from dataclasses import dataclass
from collections import deque
import copy

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

@dataclass
class APBCycle:
    start_time: int
    count: int
    direction: str
    pwrite: int
    paddr: int
    pwdata: int
    pstrb: int
    prdata: int
    pprot: int
    pslverr: int

    def __eq__(self, other):
        if not isinstance(other, APBCycle):
            return NotImplemented
        if self.direction == 'WRITE':
            data_s = self.pwdata
            data_o = other.pwdata
        else:
            data_s = self.prdata
            data_o = other.prdata

        # Compare only specific fields
        return (self.direction == other.direction and
                self.paddr == other.paddr and
                data_s == data_o and
                self.pprot == other.pprot and
                self.pslverr == other.pslverr)


    def __str__(self):
        return  '\nAPB Cycle\n'+\
                f"start_time: {self.start_time}\n"+\
                f"count:      {self.count}\n"+\
                f"direction:  {self.direction}\n"+\
                f"paddr:      0x{self.paddr:08X}\n"+\
                f"pwdata:     0x{self.pwdata:08X}\n"+\
                f"pstrb:      0x{self.pstrb:08b}\n" +\
                f"prdata:     0x{self.prdata:08X}\n"+\
                f"pprot:      0x{self.pprot:04X}\n"+\
                f"pslverr:    {self.pslverr}\n"


    def formatted(self, addr_width, data_width, strb_width):
        return  '\nAPB Cycle\n'+\
                f"start_time: {self.start_time}\n"+\
                f"count:      {self.count}\n"+\
                f"direction:  {self.direction}\n"+\
                f"paddr:      0x{self.paddr:0{int(addr_width/4)}X}\n"+\
                f"pwdata:     0x{self.pwdata:0{int(data_width/4)}X}\n"+\
                f"pstrb:      0x{self.pstrb:0{strb_width}b}\n" +\
                f"prdata:     0x{self.prdata:0{int(data_width/4)}X}\n"+\
                f"pprot:      0x{self.pprot:04X}\n"+\
                f"pslverr:    {self.pslverr}\n"


class APBTransaction(Randomized):
    def __init__(self, data_width, addr_width, strb_width,
                    constraints=None):
        super().__init__()
        self.start_time = 0
        self.data_width = data_width
        self.addr_width = addr_width
        self.strb_width = strb_width
        self.addr_mask  = (strb_width - 1)
        self.count = 0
        if constraints is None:
            addr_min_hi = (4  * self.STRB_WIDTH)-1
            addr_max_lo = (4  * self.STRB_WIDTH)
            addr_max_hi = (32 * self.STRB_WIDTH)-1
            self.constraints = {
                'last':   ([(0, 0), (1, 1)],
                            [1, 1]),
                'first':  ([(0, 0), (1, 1)],
                            [1, 1]),
                'pwrite': ([(0, 0), (1, 1)],
                            [1, 1]),
                'paddr':  ([(0, addr_min_hi), (addr_max_lo, addr_max_hi)],
                            [4, 1]),
                'pstrb':  ([(15, 15), (0, 14)],
                            [4, 1]),
                'pprot':  ([(0, 0), (1, 7)],
                            [4, 1])
            }
        else:
            self.constraints = constraints

        self.last = 0
        self.first = 0
        self.pwrite = 0
        self.paddr = 0
        self.pstrb = 0
        self.pprot = 0
        self.cycle = APBCycle(
            start_time=0,
            count=0,
            direction='unknown',
            pwrite=0,
            paddr=0,
            pwdata=0,
            prdata=0,
            pstrb=0,
            pprot=0,
            pslverr=0
        )

        # Adding randomized signals with full ranges
        self.add_rand("last",   [0, 1])
        self.add_rand("first",  [0, 1])
        self.add_rand("pwrite", [0, 1])
        self.add_rand("paddr",  list(range(2**12)))
        self.add_rand("pstrb",  list(range(2**strb_width)))
        self.add_rand("pprot",  list(range(8)))


    def apply_constraints(self):
        for signal, (bins, weights) in self.constraints.items():
            choice = random.choices(bins, weights)[0]
            value = random.randint(choice[0], choice[1])
            setattr(self, signal, value)


    def set_constrained_random(self):
        self.randomize()
        self.apply_constraints()
        self.cycle.paddr     = self.paddr & ~self.addr_mask
        self.cycle.direction = pwrite[self.pwrite]
        self.cycle.pwrite    = self.pwrite
        self.cycle.pstrb     = self.pstrb
        self.cycle.pwdata    = random.randint(0, (1 << self.data_width) - 1)
        return copy.copy(self.cycle)


    def pack_cmd_packet(self):
        """
        Pack the command packet into a single integer.
        """
        return (
            (self.last         << (self.addr_width + self.data_width + self.strb_width + 5)) |
            (self.first        << (self.addr_width + self.data_width + self.strb_width + 4)) |
            (self.cycle.pwrite << (self.addr_width + self.data_width + self.strb_width + 3)) |
            (self.cycle.pprot  << (self.addr_width + self.data_width + self.strb_width)) |
            (self.cycle.pstrb  << (self.addr_width + self.data_width)) |
            (self.cycle.paddr  << self.data_width) |
            self.cycle.pwdata
        )


    def unpack_cmd_packet(self, packed_packet):
        """
        Unpack a packed command packet into its components.
        """
        self.last         = (packed_packet >> (self.addr_width + self.data_width + self.strb_width + 5)) & 0x1
        self.first        = (packed_packet >> (self.addr_width + self.data_width + self.strb_width + 4)) & 0x1
        self.cycle.pwrite = (packed_packet >> (self.addr_width + self.data_width + self.strb_width + 3)) & 0x1
        self.cycle.pprot  = (packed_packet >> (self.addr_width + self.data_width + self.strb_width)) & 0x7
        self.cycle.pstrb  = (packed_packet >> (self.addr_width + self.data_width)) & ((1 << self.strb_width) - 1)
        self.cycle.paddr  = (packed_packet >> self.data_width) & ((1 << self.addr_width) - 1)
        self.cycle.pwdata = packed_packet & ((1 << self.data_width) - 1)


    def __str__(self):
        """
        Return a string representation of the command packet for debugging.
        """
        return (f'{self.cycle.formatted(self.addr_width, self.data_width, self.strb_width)}')


class APBMonitor(BusMonitor):
    def __init__(self, entity, name, clock, signals=None,
                 bus_width=32, addr_width=12, **kwargs):

        if signals:
            self._signals = signals
        else:
            self._signals = apb_signals
            self._optional_signals = apb_optional_signals

        self.count = 0
        self.bus_width = bus_width
        BusMonitor.__init__(self, entity, name, clock, **kwargs)
        self.clock = clock
        self.name = name
        self.bus_width = bus_width
        self.addr_width = addr_width
        self.strb_width = bus_width // 8


    def is_signal_present(self, signal_name):
        return hasattr(self.bus, signal_name)


    def print(self, transaction):
        self.entity._log.debug('-' * 120)
        self.entity._log.debug(f'{self.name} - APB Transaction')
        lines = transaction.formatted(self.addr_width, self.bus_width, self.strb_width).splitlines()
        for line in lines:
            self.entity._log.debug(line)
        self.entity._log.debug('-' * 120)


    async def _monitor_recv(self):
        while True:
            await FallingEdge(self.clock)
            if self.bus.PSEL.value.integer and \
                    self.bus.PENABLE.value.integer and \
                    self.bus.PREADY.value.integer:
                start_time = get_sim_time('ns')
                address    = self.bus.PADDR.value.integer
                direction  = pwrite[self.bus.PWRITE.value.integer]
                loc_pwrite = self.bus.PWRITE.value.integer
                error      = self.bus.PSLVERR.value.integer if self.is_signal_present('PSLVERR') else 0

                if direction == 'READ':
                    data = self.bus.PRDATA.value.integer
                else:
                    data = self.bus.PWDATA.value.integer
                strb = self.bus.PSTRB.value.integer if self.is_signal_present('PSTRB') else 0
                prot = self.bus.PPROT.value.integer if self.is_signal_present('PPROT') else 0
                self.count += 1
                transaction = APBCycle(start_time, self.count, direction, loc_pwrite, address, data, strb, data, prot, error)
                # signal to the callback
                self._recv(transaction)
                self.print(transaction)


class APBSlave(BusMonitor):

    def __init__(self, entity, name, clock, registers, signals=None,
                    bus_width=32, addr_width=12, constraints=None,
                    error_overflow=False, **kwargs):
        if signals:
            self._signals = signals
        else:
            self._signals = apb_signals
            self._optional_signals = apb_optional_signals
        if constraints is None:
            self.constraints = {
                'ready': ([[0, 1], [2, 5], [6, 10]], [5, 2, 1]),
                'error': ([[0, 0], [1, 1]], [10, 0]),
            }
        else:
            self.constraints = constraints
        BusMonitor.__init__(self, entity, name, clock, **kwargs)
        self.clock          = clock
        self.addr_width     = addr_width
        self.bus_width      = bus_width
        self.strb_bits      = bus_width // 8
        self.addr_mask      = (2**self.strb_bits - 1)
        self.num_lines      = len(registers) // self.strb_bits
        self.delay_crand    = DelayRandomizer(self.constraints)
        self.count          = 0
        self.error_overflow = error_overflow
        # Create the memory model
        self.mem = MemoryModel(num_lines=self.num_lines, bytes_per_line=self.strb_bits, log=self.entity._log, preset_values=registers)
        self._sentQ = deque()

        # initialise all outputs to zero
        self.bus.PRDATA.setimmediatevalue(0)
        self.bus.PREADY.setimmediatevalue(0)
        if self.is_signal_present('PSLVERR'):
            self.bus.PSLVERR.setimmediatevalue(0)


    def is_signal_present(self, signal_name):
        return hasattr(self.bus, signal_name)


    def dump_registers(self):
        self.entity._log.info(f"APB Slave {self.name} - Register Dump:")
        self.entity._log.info(self.mem.dump())


    async def reset_bus(self):
        self.entity._log.info(f'Resetting APB Bus {self.name}')
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

            if self.bus.PSEL.value.integer:
                rand_dict = self.delay_crand.set_constrained_random()
                ready_delay = rand_dict['ready']
                slv_error = rand_dict['error']
                self.entity._log.warning(f'APB Slave Driver-{self.name}: {ready_delay=}')
                for _ in range(ready_delay):
                    await RisingEdge(self.clock)

                self.bus.PREADY.value = 1
                await Timer(200, units='ps')
                while not self.bus.PENABLE.value.integer:
                    start_time = get_sim_time('ns')
                    self.entity._log.warning(f'Waiting for penable @ {start_time}')
                    await RisingEdge(self.clock)
                    await Timer(200, units='ps')

                address    =  self.bus.PADDR.value.integer
                word_index =  (address & ~self.addr_mask)
                prot       =  self.bus.PPROT.value.integer if self.is_signal_present('PPROT') else 0
                self.count += 1

                if word_index >= self.num_lines:
                    if self.error_overflow:
                        self.entity._log.error(f'APB {self.name} - Memory overflow error: {word_index}')
                        self.bus.PSLVERR.value = 1
                    else:
                        expand = word_index - self.num_lines + 10
                        self.entity._log.warning(f'APB {self.name} - Memory overflow: {self.num_lines=} {word_index=}')
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

    def __init__(self, entity, name, clock, signals=None,
                    bus_width=32, addr_width=12, constraints=None,
                    **kwargs):
        if signals:
            self._signals = signals
        else:
            self._signals = apb_signals
            self._optional_signals = apb_optional_signals
        if constraints is None:
            self.constraints = {
                'psel':    ([[0, 0], [1, 5], [6, 10]], [5, 2, 1]),
                'penable': ([[0, 0], [1, 2]], [4, 1]),
            }
        else:
            self.constraints = constraints
        BusDriver.__init__(self, entity, name, clock, **kwargs)
        self.clock          = clock
        self.addr_width     = addr_width
        self.bus_width      = bus_width
        self.strb_bits      = bus_width // 8
        self.addr_mask      = (2**self.strb_bits - 1)
        self.delay_crand    = DelayRandomizer(self.constraints)

        # initialise all outputs to zero
        self.bus.PADDR.setimmediatevalue(0)
        self.bus.PWRITE.setimmediatevalue(0)
        self.bus.PSEL.setimmediatevalue(0)
        self.bus.PENABLE.setimmediatevalue(0)
        self.bus.PWDATA.setimmediatevalue(0)
        if self.is_signal_present('PSTRB'):
            self.bus.PSTRB.setimmediatevalue(0)


    def is_signal_present(self, signal_name):
        return hasattr(self.bus, signal_name)


    def reset_bus(self):
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

        # launch new transmit pipeline coroutine if aren't holding for and the
        #   the coroutine isn't already running.
        #   If it is running it will just collect the transactions in the
        #   queue once it gets to them.
        if not hold and not self.transmit_coroutine:
            self.transmit_coroutine = cocotb.fork(self._transmit_pipeline())


    async def _transmit_pipeline(self):

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
            if self.is_signal_present('PSTRB'):
                self.bus.PSTRB.value = 0

            rand_dict = self.delay_crand.set_constrained_random()
            psel_delay = rand_dict['psel']
            penable_delay = rand_dict['penable']

            transaction = self.transmit_queue.popleft()
            transaction.start_time = cocotb.utils.get_sim_time('ns')

            while psel_delay > 0:
                psel_delay -= 1
                await RisingEdge(self.clock)

            self.bus.PSEL.value   = 0
            self.bus.PWRITE.value = transaction.pwrite
            self.bus.PADDR.value  = transaction.address
            if self.is_signal_present('PSTRB'):
                self.bus.PSTRB.value = transaction.pstrb
            if transaction.pwrite:
                self.bus.PWDATA.value   =  transaction.pwdata
            
            await RisingEdge(self.clock)
            await Timer(200, units='ps')

            while penable_delay > 0:
                penable_delay -= 1
                await RisingEdge(self.clock)
            
            self.bus.PENABLE.value  = 1
            await Timer(200, units='ps')

            while not self.bus.PREADY.value:
                await RisingEdge(self.clock)
                await Timer(200, units='ps')
            
            # check if the slave is asserting an error
            if self.bus.PSLVERR.value:
                transaction.error = True

            # if this is a read we should sample the data
            if transaction.direction == 'READ':
                transaction.data = self.bus.PRDATA.value

            self._sentQ.append(transaction)
