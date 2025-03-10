"""APB Sequence, APB Cycle, Transaction, Monitor, Master and Slave Classes"""

import copy
from dataclasses import dataclass, field
from collections import deque
import random
from typing import List, Tuple, Dict, Optional

import cocotb
from cocotb.utils import get_sim_time
from cocotb.triggers import RisingEdge, FallingEdge, Timer
from cocotb_bus.monitors import BusMonitor
from cocotb_bus.drivers import BusDriver
from cocotb_coverage.crv import Randomized

from .flex_randomizer import FlexRandomizer
from .memory_model import MemoryModel

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
class APBSequence:
    """Configuration for test patterns"""
    # Test name
    name: str = "basic"
    
    # Transaction sequence - list of writes (True) and reads (False)
    # Examples: [True, False] for alternating write-read
    #           [True, True, ..., False, False] for all writes then all reads
    pwrite_seq: List[bool] = field(default_factory=list)
    
    # Address sequence - list of addresses to use
    # If shorter than pwrite_seq, will cycle through the addresses
    addr_seq: List[int] = field(default_factory=list)
    
    # Data sequence - list of data values to use for writes
    # If shorter than number of writes, will cycle through the data values
    data_seq: List[int] = field(default_factory=list)
    
    # Strobe sequence - list of strobe masks to use for writes
    # If shorter than number of writes, will cycle through the strobe masks
    strb_seq: List[int] = field(default_factory=list)
    
    # Timing
    inter_cycle_delays: List[int] = field(default_factory=list)  # Delays between cycles
    
    # Master timing randomizer
    master_randomizer: Optional[Dict] = None
    slave_randomizer: Optional[Tuple] = None
    other_randomizer: Optional[Tuple] = None
    
    # Selection mode
    use_random_selection: bool = False  # If True, randomly select from sequences
    
    # Verification
    verify_data: bool = True
    
    def __post_init__(self):
        """Initialize iterators for sequences"""
        self.pwrite_iter = iter(self.pwrite_seq)
        self.addr_iter = iter(self.addr_seq)
        self.data_iter = iter(self.data_seq)
        self.strb_iter = iter(self.strb_seq)
        self.delay_iter = iter(self.inter_cycle_delays)

    def reset_iterators(self):
        """Reset all iterators to the beginning"""
        self.pwrite_iter = iter(self.pwrite_seq)
        self.addr_iter = iter(self.addr_seq)
        self.data_iter = iter(self.data_seq)
        self.strb_iter = iter(self.strb_seq)
        self.delay_iter = iter(self.inter_cycle_delays)
    
    def next_pwrite(self) -> bool:
        """Get next write/read operation"""
        if self.use_random_selection:
            return random.choice(self.pwrite_seq)
        try:
            return next(self.pwrite_iter)
        except StopIteration:
            self.pwrite_iter = iter(self.pwrite_seq)
            return next(self.pwrite_iter)
    
    def next_addr(self) -> int:
        """Get next address"""
        if self.use_random_selection:
            return random.choice(self.addr_seq)
        try:
            return next(self.addr_iter)
        except StopIteration:
            self.addr_iter = iter(self.addr_seq)
            return next(self.addr_iter)
    
    def next_data(self) -> int:
        """Get next data value"""
        if self.use_random_selection:
            return random.choice(self.data_seq)
        try:
            return next(self.data_iter)
        except StopIteration:
            self.data_iter = iter(self.data_seq)
            return next(self.data_iter)
    
    def next_strb(self) -> int:
        """Get next strobe mask"""
        if self.use_random_selection:
            return random.choice(self.strb_seq)
        try:
            return next(self.strb_iter)
        except StopIteration:
            self.strb_iter = iter(self.strb_seq)
            return next(self.strb_iter)
    
    def next_delay(self) -> int:
        """Get next inter-cycle delay"""
        if not self.inter_cycle_delays:
            return 0

        if self.use_random_selection:
            return random.choice(self.inter_cycle_delays)
        try:
            return next(self.delay_iter)
        except StopIteration:
            self.delay_iter = iter(self.inter_cycle_delays)
            return next(self.delay_iter)


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

    def _format_data(self, src, data, data_width):
        if isinstance(data, int):
            # Format prdata as an integer if it is resolvable
            return f"{src}:     0x{data:0{int(data_width / 4)}X}\n"
        else:
            # Format prdata as a binary string if it contains 'X' values
            return f"{src}:     {data}\n"

    def __str__(self):
        prdata = self._format_data('prdata', self.prdata, 32)
        pwdata = self._format_data('pwdata', self.pwdata, 32)
        return  ('\nAPB Cycle\n'
                f"start_time: {self.start_time}\n"
                f"count:      {self.count}\n"
                f"direction:  {self.direction}\n"
                f"paddr:      0x{self.paddr:08X}\n"
                f"{pwdata}\n"
                f"pstrb:      0x{self.pstrb:08b}\n"
                f"{prdata}\n"
                f"pprot:      0x{self.pprot:04X}\n"
                f"pslverr:    {self.pslverr}\n"
        )

    def formatted(self, addr_width, data_width, strb_width):
        prdata = self._format_data('prdata', self.prdata, data_width)
        pwdata = self._format_data('pwdata', self.pwdata, data_width)
        return  ('\nAPB Cycle\n'
                f"start_time: {self.start_time}\n"
                f"count:      {self.count}\n"
                f"direction:  {self.direction}\n"
                f"paddr:      0x{self.paddr:0{int(addr_width/4)}X}\n"
                f"{pwdata}\n"
                f"pstrb:      0x{self.pstrb:0{strb_width}b}\n"
                f"{prdata}\n"
                f"pprot:      0x{self.pprot:04X}\n"
                f"pslverr:    {self.pslverr}\n"
        )


class APBTransaction(Randomized):
    def __init__(self, data_width, addr_width, strb_width,
                    randomizer=None):
        super().__init__()
        self.start_time = 0
        self.data_width = data_width
        self.addr_width = addr_width
        self.strb_width = strb_width
        self.addr_mask  = (strb_width - 1)
        self.count = 0
        if randomizer is None:
            addr_min_hi = (4  * self.strb_width)-1
            addr_max_lo = (4  * self.strb_width)
            addr_max_hi = (32 * self.strb_width)-1
            self.randomizer =  FlexRandomizer({
                'pwrite': ([(0, 0), (1, 1)],
                            [1, 1]),
                'paddr':  ([(0, addr_min_hi), (addr_max_lo, addr_max_hi)],
                            [4, 1]),
                'pstrb':  ([(15, 15), (0, 14)],
                            [4, 1]),
                'pprot':  ([(0, 0), (1, 7)],
                            [4, 1])
            })
        else:
            self.randomizer = randomizer

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
        self.add_rand("pwrite", [0, 1])
        self.add_rand("paddr",  list(range(2**12)))
        self.add_rand("pstrb",  list(range(2**strb_width)))
        self.add_rand("pprot",  list(range(8)))

    def next(self):
        self.randomize()
        value_dict = self.randomizer.next()
        self.cycle.paddr     = value_dict['paddr'] & ~self.addr_mask
        self.cycle.direction = pwrite[value_dict['pwrite']]
        self.cycle.pwrite    = value_dict['pwrite']
        self.cycle.pstrb     = value_dict['pstrb']
        self.cycle.pwdata    = random.randint(0, (1 << self.data_width) - 1)
        return copy.copy(self.cycle)

    def __str__(self):
        """
        Return a string representation of the command packet for debugging.
        """
        return (f'{self.cycle.formatted(self.addr_width, self.data_width, self.strb_width)}')


class APBMonitor(BusMonitor):
    def __init__(self, entity, name, clock, signals=None,
                 bus_width=32, addr_width=12, log=None, **kwargs):

        if signals:
            self._signals = signals
        else:
            self._signals = apb_signals + apb_optional_signals
            self._optional_signals = apb_optional_signals

        self.count = 0
        self.bus_width = bus_width
        BusMonitor.__init__(self, entity, name, clock, **kwargs)
        self.clock = clock
        self.name = name
        self.log = log or self.entity._log
        self.bus_width = bus_width
        self.addr_width = addr_width
        self.strb_width = bus_width // 8

    def is_signal_present(self, signal_name):
        # Check if the bus has the attribute and that it is not None
        return hasattr(self.bus, signal_name) and getattr(self.bus, signal_name) is not None

    def print(self, transaction):
        self.log.debug('-' * 120)
        msg = f'{self.name} - APB Transaction'
        self.log.debug(msg)
        lines = transaction.formatted(self.addr_width, self.bus_width, self.strb_width).splitlines()
        for line in lines:
            self.log.debug(line)
        self.log.debug('-' * 120)

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
                prot = self.bus.PPROT.value.integer if self.is_signal_present('PPROT') else 0
                self.count += 1
                transaction = APBCycle(start_time, self.count, direction, loc_pwrite, address, data, strb, data, prot, error)
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
        self.log.warning(msg)
        msg = f'Slave {self.title} PADDR {dir(self.bus.PADDR)}'
        self.log.warning(msg)
        if self.is_signal_present('PPROT'):
            msg = f'Slave {self.title} PPROT {dir(self.bus.PPROT)}'
            self.log.warning(msg)

    def set_randomizer(self, randomizer):
        self.randomizer = randomizer
        self.log.info(f"Set new randomizer for APB Slave ({self.title})")

    def is_signal_present(self, signal_name):
        # Check if the bus has the attribute and that it is not None
        return hasattr(self.bus, signal_name) and getattr(self.bus, signal_name) is not None

    def dump_registers(self):
        msg = f"APB Slave {self.name} - Register Dump:"
        self.log.info(msg)
        self.log.info(self.mem.dump())

    async def reset_bus(self):
        msg = f'Resetting APB Bus {self.name}'
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
                msg = f'APB Slave Driver-{self.name}: {ready_delay=}'
                self.log.warning(msg)
                for _ in range(ready_delay):
                    await RisingEdge(self.clock)

                self.bus.PREADY.value = 1
                await Timer(200, units='ps')
                while not self.bus.PENABLE.value.integer:
                    start_time = get_sim_time('ns')
                    msg = f'APB Slave Driver-{self.name} Waiting for penable @ {start_time}'
                    self.log.warning(msg)
                    await RisingEdge(self.clock)
                    await Timer(200, units='ps')
                self._finish_recv(slv_error)

    def _finish_recv(self, slv_error):
        address    =  self.bus.PADDR.value.integer
        word_index =  (address & ~self.addr_mask)
        _          =  self.bus.PPROT.value.integer if self.is_signal_present('PPROT') else 0
        self.count += 1

        if word_index >= self.num_lines:
            if self.error_overflow:
                msg = f'APB {self.name} - Memory overflow error: {word_index}'
                self.log.error(msg)
                self.bus.PSLVERR.value = 1
            else:
                expand = word_index - self.num_lines + 10
                msg = f'APB {self.name} - Memory overflow: {self.num_lines=} {word_index=}'
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
        # self.log.warning(f'Master {name} {dir(self.bus)}')
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
        msg = f'Adding to the transmit_queue: {transaction}'
        self.log.warning(msg)

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
            msg = f'APB Master {self.name} attempting to transmit:\n{transaction}'
            self.log.warning(msg)
            msg = f'APB Master {self.name} {psel_delay=}'
            self.log.warning(msg)

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
            msg = f'APB Master {self.name} waiting for PREADY'
            self.log.warning(msg)
        
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
