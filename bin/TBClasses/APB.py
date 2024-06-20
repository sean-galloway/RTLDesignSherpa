from TBBase import TBBase
import cocotb
from cocotb.clock import Clock
from cocotb.triggers import RisingEdge, FallingEdge, ClockCycles, Timer
from cocotb.handle import SimHandleBase
from cocotb_bus.monitors import BusMonitor
from cocotb.utils import get_sim_time
from cocotb.queue import Queue
from cocotb.result import TestFailure
from cocotb_coverage.crv import Randomized
import os
import random
from ConstrainedRandom import ConstrainedRandom
from MemoryModel import MemoryModel
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
        self.add_rand("paddr",  list(range(2**10)))
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
    def __init__(self, entity, name, clock, signals=None, bus_width=32, addr_width=12, **kwargs):

        if signals:
            self._signals = signals
        else:
            self._signals = apb_signals
            self._optional_signals = apb_optional_signals

        self.count = 0
        self.bus_width = bus_width
        BusMonitor.__init__(self, entity, name, clock, **kwargs)
        self.clock = clock
        self.bus_width = bus_width
        self.addr_width = addr_width
        self.strb_width = bus_width // 8


    def is_signal_present(self, signal_name):
            return hasattr(self, signal_name)


    def print(self, transaction):
        self.log.debug('-' * 120)
        self.log.debug(f'{self.name} - APB Transaction')
        self.log.debug(transaction.formatted(self.addr_width, self.bus_width, self.strb_width))
        self.log.debug('-' * 120)


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


class APBBase(TBBase):
    def __init__(self, dut, name, clock, check_signals=False, signal_names=None):
        TBBase.__init__(self, dut)
        self.log.debug('---APBase init start')
        self.name = name
        self.clock = clock
        if signal_names is None:
            self.signal_name = {
                "PSEL":    f"{name}_PSEL",
                "PPROT":   f"{name}_PPROT",
                "PWRITE":  f"{name}_PWRITE",
                "PENABLE": f"{name}_PENABLE",
                "PADDR":   f"{name}_PADDR",
                "PWDATA":  f"{name}_PWDATA",
                "PRDATA":  f"{name}_PRDATA",
                "PREADY":  f"{name}_PREADY",
                "PSLVERR": f"{name}_PSLVERR",
                "PSTRB":   f"{name}_PSTRB"
            }
        else:
            self.signal_name = signal_names
        self.optional_signals = ["PSLVERR", "PSTRB", "PPROT"]
        for signal in self.optional_signals:
            setattr(self, f"{signal}_present", hasattr(self.dut, self.signal_name[signal]))
        if check_signals:
            self.check_signals()
        self.address_bits = self.get_width(self.signal_name['PADDR'])
        self.data_bits = self.get_width(self.signal_name['PWDATA'])
        self.strb_bits = self.get_width(self.signal_name['PSTRB']) if self.PSTRB_present else 0


    @staticmethod
    def set_constrained_random(passed_constraints, passed_weights):
        if passed_constraints is None:
            local_constraints = [(0, 0)]
            local_weights = [1]
        else:
            local_constraints = passed_constraints
            local_weights = passed_weights
        return ConstrainedRandom(local_constraints, local_weights)


    def check_signals(self):
        if missing_signals := [
            signal_name
            for signal_name in self.signal_name.values()
            if signal_name not in self.optional_signals and not hasattr(self.dut, signal_name)
        ]:
            raise AttributeError(f"The following signals are missing from the DUT: {', '.join(missing_signals)}")
        self.log.info('APB Check Signals passes')


    @staticmethod
    def set_constrained_random(passed_constraints, passed_weights):
        if passed_constraints is None:
            local_constraints = [(0, 0)]
            local_weights = [1]
        else:
            local_constraints = passed_constraints
            local_weights = passed_weights
        return ConstrainedRandom(local_constraints, local_weights)


    def get_width(self, signal_name):
        width = 0
        try:
            signal = getattr(self.dut, signal_name)
            if isinstance(signal, SimHandleBase):
                width = len(signal)
                self.log.info(f"Signal: {signal_name}, Width: {width}")
            else:
                self.log.info(f"Signal: {signal_name}, not a vector")
                width = 1
        except AttributeError:
            self.log.info(f"Signal '{signal_name}' not found on the DUT.")
        return width


    def bus(self, name):
        return getattr(self.dut, self.signal_name[name])


# class APBMonitor(APBBase):
#     def __init__(self, dut, name, clock, addr_mask=None, debug=None):
#         APBBase.__init__(self, dut, name, clock)
#         self.addr_mask = addr_mask if addr_mask is not None else (2 ** self.address_bits) - 1
#         self.log.debug(f'Starting APBMonitor - {name}')
#         self.transaction_queue = Queue()
#         self.count = 0
#         self.debug = debug


#     def print(self, transaction):
#         self.log.debug('-' * 120)
#         self.log.debug(f'{self.name} - APB Transaction')
#         self.log.debug(transaction)
#         self.log.debug('-' * 120)


#     async def monitor(self):
#         while True:
#             await self.wait_falling_clocks(self.clock, 1)
#             if self.bus('PSEL').value.integer and \
#                     self.bus('PENABLE').value.integer and \
#                     self.bus('PREADY').value.integer:
#                 start_time = get_sim_time('ns')
#                 address    = self.bus('PADDR').value.integer
#                 direction  = pwrite[self.bus('PWRITE').value.integer]
#                 pwrt       = self.bus('PWRITE').value.integer
#                 error      = self.bus('PSLVERR').value.integer if self.PSLVERR_present else 0

#                 if direction == 'READ':
#                     data = self.bus('PRDATA').value.integer
#                 else:
#                     data = self.bus('PWDATA').value.integer
#                 strb = self.bus('PSTRB').value.integer if self.PSTRB_present else 0
#                 prot = self.bus('PPROT').value.integer if self.PPROT_present else 0
#                 self.count += 1
#                 transaction = APBCycle(start_time, self.count, direction, pwrt, address, data, strb, data, prot, error)
#                 self.transaction_queue.put_nowait(transaction)
#                 self.print(transaction)


class APBSlave(APBBase):

    def __init__(self, dut, name, clock, registers=None,
                    ready_constraints=None, ready_weights=None,
                    error_constraints=None, error_weights=None,
                    addr_mask=None, debug=False, error_overflow=False):
        APBBase.__init__(self, dut, name, clock, True)
        self.num_lines      = len(registers) // self.strb_bits
        self.addr_mask      = addr_mask if addr_mask is not None else (2 ** self.address_bits) - 1
        self.debug          = debug
        self.count          = 0
        self.error_overflow = error_overflow
        # Create the memory model
        self.mem = MemoryModel(num_lines=self.num_lines, bytes_per_line=self.strb_bits, log=self.log, preset_values=registers)
        self.log.debug(self.mem.dump())
        # set the constrained random objects
        self.ready_crand    = self.set_constrained_random(ready_constraints, ready_weights)
        self.error_crand    = self.set_constrained_random(error_constraints, error_weights)


    def update_constraints(self, ready_constraints=None, ready_weights=None,
                            error_constraints=None, error_weights=None):
        self.ready_crand = self.set_constrained_random(ready_constraints, ready_weights)
        self.error_crand = self.set_constrained_random(error_constraints, error_weights)


    def dump_registers(self):
        self.log.info(f"APB Slave {self.name} - Register Dump:")
        self.log.info(self.mem.dump())


    async def reset_bus(self):
        self.log.info(f'Resetting APB Bus {self.name}')
        self.bus('PRDATA').value = 0
        self.bus('PREADY').value = 0
        if self.PSLVERR_present:
            self.bus('PSLVERR').value = 0


    def reset_registers(self):
        self.mem.reset(to_preset=True)


    async def driver(self):
        self.bus('PREADY').value = 0
        self.bus('PRDATA').value = 0
        if self.PSLVERR_present:
            self.bus('PSLVERR').value = 0

        while True:
            await self.wait_clocks(self.clock, 1)
            self.bus('PREADY').value = 0
            self.bus('PRDATA').value = 0
            if self.PSLVERR_present:
                self.bus('PSLVERR').value = 0

            if self.bus('PSEL').value.integer:
                rand_delay = self.ready_crand.next()
                self.log.debug(f'APB Slave Driver-{self.name}: {rand_delay=}')
                self.bus('PREADY').value = 0
                for _ in range(rand_delay):
                    await self.wait_clocks(self.clock, 1)

                self.bus('PREADY').value = 1
                await self.wait_time(200, 'ps')
                while not self.bus('PENABLE').value.integer:
                    # c = self.count + 1
                    # start_time =  get_sim_time('ns')
                    # self.log.debug(f'APB-Slave waiting for penable cycle: {c} sim time={start_time}ns')
                    await self.wait_clocks(self.clock, 1)

                address    =  self.bus('PADDR').value.integer
                word_index =  (address &  self.addr_mask) // self.strb_bits
                # prot       =  self.bus('PPROT').value.integer if self.PPROT_present else 0
                self.count += 1

                if word_index >= self.num_lines:
                    if self.error_overflow:
                        self.log.error(f'APB {self.name} - Memory overflow error: {word_index}')
                        self.bus('PSLVERR').value = 1
                    else:
                        expand = word_index - self.num_lines + 10
                        self.log.warning(f'APB {self.name} - Memory overflow: {self.num_lines=} {word_index=}')
                        # Extend the self.mem array to accommodate the overflow
                        self.mem.expand(expand)
                        self.num_lines += expand

                if slv_error := self.error_crand.next():
                    if self.PSLVERR_present:
                        self.bus('PSLVERR').value = 1

                if self.bus('PWRITE').value.integer:  # Write transaction
                    strobes   = self.bus('PSTRB').value.integer if self.PSTRB_present else (1 << self.strb_bits) - 1
                    pwdata    = self.bus('PWDATA').value.integer
                    pwdata_ba = self.mem.integer_to_bytearray(pwdata, self.strb_bits)
                    self.mem.write(address, pwdata_ba, strobes)

                else:  # Read transaction
                    prdata_ba = self.mem.read(address, self.strb_bits)
                    prdata = self.mem.bytearray_to_integer(prdata_ba)

                    self.bus('PRDATA').value = prdata



# class APBMaster(APBBase):
#     def __init__(self, dut, name, clock, registers=None,
#                  ready_constraints=None, ready_weights=None,
#                  error_constraints=None, error_weights=None,
#                  addr_mask=None, debug=False, error_overflow=False):
#         APBBase.__init__(self, dut, name, clock, False)
#         self.log.debug('Starting APBMaster')
#         bytes_per_line = self.strb_bits
#         self.num_lines = len(registers) // bytes
#         self.mem = MemoryModel(num_lines=self.num_lines, bytes_per_line=bytes_per_line, preset_values=registers)
#         self.error_overflow = error_overflow
#         self.ready_crand = self.set_constrained_random(ready_constraints, ready_weights)
#         self.error_crand = self.set_constrained_random(error_constraints, error_weights)
#         self.addr_mask = addr_mask if addr_mask is not None else (2 ** self.address_bits) - 1
#         self.debug = debug
#         self.transaction_queue = deque()

#     def update_constraints(self, ready_constraints=None, ready_weights=None,
#                            error_constraints=None, error_weights=None):
#         self.ready_crand = self.set_constrained_random(ready_constraints, ready_weights)
#         self.error_crand = self.set_constrained_random(error_constraints, error_weights)

#     def dump_registers(self):
#         self.log.debug(f"APB Master {self.name} - Register Dump:")
#         self.log.debug(self.mem.dump())

#     async def reset_bus(self):
#         self.log.debug(f'Resetting APB Bus {self.name}')
#         self.bus('PSEL').value = 0
#         self.bus('PENABLE').value = 0
#         self.bus('PWRITE').value = 0
#         self.bus('PADDR').value = 0
#         self.bus('PWDATA').value = 0
#         if self.PSTRB_present:
#             self.bus('PSTRB').value = 0
#         if self.PPROT_present:
#             self.bus('PPROT').value = 0

#     def reset_registers(self):
#         self.mem.reset(to_preset=True)

#     async def driver(self):
#         while True:
#             if self.transaction_queue:
#                 transaction = self.transaction_queue.popleft()
#                 address = transaction.paddr & self.addr_mask
#                 word_index = (address // self.strb_bits)

#                 start_time = transaction.start_time
#                 rand_delay = self.ready_crand.next()
#                 count = 0

#                 self.log.debug(f'APB Master-{self.name}: {rand_delay=}')

#                 while rand_delay != count:
#                     self.bus('PSEL').value = 0
#                     await self.wait_clocks(self.clock, 1)
#                     count += 1

#                 self.bus('PSEL').value = 1
#                 self.bus('PADDR').value = address
#                 self.bus('PPROT').value = transaction.pprot if self.PPROT_present else 0

#                 if transaction.pwrite:  # Write transaction
#                     self.bus('PWRITE').value = 1
#                     self.bus('PWDATA').value = transaction.pwdata
#                     if self.PSTRB_present:
#                         self.bus('PSTRB').value = transaction.pstrb

#                     while not self.bus('PREADY').value.integer:
#                         await self.wait_clocks(self.clock, 1)

#                     self.bus('PENABLE').value = 1

#                     while self.bus('PENABLE').value.integer:
#                         await self.wait_clocks(self.clock, 1)

#                     self.bus('PENABLE').value = 0

#                     if self.debug:
#                         self.log.debug(f'APB {self.name} - WRITE -{start_time}')
#                         self.log.debug(f' Address: 0x{address:08x}')
#                         self.log.debug(f' Word Index: 0d{word_index:04d}')
#                         self.log.debug(f' Data: 0x{transaction.pwdata:0{int(self.data_bits/4)}X}')
#                         if self.PSTRB_present:
#                             self.log.debug(f' Strb: 0b{transaction.pstrb:0{self.strb_bits}b}')

#                 else:  # Read transaction
#                     self.bus('PWRITE').value = 0

#                     while not self.bus('PREADY').value.integer:
#                         await self.wait_clocks(self.clock, 1)

#                     self.bus('PENABLE').value = 1

#                     while self.bus('PENABLE').value.integer:
#                         await self.wait_clocks(self.clock, 1)

#                     self.bus('PENABLE').value = 0

#                     prdata = self.bus('PRDATA').value.integer
#                     pslverr = self.bus('PSLVERR').value.integer if self.PSLVERR_present else 0

#                     if self.debug:
#                         self.log.debug(f'APB {self.name} - READ -{start_time}')
#                         self.log.debug(f' Address: 0x{address:08x}')
#                         self.log.debug(f' Word Index: 0d{word_index:04d}')
#                         self.log.debug(f' Data: 0x{prdata:0{int(self.data_bits/4)}X}')
#                         if self.PSLVERR_present:
#                             self.log.debug(f' PSLVERR: {pslverr}')

#                     if word_index >= self.num_lines:
#                         if self.error_overflow:
#                             self.log.error(f'APB {self.name} - Read overflow: {word_index}')
#                         else:
#                             self.log.warning(f'APB {self.name} - Read overflow: {word_index}')
#                             # Extend the self.mem to accommodate the overflow
#                             self.mem.expand(5)
#                             self.num_lines += 5

#                     strobes = (2**self.strb_bits)-1
#                     self.mem.write(word_index, prdata, strobes)

#             await self.wait_clocks(self.clock, 1)
