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
import json
from dataclasses import dataclass, field
from typing import List
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


class RegisterMap:
    def __init__(self, filename, apb_data_width, apb_addr_width, start_address):
        self.registers = self._load_registers(filename)
        self.current_state = self._initialize_state()
        self.write_storage = {}
        self.apb_data_width = apb_data_width
        self.apb_addr_width = apb_addr_width
        self.start_address = start_address
        self.addr_mask = (1 << apb_addr_width) - 1
        self.data_mask = (1 << apb_data_width) - 1
        self.bytes_per_word = apb_data_width // 8


    def _load_registers(self, filename):
        with open(filename, 'r') as f:
            return json.load(f)


    def _initialize_state(self):
        return {
            reg_name: (
                [int(reg_info['default'], 16)] * int(reg_info['count'])
                if 'count' in reg_info
                else int(reg_info['default'], 16)
            )
            for reg_name, reg_info in self.registers.items()
        }


    def get_register_field_map(self):
        register_field_map = {}
        for register_name, register_info in self.registers.items():
            fields = [field for field in register_info.keys() if register_info[field]['type'] == 'field']
            register_field_map[register_name] = fields
        return register_field_map


    def get_register_offset_map(self):
        return {reg_name: int(reg_info['offset'], 16) for reg_name, reg_info in self.registers.items()}


    def get_combined_register_map(self):
        field_map = self.get_register_field_map()
        offset_map = self.get_register_offset_map()
        return {
            reg: {'fields': field_map[reg], 'offset': offset}
            for reg, offset in offset_map.items()
        }


    def write(self, register, field, value):
        if register not in self.registers:
            raise ValueError(f"Register {register} not found")
        if field not in self.registers[register]:
            raise ValueError(f"Field {field} not found in register {register}")
        
        reg_info = self.registers[register]
        field_info = reg_info[field]
        
        mask = self._create_mask(field_info['offset'])
        field_width = self._get_field_width(field_info['offset'])
        
        num_words = (field_width + self.apb_data_width - 1) // self.apb_data_width
        
        if 'count' in reg_info:
            if register not in self.write_storage:
                self.write_storage[register] = [None] * int(reg_info['count'])
            for i in range(int(reg_info['count'])):
                if self.write_storage[register][i] is None:
                    self.write_storage[register][i] = self.current_state[register][i]
                for j in range(num_words):
                    word_mask = mask & self.data_mask
                    word_value = (value >> (j * self.apb_data_width)) & self.data_mask
                    self.write_storage[register][i+j] = (self.write_storage[register][i+j] & ~word_mask) | (word_value & word_mask)
                    mask >>= self.apb_data_width
        else:
            if register not in self.write_storage:
                self.write_storage[register] = [self.current_state[register]] * num_words
            for j in range(num_words):
                word_mask = mask & self.data_mask
                word_value = (value >> (j * self.apb_data_width)) & self.data_mask
                self.write_storage[register][j] = (self.write_storage[register][j] & ~word_mask) | (word_value & word_mask)
                mask >>= self.apb_data_width


    def _create_mask(self, offset):
        if ':' not in offset:
            return 1 << int(offset)
        high, low = map(int, offset.split(':'))
        return ((1 << (high - low + 1)) - 1) << low


    def _get_field_width(self, offset):
        if ':' not in offset:
            return 1
        high, low = map(int, offset.split(':'))
        return high - low + 1


    def generate_apb_cycles(self) -> List[APBCycle]:
        apb_cycles = []
        for register, value in self.write_storage.items():
            reg_info = self.registers[register]
            base_address = (self.start_address + int(reg_info['address'], 16)) & self.addr_mask
            for i, v in enumerate(value):
                if (
                    isinstance(value, list)
                    and v is not None
                    or not isinstance(value, list)
                ):
                    address = (base_address + i * self.bytes_per_word) & self.addr_mask
                    apb_cycles.append(APBCycle(
                        start_time=0,  # You might want to set this appropriately
                        count=i,
                        direction='WRITE',
                        pwrite=1,
                        paddr=address,
                        pwdata=v,
                        pstrb=(1 << (self.bytes_per_word)) - 1,  # Full write strobe
                        prdata=0,
                        pprot=0,
                        pslverr=0
                    ))
        self._update_current_state()
        self.write_storage.clear()

        return apb_cycles


    def _update_current_state(self):
        for register, value in self.write_storage.items():
            if isinstance(self.current_state[register], list):
                for i, v in enumerate(value):
                    if v is not None:
                        self.current_state[register][i] = v
            else:
                self.current_state[register] = value[0]  # Take the first word for non-array registers

# Usage example:
# reg_map = RegisterMap('registers.json', apb_data_width=32, apb_addr_width=24, start_address=0x7F0000)
# reg_map.write('descr_map', 'descr_data', 0xFFFFFFFFFFFFFFFF)  # 64-bit write
# apb_cycles = reg_map.generate_apb_cycles()


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


    def apply_constraints(self):
        for signal, (bins, weights) in self.constraints.items():
            print(f'{signal=} {bins=} {weights=}')
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


    def __str__(self):
        """
        Return a string representation of the command packet for debugging.
        """
        return (f'{self.cycle.formatted(self.addr_width, self.data_width, self.strb_width)}')


class APBMonitor(BusMonitor):
    def __init__(self, entity, name, clock, signals=None,
                 bus_width=32, addr_width=12, log=None, **kwargs):

        # flag = False
        if signals:
            self._signals = signals
        else:
            flag = True
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
        # if flag: 
        #     self.log.warning(f'Monitor {name} setting default signals')
        # self.log.warning(f'Monitor {name} {dir(self.bus)}')


    def is_signal_present(self, signal_name):
        # Check if the bus has the attribute and that it is not None
        return hasattr(self.bus, signal_name) and getattr(self.bus, signal_name) is not None


    def print(self, transaction):
        self.log.debug('-' * 120)
        self.log.debug(f'{self.name} - APB Transaction')
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
                    log=None, error_overflow=False, **kwargs):
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
        self.log = log or self.entity._log
        self.addr_width     = addr_width
        self.bus_width      = bus_width
        self.strb_bits      = bus_width // 8
        self.addr_mask      = (2**self.strb_bits - 1)
        self.num_lines      = len(registers) // self.strb_bits
        self.delay_crand    = DelayRandomizer(self.constraints)
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
        self.log.warning(f'Slave {name} {dir(self.bus)}')
        self.log.warning(f'Slave {name} PADDR {dir(self.bus.PADDR)}')
        if self.is_signal_present('PPROT'):
            self.log.warning(f'Slave {name} PPROT {dir(self.bus.PPROT)}')


    def is_signal_present(self, signal_name):
        # Check if the bus has the attribute and that it is not None
        return hasattr(self.bus, signal_name) and getattr(self.bus, signal_name) is not None


    def dump_registers(self):
        self.log.info(f"APB Slave {self.name} - Register Dump:")
        self.log.info(self.mem.dump())


    async def reset_bus(self):
        self.log.info(f'Resetting APB Bus {self.name}')
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
                rand_dict = self.delay_crand.set_constrained_random()
                ready_delay = rand_dict['ready']
                slv_error = rand_dict['error']
                self.log.warning(f'APB Slave Driver-{self.name}: {ready_delay=}')
                for _ in range(ready_delay):
                    await RisingEdge(self.clock)

                self.bus.PREADY.value = 1
                await Timer(200, units='ps')
                while not self.bus.PENABLE.value.integer:
                    start_time = get_sim_time('ns')
                    self.log.warning(f'APB Slave Driver-{self.name} Waiting for penable @ {start_time}')
                    await RisingEdge(self.clock)
                    await Timer(200, units='ps')

                address    =  self.bus.PADDR.value.integer
                word_index =  (address & ~self.addr_mask)
                prot       =  self.bus.PPROT.value.integer if self.is_signal_present('PPROT') else 0
                self.count += 1

                if word_index >= self.num_lines:
                    if self.error_overflow:
                        self.log.error(f'APB {self.name} - Memory overflow error: {word_index}')
                        self.bus.PSLVERR.value = 1
                    else:
                        expand = word_index - self.num_lines + 10
                        self.log.warning(f'APB {self.name} - Memory overflow: {self.num_lines=} {word_index=}')
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
                    log=None, **kwargs):
        if signals:
            self._signals = signals
        else:
            self._signals = apb_signals + apb_optional_signals
            self._optional_signals = apb_optional_signals
        if constraints is None:
            self.constraints = {
                'psel':    ([[0, 0], [1, 5], [6, 10]], [5, 2, 1]),
                'penable': ([[0, 0], [1, 2]], [4, 1]),
            }
        else:
            self.constraints = constraints
        BusDriver.__init__(self, entity, name, clock, **kwargs)
        self.log = log or self.entity._log
        # Print the attributes of the bus object
        self.log.debug("APB Master Bus object attributes:")
        for attribute in dir(self.bus):
            try:
                value = getattr(self.bus, attribute)
                self.log.debug(f"{attribute}: {value}")
            except AttributeError:
                self.log.debug(f"{attribute}: <unreadable>")
        self.clock          = clock
        self.addr_width     = addr_width
        self.bus_width      = bus_width
        self.strb_bits      = bus_width // 8
        self.addr_mask      = (2**self.strb_bits - 1)
        self.delay_crand    = DelayRandomizer(self.constraints)
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
        self.log.warning(f'Adding to the transmit_queue: {transaction}')

        # launch new transmit pipeline coroutine if aren't holding for and the
        #   the coroutine isn't already running.
        #   If it is running it will just collect the transactions in the
        #   queue once it gets to them.
        if not hold and not self.transmit_coroutine:
            self.transmit_coroutine = cocotb.start_soon(self._transmit_pipeline())


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
            if self.is_signal_present('PPROT'):
                self.bus.PPROT.value = 0
            if self.is_signal_present('PSTRB'):
                self.bus.PSTRB.value = 0

            rand_dict = self.delay_crand.set_constrained_random()
            psel_delay = rand_dict['psel']
            penable_delay = rand_dict['penable']

            transaction = self.transmit_queue.popleft()
            transaction.start_time = cocotb.utils.get_sim_time('ns')
            self.log.warning(f'APB Master {self.name} attempting to transmit:\n{transaction}')
            self.log.warning(f'APB Master {self.name} {psel_delay=}')

            while psel_delay > 0:
                psel_delay -= 1
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

            while penable_delay > 0:
                penable_delay -= 1
                await RisingEdge(self.clock)
            
            self.bus.PENABLE.value  = 1
            await FallingEdge(self.clock)

            while not self.bus.PREADY.value:
                await FallingEdge(self.clock)
                self.log.warning(f'APB Master {self.name} waiting for PREADY')
            
            # check if the slave is asserting an error
            if self.is_signal_present('PSLVERR') and self.bus.PSLVERR.value:
                transaction.error = True

            # if this is a read we should sample the data
            if transaction.direction == 'READ':
                transaction.data = self.bus.PRDATA.value

            self.sentQ.append(transaction)
            await RisingEdge(self.clock)

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
