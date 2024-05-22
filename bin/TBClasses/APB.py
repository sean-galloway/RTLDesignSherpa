from TBBase import TBBase
import cocotb
from cocotb.clock import Clock
from cocotb.triggers import RisingEdge, FallingEdge, ClockCycles, Timer
from cocotb.handle import SimHandleBase
from cocotb.utils import get_sim_time
from cocotb.queue import Queue
from cocotb.result import TestFailure
import os
import random
from ConstrainedRandom import ConstrainedRandom
from dataclasses import dataclass
from collections import deque



# define the PWRITE mapping
pwrite = ['READ', 'WRITE']


@dataclass
class APBTransaction:
    start_time: int
    direction: str
    address: int
    word_index: int
    data: int
    strb: int
    prot: int
    error: int


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


class APBMonitor(APBBase):
    def __init__(self, dut, name, clock, addr_mask=None):
        APBBase.__init__(self, dut, name, clock)
        self.addr_mask = addr_mask if addr_mask is not None else (2 ** self.address_bits) - 1
        self.log.debug(f'Starting APBMonitor - {name}')
        self.transaction_queue = Queue[APBTransaction]()


    def print(self, transaction):
        self.log.info('-' * 120)
        self.log.info(f'{self.name} - APB Transaction - Started at {transaction.start_time} ns')
        self.log.info(f'  Direction:  {transaction.direction}')
        self.log.info(f'  Address:    0x{transaction.address:08x}')
        self.log.info(f'  Word Index: 0d{transaction.word_index:04d}')

        if transaction.data is None:
            self.log.info('  NO DATA YET!')
        else:
            self.log.info(f'  Data:      0x{transaction.data:0{int(self.data_bits/4)}X}')
            if self.PSTRB_present:
                self.log.info(f'  Strb:      0b{transaction.strb:0{self.strb_bits}b}')
            if self.PPROT_present:
                self.log.info(f'  Prot:      0b{transaction.prot:03b}')

        if transaction.error:
            self.log.info('  TRANSACTION ENDED IN ERROR!')
            self.log.info('')
        self.log.info('-' * 120)


    async def monitor(self):
        await self.wait_clocks(self.clock, 1)
        while True:
            start_time = get_sim_time('ns')
            if self.bus('PSEL').value.integer and \
                    self.bus('PENABLE').value.integer and \
                    self.bus('PREADY').value.integer:
                address = self.bus('PADDR').value.integer
                word_index = (address & self.addr_mask) // self.strb_bits
                direction = pwrite[self.bus('PWRITE').value.integer]
                error = self.bus('PSLVERR').value.integer if self.PSLVERR_present else 0

                if direction == 'READ':
                    data = self.bus('PRDATA').value.integer
                    strb = (2**self.strb_bits)-1
                    prot = 0
                else:
                    data = self.bus('PWDATA').value.integer
                    strb = self.bus('PSTRB').value.integer if self.PSTRB_present else 0
                    prot = self.bus('PPROT').value.integer if self.PPROT_present else 0

                transaction = APBTransaction(start_time, direction, address, word_index, data, strb, prot, error)
                self.transaction_queue.put_nowait(transaction)
                self.print(transaction)

            await self.wait_clocks(self.clock, 1)


class APBSlave(APBBase):
    def __init__(self, dut, name, clock, registers=None,
                    ready_constraints=None, ready_weights=None,
                    error_constraints=None, error_weights=None,
                    addr_mask=None, debug=False, error_overflow=False):
        APBBase.__init__(self, dut, name, clock, True)
        self.log.info('Starting APBSlave')
        self.registers_init = registers
        self.registers = registers
        self.error_overflow = error_overflow
        self.ready_crand = self.set_constrained_random(ready_constraints, ready_weights)
        self.error_crand = self.set_constrained_random(error_constraints, error_weights)
        self.addr_mask = addr_mask if addr_mask is not None else (2 ** self.address_bits) - 1
        self.debug = debug
        self.transaction_queue = Queue[APBTransaction]()


    def update_constraints(self, ready_constraints=None, ready_weights=None,
                            error_constraints=None, error_weights=None):
        self.ready_crand = self.set_constrained_random(ready_constraints, ready_weights)
        self.error_crand = self.set_constrained_random(error_constraints, error_weights)


    def dump_registers(self):
        self.log.info(f"APB Slave {self.name} - Register Dump:")
        self.log.info("-" * 40)
        for i, value in enumerate(self.registers):
            addr = i * self.strb_bits
            self.log.info(f"Register {i:2}: Address 0x{addr:08X} - Value 0x{value:0{self.data_bits//4}X}")
        self.log.info("-" * 40)


    async def reset_bus(self):
        self.log.info(f'Resetting APB Bus {self.name}')
        self.bus('PRDATA').value = 0
        self.bus('PREADY').value = 0
        if self.PSLVERR_present:
            self.bus('PSLVERR').value = 0

    def reset_registers(self):
        self.registers = self.registers_init

    async def driver(self):
        self.bus('PREADY').value = 0

        while True:
            if self.bus('PSEL').value.integer:
                address = self.bus('PADDR').value.integer
                word_index = (address & self.addr_mask) // self.strb_bits

                start_time = get_sim_time('ns')
                rand_delay = self.ready_crand.next()
                count = 0

                self.log.debug(f'APB Driver-{self.name}: {rand_delay=}')

                while rand_delay != count:
                    self.bus('PREADY').value = 0
                    await self.wait_clocks(self.clock, 1)
                    count += 1

                self.bus('PREADY').value = 1
                prot = self.bus('PPROT').value.integer if self.PPROT_present else 0

                if slv_error := self.error_crand.next():
                    if self.PSLVERR_present:
                        self.bus('PSLVERR').value = 1
                    transaction = APBTransaction(start_time, 'ERROR', address, word_index, 0, 0, prot, 1)

                elif self.bus('PWRITE').value.integer:  # Write transaction
                    while not self.bus('PENABLE').value.integer:
                        await self.wait_clocks(self.clock, 1)

                    strobes = self.bus('PSTRB').value.integer if self.PSTRB_present else (1 << self.strb_bits) - 1
                    pwdata = self.bus('PWDATA').value.integer

                    if self.debug:
                        self.log.debug(f'APB {self.name} - WRITE -{start_time}')
                        self.log.debug(f' Address: 0x{address:08x}')
                        self.log.debug(f' Word Index: 0d{word_index:04d}')
                        self.log.debug(f' Data: 0x{pwdata:0{int(self.data_bits/4)}X}')
                        if self.PSTRB_present:
                            self.log.info(f' Strb: 0b{strobes:0{self.strb_bits}b}')

                    if word_index >= len(self.registers):
                        if self.error_overflow:
                            self.log.error(f'APB {self.name} - Write overflow: {word_index}')
                            self.bus('PSLVERR').value = 1
                        else:
                            self.log.warning(f'APB {self.name} - Write overflow: {word_index}')
                            # Extend the self.registers array to accommodate the overflow
                            self.registers.extend([0] * (word_index - len(self.registers) + 1))

                    for i in range(self.strb_bits):
                        if (strobes >> i) & 1:
                            byte_offset = i * 8
                            byte_mask = 0xFF << byte_offset
                            self.registers[word_index] &= ~byte_mask
                            self.registers[word_index] |= (pwdata & byte_mask)

                    transaction = APBTransaction(start_time, 'WRITE', address, word_index, pwdata, strobes, prot, 0)

                else:  # Read transaction
                    if word_index >= len(self.registers):
                        if self.error_overflow:
                            self.log.error(f'APB {self.name} - Read overflow: {word_index}')
                            self.bus('PSLVERR').value = 1
                        else:
                            self.log.warning(f'APB {self.name} - Read overflow: {word_index}')
                        prdata = 0
                    else:
                        prdata = self.registers[word_index]

                    self.bus('PRDATA').value = prdata

                    while not self.bus('PENABLE').value.integer:
                        await self.wait_clocks(self.clock, 1)

                    if self.debug:
                        self.log.debug(f'APB {self.name} - READ -{start_time}')
                        self.log.debug(f' Address: 0x{address:08x}')
                        self.log.debug(f' Word Index: 0d{word_index:04d}')
                        self.log.debug(f' Data: 0x{prdata:0{int(self.data_bits/4)}X}')
                        if self.PSTRB_present:
                            self.log.info(f' Strb: 0b{strobes:0{self.strb_bits}b}')

                    transaction = APBTransaction(start_time, 'READ', address, word_index, prdata, 0, prot, 0)

                self.transaction_queue.put_nowait(transaction)

            await self.wait_clocks(self.clock, 1)


class APBMaster(APBBase):
    def __init__(self, dut, name, clock, registers=None,
                 ready_constraints=None, ready_weights=None,
                 error_constraints=None, error_weights=None,
                 addr_mask=None, debug=False, error_overflow=False):
        APBBase.__init__(self, dut, name, clock, False)
        self.log.info('Starting APBMaster')
        self.registers_init = registers
        self.registers = registers
        self.error_overflow = error_overflow
        self.ready_crand = self.set_constrained_random(ready_constraints, ready_weights)
        self.error_crand = self.set_constrained_random(error_constraints, error_weights)
        self.addr_mask = addr_mask if addr_mask is not None else (2 ** self.address_bits) - 1
        self.debug = debug
        self.transaction_queue = deque()

    def update_constraints(self, ready_constraints=None, ready_weights=None,
                           error_constraints=None, error_weights=None):
        self.ready_crand = self.set_constrained_random(ready_constraints, ready_weights)
        self.error_crand = self.set_constrained_random(error_constraints, error_weights)

    def dump_registers(self):
        self.log.info(f"APB Master {self.name} - Register Dump:")
        self.log.info("-" * 40)
        for i, value in enumerate(self.registers):
            addr = i * self.strb_bits
            self.log.info(f"Register {i:2}: Address 0x{addr:08X} - Value 0x{value:0{self.data_bits//4}X}")
        self.log.info("-" * 40)

    async def reset_bus(self):
        self.log.info(f'Resetting APB Bus {self.name}')
        self.bus('PSEL').value = 0
        self.bus('PENABLE').value = 0
        self.bus('PWRITE').value = 0
        self.bus('PADDR').value = 0
        self.bus('PWDATA').value = 0
        if self.PSTRB_present:
            self.bus('PSTRB').value = 0
        if self.PPROT_present:
            self.bus('PPROT').value = 0

    def reset_registers(self):
        self.registers = self.registers_init

    async def driver(self):
        while True:
            if self.transaction_queue:
                transaction = self.transaction_queue.popleft()
                address = transaction.paddr & self.addr_mask
                word_index = (address // self.strb_bits)

                start_time = transaction.start_time
                rand_delay = self.ready_crand.next()
                count = 0

                self.log.debug(f'APB Master-{self.name}: {rand_delay=}')

                while rand_delay != count:
                    self.bus('PSEL').value = 0
                    await self.wait_clocks(self.clock, 1)
                    count += 1

                self.bus('PSEL').value = 1
                self.bus('PADDR').value = address
                self.bus('PPROT').value = transaction.pprot if self.PPROT_present else 0

                if transaction.pwrite:  # Write transaction
                    self.bus('PWRITE').value = 1
                    self.bus('PWDATA').value = transaction.pwdata
                    if self.PSTRB_present:
                        self.bus('PSTRB').value = transaction.pstrb

                    while not self.bus('PREADY').value.integer:
                        await self.wait_clocks(self.clock, 1)

                    self.bus('PENABLE').value = 1

                    while self.bus('PENABLE').value.integer:
                        await self.wait_clocks(self.clock, 1)

                    self.bus('PENABLE').value = 0

                    if self.debug:
                        self.log.debug(f'APB {self.name} - WRITE -{start_time}')
                        self.log.debug(f' Address: 0x{address:08x}')
                        self.log.debug(f' Word Index: 0d{word_index:04d}')
                        self.log.debug(f' Data: 0x{transaction.pwdata:0{int(self.data_bits/4)}X}')
                        if self.PSTRB_present:
                            self.log.debug(f' Strb: 0b{transaction.pstrb:0{self.strb_bits}b}')

                else:  # Read transaction
                    self.bus('PWRITE').value = 0

                    while not self.bus('PREADY').value.integer:
                        await self.wait_clocks(self.clock, 1)

                    self.bus('PENABLE').value = 1

                    while self.bus('PENABLE').value.integer:
                        await self.wait_clocks(self.clock, 1)

                    self.bus('PENABLE').value = 0

                    prdata = self.bus('PRDATA').value.integer
                    pslverr = self.bus('PSLVERR').value.integer if self.PSLVERR_present else 0

                    if self.debug:
                        self.log.debug(f'APB {self.name} - READ -{start_time}')
                        self.log.debug(f' Address: 0x{address:08x}')
                        self.log.debug(f' Word Index: 0d{word_index:04d}')
                        self.log.debug(f' Data: 0x{prdata:0{int(self.data_bits/4)}X}')
                        if self.PSLVERR_present:
                            self.log.debug(f' PSLVERR: {pslverr}')

                    if word_index >= len(self.registers):
                        if self.error_overflow:
                            self.log.error(f'APB {self.name} - Read overflow: {word_index}')
                        else:
                            self.log.warning(f'APB {self.name} - Read overflow: {word_index}')
                            # Extend the self.registers array to accommodate the overflow
                            self.registers.extend([0] * (word_index - len(self.registers) + 1))

                    self.registers[word_index] = prdata

            await self.wait_clocks(self.clock, 1)


class APBCommandPacket:
    def __init__(self, data_width, addr_width, strb_width):
        self.data_width = data_width
        self.addr_width = addr_width
        self.strb_width = strb_width

        self.pwrite  = random.randint(0, 1)
        self.paddr   = random.randint(0, (1 << 5) - 1)
        self.pwdata  = random.randint(0, (1 << data_width) - 1)
        self.prdata  = random.randint(0, (1 << data_width) - 1)
        self.pstrb   = random.randint(0, (1 << strb_width) - 1)
        self.pprot   = random.randint(0, 7)  # Assuming 3-bit pprot
        self.pslverr = 0


    def pack_cmd_packet(self):
        print('------------------------------------------------------')
        print(f' Write: {self.pwrite=}')
        print(f' Addr:  0x{self.paddr:08x}')
        print(f' Data:  0x{self.pwdata:08x}')
        print(f' Prot:  0x{self.pprot:x}')
        cmd_packet = (self.pwrite << (self.addr_width + self.data_width + self.strb_width + 3)) | \
                     (self.pprot << (self.addr_width + self.data_width + self.strb_width)) | \
                     (self.pstrb << (self.addr_width + self.data_width)) | \
                     (self.paddr << self.data_width) | \
                     self.pwdata
        return cmd_packet


class APBCommandGenerator():
    def __init__(self, dw, aw, sw):
        self.data_bits = dw
        self.address_bits = aw
        self.strb_bits = sw


    def generate_write_cmd(self):
        print('generate_write_cmd')
        cmd_packet = APBCommandPacket(self.data_bits, self.address_bits, self.strb_bits)
        cmd_packet.pwrite = 1  # Set pwrite to 1 for write command
        return cmd_packet.pack_cmd_packet()


    def generate_read_cmd(self):
        print('generate_read_cmd')
        cmd_packet = APBCommandPacket(self.data_bits, self.address_bits, self.strb_bits)
        cmd_packet.pwrite = 0  # Set pwrite to 0 for read command
        return cmd_packet.pack_cmd_packet()