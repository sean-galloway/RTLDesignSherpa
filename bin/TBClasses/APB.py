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
    error: int


class APBBase(TBBase):
    def __init__(self, dut, name, clock, check_signals=False, signal_names=None):
        TBBase.__init__(self, dut)
        self.log.debug('---APBase init start')
        self.name = name
        self.clock = clock
        if signal_names is None:
            self.signal_name = {
                "PSEL": f"{name}_PSEL",
                "PWRITE": f"{name}_PWRITE",
                "PENABLE": f"{name}_PENABLE",
                "PADDR": f"{name}_PADDR",
                "PWDATA": f"{name}_PWDATA",
                "PRDATA": f"{name}_PRDATA",
                "PREADY": f"{name}_PREADY",
                "PSLVERR": f"{name}_PSLVERR",
                "PSTRB": f"{name}_PSTRB"
            }
        else:
            self.signal_name = signal_names
        self.optional_signals = ["PSLVERR", "PSTRB"]
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
    def __init__(self, dut, name, clock):
        APBBase.__init__(self, dut, name, clock)
        self.log.debug(f'Starting APBMonitor - {name}')
        self.transaction_queue = Queue[APBTransaction]()

    def print(self, transaction):
        self.log.info('-' * 120)
        self.log.info(f'{self.name} - APB Transaction - Started at {transaction.start_time} ns')
        self.log.info(f'  Direction: {transaction.direction}')
        self.log.info(f'  Address:   0x{transaction.address:08x}')

        if transaction.data is None:
            self.log.info('  NO DATA YET!')
        else:
            self.log.info(f'  Data:      0x{transaction.data:0{int(self.data_bits/4)}X}')
            if self.PSTRB_present:
                self.log.info(f'  Strb:      0b{transaction.strb:0{self.strb_bits}b}')

        if transaction.error:
            self.log.info('  TRANSACTION ENDED IN ERROR!')
            self.log.info('')
        self.log.info('-' * 120)

    async def monitor(self):
        await self.wait_clocks(self.clock, 1)
        while True:
            start_time = get_sim_time('ns')
            if self.bus('PSEL').value.integer and self.bus('PENABLE').value.integer and self.bus('PREADY').value.integer:
                address = self.bus('PADDR').value.integer
                word_index = int((address % (2 ** self.address_bits - 1)) / 4)
                direction = pwrite[self.bus('PWRITE').value.integer]
                error = self.bus('PSLVERR').value.integer if self.PSLVERR_present else 0

                if direction == 'READ':
                    data = self.bus('PRDATA').value.integer
                    strb = (2**self.strb_bits)-1
                else:
                    data = self.bus('PWDATA').value.integer
                    strb = self.bus('PSTRB').value.integer if self.PSTRB_present else 0

                transaction = APBTransaction(start_time, direction, address, word_index, data, strb, error)
                self.transaction_queue.put_nowait(transaction)
                # self.print(transaction)

            await self.wait_clocks(self.clock, 1)


class APBSlave(APBBase):
    def __init__(self, dut, name, clock, registers=None,
                    idle_constraints=None, idle_weights=None,
                    delay_constraints=None, delay_weights=None,
                    error_constraints=None, error_weights=None,
                    addr_mask=None, debug=False):
        APBBase.__init__(self, dut, name, clock, True)
        self.log.info('Starting APBSlave')
        self.registers_init = registers
        self.registers = registers
        self.idle_crand = self.set_constrained_random(idle_constraints, idle_weights)
        self.reply_crand = self.set_constrained_random(delay_constraints, delay_weights)
        self.error_crand = self.set_constrained_random(error_constraints, error_weights)
        self.addr_mask = addr_mask if addr_mask is not None else (2 ** self.address_bits) - 1
        self.debug = debug
        self.transaction_queue = Queue[APBTransaction]()


    def dump_registers(self):
        self.log.info(f"APB Slave {self.name} - Register Dump:")
        self.log.info("-" * 40)
        for i, value in enumerate(self.registers):
            addr = i * 4
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
        while True:
            self.bus('PREADY').value = 0
            await self.wait_clocks(self.clock, 1)

            if self.bus('PSEL').value.integer:
                address = self.bus('PADDR').value.integer
                word_index = (address & self.addr_mask) // self.strb_bits
                start_time = get_sim_time('ns')

                rand_delay = self.reply_crand.next()
                count = 0
                while rand_delay != count:
                    await self.wait_clocks(self.clock, 1)
                    count += 1

                if slv_error := self.error_crand.next():
                    if self.PSLVERR_present:
                        self.bus('PSLVERR').value = 1
                    transaction = APBTransaction(start_time, 'ERROR', address, word_index, 0, 0, 1)
                elif self.bus('PWRITE').value.integer:  # Write transaction
                    while not self.bus('PENABLE').value.integer:
                        await self.wait_clocks(self.clock, 1)

                    strobes = self.bus('PSTRB').value.integer if self.PSTRB_present else (1 << self.strb_bits) - 1
                    pwdata = self.bus('PWDATA').value.integer

                    if self.debug:
                        self.log.debug(f'APB {self.name} - WRITE -{start_time}')
                        self.log.debug(f'  Address:    0x{address:08x}')
                        self.log.debug(f'  Word Index: 0x{word_index:08x}')
                        self.log.debug(f'  Data:       0x{pwdata:0{int(self.data_bits/4)}X}')
                        if self.PSTRB_present:
                            self.log.info(f'  Strb:        0b{strobes:0{self.strb_bits}b}')

                    for i in range(self.strb_bits):
                        if (strobes >> i) & 1:
                            byte_offset = i * 8
                            byte_mask = 0xFF << byte_offset

                            self.registers[word_index] &= ~byte_mask
                            self.registers[word_index] |= (pwdata & byte_mask)

                    transaction = APBTransaction(start_time, 'WRITE', address, word_index, pwdata, strobes, 0)
                else:  # Read transaction
                    prdata = self.registers[word_index]
                    self.bus('PRDATA').value = prdata

                    while not self.bus('PENABLE').value.integer:
                        await self.wait_clocks(self.clock, 1)

                    if self.debug:
                        self.log.debug(f'APB {self.name} - READ -{start_time}')
                        self.log.debug(f'  Address:    0x{address:08x}')
                        self.log.debug(f'  Word Index: 0x{word_index:08x}')
                        self.log.debug(f'  Data:       0x{prdata:0{int(self.data_bits/4)}X}')
                        if self.PSTRB_present:
                            self.log.info(f'  Strb:        0b{strobes:0{self.strb_bits}b}')

                    transaction = APBTransaction(start_time, 'READ', address, word_index, prdata, 0, 0)
                self.transaction_queue.put_nowait(transaction)
                self.bus('PREADY').value = 1
                await self.wait_clocks(self.clock, 1)