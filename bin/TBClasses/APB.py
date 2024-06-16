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
from MemoryModel import MemoryModel
from dataclasses import dataclass
from collections import deque

# define the PWRITE mapping
pwrite = ['READ', 'WRITE']


@dataclass
class APBTransaction:
    start_time: int
    count: int
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


class APBMonitor(APBBase):
    def __init__(self, dut, name, clock, addr_mask=None, debug=None):
        APBBase.__init__(self, dut, name, clock)
        self.addr_mask = addr_mask if addr_mask is not None else (2 ** self.address_bits) - 1
        self.log.debug(f'Starting APBMonitor - {name}')
        self.transaction_queue = Queue()
        self.count = 0
        self.debug = debug


    def print(self, transaction):
        self.log.info('-' * 120)
        self.log.info(f'{self.name} - APB Transaction - Started at {transaction.start_time} ns')
        self.log.info(f'  Count:      {transaction.count}')
        self.log.info(f'  Direction:  {transaction.direction}')
        self.log.info(f'  Address:    0x{transaction.address:08x}')

        if transaction.data is None:
            self.log.info('  NO DATA YET!')
        else:
            self.log.info(f'  Data:       0x{transaction.data:0{int(self.data_bits/4)}X}')
            if self.PSTRB_present:
                self.log.info(f'  Strb:       0b{transaction.strb:0{self.strb_bits}b}')
            if self.PPROT_present:
                self.log.info(f'  Prot:       0b{transaction.prot:03b}')

        if transaction.error:
            self.log.info('  TRANSACTION ENDED IN ERROR!')
            self.log.info('')
        self.log.info('-' * 120)


    async def monitor(self):
        while True:
            await self.wait_falling_clocks(self.clock, 1)
            if self.bus('PSEL').value.integer and \
                    self.bus('PENABLE').value.integer and \
                    self.bus('PREADY').value.integer:
                start_time = get_sim_time('ns')
                address    = self.bus('PADDR').value.integer
                word_index = (address & self.addr_mask) // self.strb_bits
                direction  = pwrite[self.bus('PWRITE').value.integer]
                error      = self.bus('PSLVERR').value.integer if self.PSLVERR_present else 0

                if direction == 'READ':
                    data = self.bus('PRDATA').value.integer
                else:
                    data = self.bus('PWDATA').value.integer
                strb = self.bus('PSTRB').value.integer if self.PSTRB_present else 0
                prot = self.bus('PPROT').value.integer if self.PPROT_present else 0
                self.count += 1
                transaction = APBTransaction(start_time, self.count, direction, address, word_index, data, strb, prot, error)
                self.transaction_queue.put_nowait(transaction)
                if self.debug:
                    self.print(transaction)


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
        self.log.info(self.mem.dump())
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


class APBCommandPacket:
    def __init__(self, data_width, addr_width, strb_width, log=None,
                    pwrite_constraints=None, pwrite_weights=None,
                    paddr_constraints=None, paddr_weights=None,
                    pprot_constraints=None, pprot_weights=None):
        self.start_time = 0
        self.data_width = data_width
        self.addr_width = addr_width
        self.strb_width = strb_width
        self.addr_mask  = (strb_width - 1)
        self.log = log
        self.count = 0

        # Create the ConstrainedRandom objects
        self.pwrite_crand = self.set_constrained_random(pwrite_constraints, pwrite_weights)
        self.paddr_crand = self.set_constrained_random(paddr_constraints, paddr_weights)
        self.pprot_crand = self.set_constrained_random(pprot_constraints, pprot_weights)

        self.pwrite  = self.pwrite_crand.next() if pwrite_constraints else random.randint(0, 1)
        self.direction = 'WRITE' if self.pwrite else 'READ'
        self.paddr   = self.paddr_crand.next() if paddr_constraints else random.randint(0, (1 << addr_width) - 1)
        self.paddr   = self.paddr & ~self.addr_mask
        self.pwdata  = random.randint(0, (1 << data_width) - 1)
        self.prdata  = 0  # PRDATA is typically read, not written by master
        self.pstrb   = random.randint(0, (1 << strb_width) - 1)
        self.pprot   = self.pprot_crand.next() if pprot_constraints else random.randint(0, 7)  # Assuming 3-bit PPROT
        self.pslverr = 0  # PSLVERR is typically set by the slave


    def log_packet(self):
            self.log.info(f"APBCommandPacket - start_time: {self.start_time}\n"+ 
                            f"                        count: {self.count}\n"+
                            f"                    direction: {self.direction}\n"+
                            f"                        paddr:  0x{self.paddr:08X}\n"+
                            f"                       pwdata:  0x{self.pwdata:0{self.data_width // 4}X}\n"+
                            f"                        pstrb:  0x{self.pstrb:X}\n"
                            f"                        pprot:  {self.pprot}\n"+
                            f"                      pslverr:  {self.pslverr}\n")


    @staticmethod
    def set_constrained_random(passed_constraints, passed_weights):
        if passed_constraints is None:
            local_constraints = [(0, 0)]
            local_weights = [1]
        else:
            local_constraints = passed_constraints
            local_weights = passed_weights
        return ConstrainedRandom(local_constraints, local_weights)


    def pack_cmd_packet(self):
        """
        Pack the command packet into a single integer.
        """
        return (
            (self.pwrite << (self.addr_width + self.data_width + self.strb_width + 3)) |
            (self.pprot << (self.addr_width + self.data_width + self.strb_width)) |
            (self.pstrb << (self.addr_width + self.data_width)) |
            (self.paddr << self.data_width) |
            self.pwdata
        )


    def unpack_cmd_packet(self, packed_packet):
        """
        Unpack a packed command packet into its components.
        """
        self.pwrite = (packed_packet >> (self.addr_width + self.data_width + self.strb_width + 3)) & 0x1
        self.pprot = (packed_packet >> (self.addr_width + self.data_width + self.strb_width)) & 0x7
        self.pstrb = (packed_packet >> (self.addr_width + self.data_width)) & ((1 << self.strb_width) - 1)
        self.paddr = (packed_packet >> self.data_width) & ((1 << self.addr_width) - 1)
        self.pwdata = packed_packet & ((1 << self.data_width) - 1)


    def __str__(self):
        """
        Return a string representation of the command packet for debugging.
        """
        return (
            f"APB Command Packet:\n"
            f"  PWRITE : {self.pwrite}\n"
            f"  PADDR  : 0x{self.paddr:08X}\n"
            f"  PWDATA : 0x{self.pwdata:0{self.data_width // 4}X}\n"
            f"  PSTRB  : 0b{self.pstrb:0{self.strb_width}b}\n"
            f"  PPROT  : 0b{self.pprot:03b}\n"
            f"  PSLVERR: {self.pslverr}\n"
        )


class APBCommandGenerator():
    def __init__(self, dw, aw, sw):
        self.data_bits = dw
        self.address_bits = aw
        self.strb_bits = sw


    def generate_write_cmd(self):
        return self.generate_cmd(1)


    def generate_read_cmd(self):
        return self.generate_cmd(0)


    def generate_cmd(self, arg0):
        cmd_packet = APBCommandPacket(
            self.data_bits, self.address_bits, self.strb_bits
        )
        cmd_packet.pwrite = arg0
        return cmd_packet.pack_cmd_packet()


# class APBMaster(APBBase):
#     def __init__(self, dut, name, clock, registers=None,
#                  ready_constraints=None, ready_weights=None,
#                  error_constraints=None, error_weights=None,
#                  addr_mask=None, debug=False, error_overflow=False):
#         APBBase.__init__(self, dut, name, clock, False)
#         self.log.info('Starting APBMaster')
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
#         self.log.info(f"APB Master {self.name} - Register Dump:")
#         self.log.info(self.mem.dump())

#     async def reset_bus(self):
#         self.log.info(f'Resetting APB Bus {self.name}')
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
