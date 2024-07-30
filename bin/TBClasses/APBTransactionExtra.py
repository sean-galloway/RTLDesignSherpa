from TBBase import TBBase
from APB import APBCycle, pwrite, apb_signals, apb_optional_signals
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

class APBTransactionExtra(Randomized):
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
