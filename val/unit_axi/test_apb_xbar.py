import cocotb
from cocotb.triggers import RisingEdge, Timer
from cocotb.clock import Clock
from cocotb.queue import Queue
from cocotb.utils import get_sim_time
import os
import subprocess
import random
import math
import pytest
from cocotb_test.simulator import run
from TBBase import TBBase
from DelayRandomizer import DelayRandomizer
from ConstrainedRandom import ConstrainedRandom
from APB import APBTransaction, APBMonitor, APBSlave, APBMaster
from collections import deque


class APBXbar_TB(TBBase):
    def __init__(self, dut):
        TBBase.__init__(self, dut)
        self.M = self.convert_to_int(os.environ.get('PARAM_M', '0'))
        self.S = self.convert_to_int(os.environ.get('PARAM_S', '0'))
        self.ADDR_WIDTH = self.convert_to_int(os.environ.get('PARAM_ADDR_WIDTH', '0'))
        self.DATA_WIDTH = self.convert_to_int(os.environ.get('PARAM_DATA_WIDTH', '0'))
        self.STRB_WIDTH = self.DATA_WIDTH // 8
        self.SLAVE_ENABLE = [1, 1, 1, 1, 1] 
        self.SLAVE_ADDR_BASE =  [0x000, 0x1000, 0x2000, 0x3000, 0x4000]
        self.SLAVE_ADDR_LIMIT = [0xFFF, 0x1FFF, 0x2FFF, 0x3FFF, 0x4FFF]
        self.THRESHOLDS = [4, 4, 4]

        self.registers = 32 * self.STRB_WIDTH
        self.slave_register = list(range(self.registers))

        # Create the Monitors
        self.apb_master_mon = []
        self.apb_slave_mon = []
        for i in range(self.M):
            mon = APBMonitor(dut, f'm{i}_apb', dut.aclk, bus_width=self.DATA_WIDTH, addr_width=self.ADDR_WIDTH, log=self.log)
            self.apb_master_mon.append(mon)
        for i in range(self.S):
            mon = APBMonitor(dut, f's{i}_apb', dut.aclk, bus_width=self.DATA_WIDTH, addr_width=self.ADDR_WIDTH, log=self.log)
            self.apb_slave_mon.append(mon)

        # Create the Slaves
        apb_slv_constraints = {
                'ready': ([[0, 0], [1, 5], [6, 10]], [5, 3, 1]),
                'error': ([[0, 0], [1, 1]], [10, 0]),
        }
        self.apb_slave = []
        for i in range(self.S):
            slave   = APBSlave(dut, f's{i}_apb', dut.aclk, registers=self.slave_register,
                                    bus_width=self.DATA_WIDTH, addr_width=self.ADDR_WIDTH,
                                    constraints=apb_slv_constraints)
            self.apb_slave.append(slave)
        
        apb_mst_constraints = {
            'psel':    ([[0, 0], [1, 5], [6, 10]], [5, 2, 1]),
            'penable': ([[0, 0], [1, 2]], [4, 1]),
        }
        self.apb_master = []
        for i in range(self.M):
            master   = APBMaster(dut, f'm{i}_apb', dut.aclk,
                                    bus_width=self.DATA_WIDTH, addr_width=self.ADDR_WIDTH,
                                    constraints=apb_mst_constraints)
            self.apb_master.append(master)
        # Set up some standard test variables
        self.addr_decode = [ 
                        [0x0000, 0x0FFC],
                        [0x1000, 0x1FFC],
                        [0x2000, 0x2FFC],
                        [0x3000, 0x3FFC],
                        [0x4000, 0x4FFC],
                        [0x5000, 0x5FFC],
                        [0x6000, 0x6FFC],
                        [0x7000, 0x7FFC],
                        [0x8000, 0x8FFC],
                        [0x9000, 0x9FFC]
                    ]
        self.expectQ_list = []
        for _ in range(self.S):
            self.expectQ_list.append(deque())
        self.addresses = [ 
                        0x0000, 0x0800, 0x0FFC,
                        0x1000, 0x1800, 0x1FFC,
                        0x2000, 0x2800, 0x2FFC,
                        0x3000, 0x3800, 0x3FFC,
                        0x4000, 0x4800, 0x4FFC,
                        0x5000, 0x5800, 0x5FFC,
                        0x6000, 0x6800, 0x6FFC,
                        0x7000, 0x7800, 0x7FFC,
                        0x8000, 0x8800, 0x8FFC,
                        0x9000, 0x9800, 0x9FFC
                    ]
        self.addr_min_hi = (4  * self.STRB_WIDTH)-1
        self.addr_max_lo = (4  * self.STRB_WIDTH)
        self.addr_max_hi = (32 * self.STRB_WIDTH)-1


    async def reset_dut(self):
        self.log.debug('Starting reset_dut')
        self.dut.aresetn.value = 0
        for m in self.apb_master:
            await m.reset_bus()
        for s in self.apb_slave:
            await s.reset_bus()
        await self.wait_clocks('aclk', 2)
        self.dut.aresetn.value = 1
        await self.wait_clocks('aclk', 2)
        self.log.debug('Ending reset_dut')


    def route_transaction_to_expectq(self, apb_cycle):
        """
        Route the APBCycle transaction to the correct expectQ based on the addr_decode ranges.
    
        Args:
            apb_cycle (APBCycle): The APBCycle transaction to be routed.
        """
        for idx, (addr_start, addr_end) in enumerate(self.addr_decode):
            if addr_start <= apb_cycle.paddr <= addr_end:
                self.expectQ_list[idx].append(apb_cycle)
                self.log.info(f'Transaction with address {apb_cycle.paddr:08X} routed to expectQ[{idx}]')
                return
    
        self.log.warning(f'Transaction with address {apb_cycle.paddr:08X} does not match any addr_decode range')


    def compare_expect_and_recv_queues(self):
        """
        Compare all items in the expectQ_list to the _recvQ of each APBMonitor.
        Flag an error if there are any cycles remaining in any of the queues after
        all expects are checked against the received.
        """
        error_flag = False
    
        for i in range(self.S):
            expectQ = self.expectQ_list[i]
            recvQ = self.apb_slave_mon[i]._recvQ
    
            while expectQ and recvQ:
                expected = expectQ.popleft()
                received = recvQ.popleft()
    
                if not self.compare_cycles(expected, received):
                    self.log.error(f'Mismatch in slave {i}: Expected {expected}, Received {received}')
                    error_flag = True
    
            # Check if any remaining items in expectQ or recvQ
            if expectQ:
                self.log.error(f'Expected queue for slave {i} is not empty: {list(expectQ)}')
                error_flag = True
            if recvQ:
                self.log.error(f'Received queue for slave {i} is not empty: {list(recvQ)}')
                error_flag = True
    
        if not error_flag:
            self.log.info('All transactions matched correctly between expectQ and recvQ.')
    
    
    def compare_cycles(self, expected, received):
        """
        Compare two APBCycle objects.
    
        Args:
            expected (APBCycle): The expected APBCycle object.
            received (APBCycle): The received APBCycle object.
    
        Returns:
            bool: True if the cycles match, False otherwise.
        """
        return expected == received


    async def wait_for_queue_empty(self, master, timeout=None):
        start_time = get_sim_time('ns')
        while len(master.transmit_queue) > 0 or master.transfer_busy:
            if timeout and (get_sim_time('ns') - start_time) > timeout:
                raise TimeoutError(f"Timeout waiting for queue to empty after {timeout} ns")
            await RisingEdge(self.dut.aclk)


    async def write_single_master_test(self):
        self.log.info('Starting write single master test')
        # force all writes
        constraints = {
            'last':   ([(0, 0), (1, 1)], [1, 1]),
            'first':  ([(0, 0), (1, 1)], [1, 1]),
            'pwrite': ([(0, 0), (1, 1)], [0, 1]),
            'paddr':  ([(0, self.addr_min_hi), (self.addr_max_lo, self.addr_max_hi)], [4, 1]),
            'pstrb':  ([(15, 15), (0, 14)], [4, 1]),
            'pprot':  ([(0, 0), (1, 1), (2, 2)], [1, 1, 1])
        }
        transaction_cls = APBTransaction(self.DATA_WIDTH, self.ADDR_WIDTH, self.STRB_WIDTH, constraints)
    
        for m, master in enumerate(self.apb_master):
            for idx, address in enumerate(self.addresses):
                if idx == 3*self.S:
                    break
                transaction = transaction_cls.set_constrained_random()
                transaction.pwrite = 1
                transaction.direction = "WRITE"
                self.log.info(f'Sending write from master {m} to {address:08X}')
                transaction.paddr = address
                transaction.pprot = m
                await master.send(transaction)
                self.route_transaction_to_expectq(transaction)
                await self.wait_clocks('aclk', 1)
            
            # Wait for the master's transaction queue to be empty
            self.log.info(f'Waiting for transaction queue of master {m} to empty...')
            await self.wait_for_queue_empty(master, timeout=1000)
            self.log.info(f'Transaction queue of master {m} is now empty.')

        self.log.info('Checking routing of all transactions')
        self.compare_expect_and_recv_queues()


    async def read_single_master_test(self):
        self.log.info('Starting write single master test')
        # force all writes
        constraints = {
            'last':   ([(0, 0), (1, 1)], [1, 1]),
            'first':  ([(0, 0), (1, 1)], [1, 1]),
            'pwrite': ([(0, 0), (1, 1)], [0, 1]),
            'paddr':  ([(0, self.addr_min_hi), (self.addr_max_lo, self.addr_max_hi)], [4, 1]),
            'pstrb':  ([(15, 15), (0, 14)], [4, 1]),
            'pprot':  ([(0, 0), (1, 1), (2, 2)], [1, 1, 1])
        }
        transaction_cls = APBTransaction(self.DATA_WIDTH, self.ADDR_WIDTH, self.STRB_WIDTH, constraints)
    
        for m, master in enumerate(self.apb_master):
            for idx, address in enumerate(self.addresses):
                if idx == 3*self.S:
                    break
                transaction = transaction_cls.set_constrained_random()
                transaction.pwrite = 0
                transaction.direction = "READ"
                self.log.info(f'Sending read from master {m} to {address:08X}')
                transaction.paddr = address
                transaction.pprot = m
                await master.send(transaction)
                self.route_transaction_to_expectq(transaction)
                await self.wait_clocks('aclk', 1)
            
            # Wait for the master's transaction queue to be empty
            self.log.info(f'Waiting for transaction queue of master {m} to empty...')
            await self.wait_for_queue_empty(master, timeout=1000)
            self.log.info(f'Transaction queue of master {m} is now empty.')

        self.log.info('Checking routing of all transactions')
        self.compare_expect_and_recv_queues()


    async def main_loop(self):
        await self.write_single_master_test()
        # await self.read_single_master_test()


@cocotb.test()
async def apb_xbar_wrap_test(dut):
    tb = APBXbar_TB(dut)
    # Use the seed for reproducibility
    seed = int(os.environ.get('SEED', '0'))
    random.seed(seed)
    await tb.start_clock('aclk', 10, 'ns')
    await tb.reset_dut()
    await tb.main_loop()
    await tb.wait_clocks('aclk', 50)
    tb.log.info("Test completed successfully.")

repo_root = subprocess.check_output(['git', 'rev-parse', '--show-toplevel']).strip().decode('utf-8')
tests_dir = os.path.abspath(os.path.dirname(__file__))
rtl_dir = os.path.abspath(os.path.join(repo_root, 'rtl/', 'common'))
rtl_axi_dir = os.path.abspath(os.path.join(repo_root, 'rtl/', 'axi/'))
rtl_integ_axi_dir = os.path.abspath(os.path.join(repo_root, 'rtl/', 'integ_axi/apb_xbar'))

@pytest.mark.parametrize("m, s, addr_width, data_width", 
    [
        (
            3,                   # m
            5,                   # s
            32,                  # addr_width
            32,                  # data_width
        )
    ])
def test_apb_xbar_wrap(request, m, s, addr_width, data_width):
    dut_name = "apb_xbar_wrap_m10_s10"
    module = os.path.splitext(os.path.basename(__file__))[0]
    toplevel = dut_name

    verilog_sources = [
        os.path.join(rtl_dir, "arbiter_fixed_priority.sv"),
        os.path.join(rtl_dir, "arbiter_round_robin_subinst.sv"),
        os.path.join(rtl_dir, "arbiter_weighted_round_robin.sv"),
        os.path.join(rtl_axi_dir, "apb_xbar.sv"),
        os.path.join(rtl_integ_axi_dir, f"{dut_name}.sv")
    ]
    includes = []

    print("M:               ", m)
    print("S:               ", s)
    print("ADDR_WIDTH:      ", addr_width)
    print("DATA_WIDTH:      ", data_width)

    parameters = {
        'M':                m,
        'S':                s,
        'ADDR_WIDTH':       addr_width,
        'DATA_WIDTH':       data_width
    }

    extra_env = {f'PARAM_{k}': str(v) for k, v in parameters.items()}

    sim_build = os.path.join(repo_root, 'val', 'unit_axi', 'local_sim_build', request.node.name.replace('[', '-').replace(']', ''))

    extra_env['LOG_PATH'] = os.path.join(str(sim_build), f'cocotb_log_{dut_name}.log')
    extra_env['DUT'] = dut_name

    run(
        python_search=[tests_dir],
        verilog_sources=verilog_sources,
        includes=includes,
        toplevel=toplevel,
        module=module,
        parameters=parameters,
        sim_build=sim_build,
        extra_env=extra_env,
        waves=True,
    )
