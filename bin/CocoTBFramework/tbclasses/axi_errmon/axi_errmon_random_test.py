"""
Random traffic test class for AXI Error Monitor.

This module provides tests with randomized traffic patterns for the AXI Error Monitor
Base module, including varied transaction types, delays, and error conditions.
"""

import random
import cocotb
from cocotb.triggers import RisingEdge

from .axi_errmon_base_test import AXIErrorMonBaseTest


class AXIErrorMonRandomTest(AXIErrorMonBaseTest):
    """
    Random traffic tests for AXI Error Monitor.
    Tests behavior under randomized traffic patterns.
    """

    def __init__(self, tb):
        """
        Initialize with a reference to the testbench

        Args:
            tb: Reference to the AXIErrorMonitorTB wrapper class
        """
        super().__init__(tb)

        # Initialize random seed
        self.seed = int(cocotb.utils.get_sim_time('ns')) & 0xFFFFFFFF
        random.seed(self.seed)

        # Transaction statistics
        self.transaction_count = 0
        self.error_transaction_count = 0
        self.normal_transaction_count = 0

    async def run(self, num_transactions=20):
        """
        Run random traffic test

        Args:
            num_transactions: Number of transactions to generate

        Returns:
            True if test passed, False otherwise
        """
        self.log.info("+"*80)
        self.log.info(f"Running random traffic test with {num_transactions} transactions (seed: {self.seed}){self.tb.get_time_ns_str()}")
        self.log.info("+"*80)

        # Reset and setup for clean test state
        await self.reset_and_setup_for_test()

        # Reset statistics
        self.transaction_count = 0
        self.error_transaction_count = 0
        self.normal_transaction_count = 0
        self.tb.errors_detected = []

        # Generate a random sequence of transactions
        initial_error_count = 0
        test_passed = await self.generate_random_traffic(num_transactions)
        final_error_count = len(self.tb.errors_detected)

        # Report statistics
        self.log.info(f"Random traffic test statistics:{self.tb.get_time_ns_str()}")
        self.log.info(f"  Total transactions: {self.transaction_count}{self.tb.get_time_ns_str()}")
        self.log.info(f"  Normal transactions: {self.normal_transaction_count}{self.tb.get_time_ns_str()}")
        self.log.info(f"  Error transactions: {self.error_transaction_count}{self.tb.get_time_ns_str()}")
        self.log.info(f"  Errors detected: {final_error_count - initial_error_count}{self.tb.get_time_ns_str()}")

        if test_passed:
            self.log.info(f"Random traffic test passed successfully{self.tb.get_time_ns_str()}")
        else:
            self.log.error(f"Random traffic test failed{self.tb.get_time_ns_str()}")

        return test_passed

    async def generate_random_traffic(self, num_transactions):
        """
        Generate random traffic pattern focusing only on response errors

        Updated for write mode to account for the single shared FIFO.

        Args:
            num_transactions: Number of transactions to generate

        Returns:
            True if test passed, False otherwise
        """
        # Transaction types
        NORMAL = 0
        RESP_ERROR = 1

        # Type names for logging
        type_names = {
            NORMAL: "NORMAL",
            RESP_ERROR: "RESP_ERROR"
        }

        # Define the probability of each transaction type
        transaction_probabilities = [
            (NORMAL, 0.7),            # 70% normal transactions
            (RESP_ERROR, 0.3)         # 30% response errors
        ]

        # Create weights for random choices
        transaction_types = [t[0] for t in transaction_probabilities]
        weights = [t[1] for t in transaction_probabilities]

        # Reset counters
        self.transaction_count = 0
        self.error_transaction_count = 0
        self.normal_transaction_count = 0

        # Lists to track transactions and errors
        transactions = []
        expected_errors = []

        # Ensure error FIFO ready is high
        # self.tb.ready_ctrl.set_error_ready(1)
        await self.tb.wait_clocks('aclk', 5)

        # Generate random transactions
        all_succeeded = True

        if self.tb.is_read:
            # Original approach for read mode
            for i in range(num_transactions):
                # Select random transaction type
                transaction_type = random.choices(transaction_types, weights=weights)[0]

                # Select random channel/ID
                id_value = random.randrange(0, self.tb.channels)

                # Select random address
                addr = random.randrange(0, 0xF000, 0x100)

                # Select random data value
                data_value = random.randrange(0, 0xFFFFFFFF)

                # Response value for error transactions
                resp_value = 0  # OKAY by default
                if transaction_type == RESP_ERROR:
                    resp_value = random.choice([2, 3])  # SLVERR or DECERR
                    self.error_transaction_count += 1
                    expected_errors.append({
                        'type': 'resp_error',
                        'addr': addr,
                        'id': id_value
                    })
                else:  # NORMAL
                    self.normal_transaction_count += 1

                # Update transaction count
                self.transaction_count += 1

                # Log transaction details in compact format
                self.log.info(f"TX{i:02d}: {type_names[transaction_type]} addr=0x{addr:X} id={id_value} resp={resp_value}{self.tb.get_time_ns_str()}")

                # Create and send transaction
                transaction = await self.drive_basic_transaction(
                    addr=addr,
                    id_value=id_value,
                    data_value=data_value,
                    resp_value=resp_value,
                    control_ready=False,  # Use default ready behavior
                    pipeline_phases=False,  # No pipelining for simplicity
                    wait_for_completion=True,  # Wait for completion
                    wait_prev_completion=True  # Wait for previous transaction
                )

                # Store transaction details
                transactions.append({
                    'id': i,
                    'type': transaction_type,
                    'type_name': type_names[transaction_type],
                    'addr': addr,
                    'id_value': id_value,
                    'data': data_value,
                    'resp': resp_value,
                    'should_error': transaction_type == RESP_ERROR
                })

                # Small pause between transactions
                await self.tb.wait_clocks('aclk', 10)

                # Periodically log progress
                if i % 5 == 0 and i > 0:
                    self.log.info(f"Progress: {i}/{num_transactions} transactions completed{self.tb.get_time_ns_str()}")
        else:
            # Modified approach for write mode with shared FIFO
            # For write mode, we need to be more careful about filling the FIFO

            # Limit active transactions to avoid timeout waiting for FIFO space
            max_active_transactions = self.tb.addr_fifo_depth  # Same as shared FIFO depth
            active_tasks = []

            i = 0
            transactions_completed = 0

            # Keep sending transactions until we've completed the requested number
            while transactions_completed < num_transactions:
                # Only start new transactions if we have room in the FIFO
                if len(active_tasks) < max_active_transactions and i < num_transactions:
                    # Select random transaction type
                    transaction_type = random.choices(transaction_types, weights=weights)[0]

                    # Select random channel/ID
                    id_value = random.randrange(0, self.tb.channels)

                    # Select random address
                    addr = random.randrange(0, 0xF000, 0x100)

                    # Select random data value
                    data_value = random.randrange(0, 0xFFFFFFFF)

                    # Response value for error transactions
                    resp_value = 0  # OKAY by default
                    if transaction_type == RESP_ERROR:
                        resp_value = random.choice([2, 3])  # SLVERR or DECERR
                        self.error_transaction_count += 1
                        expected_errors.append({
                            'type': 'resp_error',
                            'addr': addr,
                            'id': id_value
                        })
                    else:  # NORMAL
                        self.normal_transaction_count += 1

                    # Update transaction count
                    self.transaction_count += 1

                    # Log transaction details in compact format
                    self.log.info(f"TX{i:02d}: {type_names[transaction_type]} addr=0x{addr:X} id={id_value} resp={resp_value}{self.tb.get_time_ns_str()}")

                    # Start transaction, but don't wait for completion
                    task = cocotb.start_soon(self.drive_basic_transaction(
                        addr=addr,
                        id_value=id_value,
                        data_value=data_value,
                        resp_value=resp_value,
                        control_ready=False,  # Use default ready behavior
                        pipeline_phases=True,  # Enable pipelining for performance
                        wait_for_completion=True,  # Wait for completion within the task
                        wait_prev_completion=False  # We're managing this ourselves
                    ))

                    # Store task with transaction details
                    active_tasks.append({
                        'task': task,
                        'id': i,
                        'type': transaction_type,
                        'type_name': type_names[transaction_type],
                        'addr': addr,
                        'id_value': id_value,
                        'data': data_value,
                        'resp': resp_value,
                        'should_error': transaction_type == RESP_ERROR
                    })

                    i += 1

                # Check for completed tasks
                completed_indices = []
                for task_idx, task_info in enumerate(active_tasks):
                    if task_info['task'].done():
                        transactions_completed += 1
                        transactions.append({
                            'id': task_info['id'],
                            'type': task_info['type'],
                            'type_name': task_info['type_name'],
                            'addr': task_info['addr'],
                            'id_value': task_info['id_value'],
                            'data': task_info['data'],
                            'resp': task_info['resp'],
                            'should_error': task_info['should_error']
                        })
                        completed_indices.append(task_idx)

                # Remove completed tasks from active list (in reverse order to avoid index issues)
                for idx in sorted(completed_indices, reverse=True):
                    del active_tasks[idx]

                # Log progress if tasks completed
                if completed_indices and transactions_completed % 5 == 0:
                    self.log.info(f"Progress: {transactions_completed}/{num_transactions} transactions completed{self.tb.get_time_ns_str()}")

                # Small pause to allow tasks to progress
                await self.tb.wait_clocks('aclk', 5)

            # Wait for any remaining active tasks to complete
            while active_tasks:
                completed_indices = []
                for task_idx, task_info in enumerate(active_tasks):
                    if task_info['task'].done():
                        transactions_completed += 1
                        transactions.append({
                            'id': task_info['id'],
                            'type': task_info['type'],
                            'type_name': task_info['type_name'],
                            'addr': task_info['addr'],
                            'id_value': task_info['id_value'],
                            'data': task_info['data'],
                            'resp': task_info['resp'],
                            'should_error': task_info['should_error']
                        })
                        completed_indices.append(task_idx)

                # Remove completed tasks
                for idx in sorted(completed_indices, reverse=True):
                    del active_tasks[idx]

                # Exit early if everything is done
                if not active_tasks:
                    break

                # Wait a bit for more tasks to complete
                await self.tb.wait_clocks('aclk', 10)

        # Log expected errors
        self.log.info(f"Expected errors: {len(expected_errors)}{self.tb.get_time_ns_str()}")
        for i, err in enumerate(expected_errors):
            self.log.info(f"  Expected Error {i}: type={err['type']}, addr=0x{err['addr']:X}, id={err['id']}{self.tb.get_time_ns_str()}")

        # Wait for error reporting to complete
        self.log.info(f"Waiting for error reporting to complete{self.tb.get_time_ns_str()}")

        # Make sure error_ready is high
        # self.tb.ready_ctrl.set_error_ready(1)
        await self.tb.wait_clocks('aclk', 200)

        # Verify error counts match expectations
        actual_errors = len(self.tb.errors_detected)
        if actual_errors < self.error_transaction_count:
            self.log.error(f"Not all errors were detected: expected {self.error_transaction_count}, got {actual_errors}{self.tb.get_time_ns_str()}")

            # Log which expected errors were not detected
            for i, err in enumerate(expected_errors):
                error_detected = False
                for detected in self.tb.errors_detected:
                    if (detected['addr'] == err['addr'] and detected['id'] == err['id']):
                        error_detected = True
                        break

                if not error_detected:
                    self.log.error(f"  Missing Error: type={err['type']}, addr=0x{err['addr']:X}, id={err['id']}{self.tb.get_time_ns_str()}")

            all_succeeded = False

        # Log detected errors
        self.log.info(f"Detected errors: {actual_errors}{self.tb.get_time_ns_str()}")
        for i, err in enumerate(self.tb.errors_detected):
            self.log.info(f"  Detected Error {i}: type=0x{err['type']:X}, addr=0x{err['addr']:X}, id={err['id']}{self.tb.get_time_ns_str()}")

        # Print statistics
        self.log.info(f"Random traffic test statistics:{self.tb.get_time_ns_str()}")
        self.log.info(f"  Total transactions: {self.transaction_count}{self.tb.get_time_ns_str()}")
        self.log.info(f"  Normal transactions: {self.normal_transaction_count}{self.tb.get_time_ns_str()}")
        self.log.info(f"  Error transactions: {self.error_transaction_count}{self.tb.get_time_ns_str()}")
        self.log.info(f"  Errors detected: {actual_errors}{self.tb.get_time_ns_str()}")

        # Return overall success
        return all_succeeded

    async def test_random_burst(self):
        """
        Test random burst of transactions

        This test generates a burst of transactions with random IDs and
        addresses to simulate heavy traffic.

        Returns:
            True if test passed, False otherwise
        """
        self.log.info(f"Testing random burst{self.tb.get_time_ns_str()}")

        # Number of transactions in the burst
        burst_size = 20

        # Generate random IDs and addresses
        ids = [random.randrange(0, self.tb.channels) for _ in range(burst_size)]
        addresses = [random.randrange(0, 0xF000, 0x100) for _ in range(burst_size)]

        # Launch all transactions concurrently
        tasks = []

        for i in range(burst_size):
            task = cocotb.start_soon(self.drive_basic_transaction(
                addr=addresses[i],
                id_value=ids[i],
                data_value=random.randrange(0, 0xFFFFFFFF),
                resp_value=0,  # All OKAY
                control_ready=False,  # Default ready behavior
                pipeline_phases=True,  # Enable pipelining for write mode
                wait_for_completion=False
            ))
            tasks.append(task)

            # Small delay between launches
            await self.tb.wait_clocks('aclk', 1)

        # Wait for all tasks to complete or timeout
        timeout_count = 0
        max_timeout = 1000

        while tasks and timeout_count < max_timeout:
            # Check if any tasks are done
            completed_tasks = [t for t in tasks if t.done()]

            # Remove completed tasks
            for task in completed_tasks:
                tasks.remove(task)

            # Wait if tasks remain
            if tasks:
                await self.tb.wait_clocks('aclk', 1)
                timeout_count += 1

        # Check if all tasks completed
        if tasks:
            self.log.error(f"Not all burst transactions completed: {len(tasks)} remaining{self.tb.get_time_ns_str()}")
            return False

        # Additional wait to allow any delayed errors
        await self.tb.wait_clocks('aclk', 50)

        # Check for unexplained errors
        if len(self.tb.errors_detected) > 0:
            self.log.error(f"Errors detected during random burst: {len(self.tb.errors_detected)}{self.tb.get_time_ns_str()}")
            for error in self.tb.errors_detected:
                self.log.error(f"  Error: type={error['type_str']}, id={error['id']}, addr=0x{error['addr']:X}{self.tb.get_time_ns_str()}")
            return False

        self.log.info(f"Random burst test passed successfully{self.tb.get_time_ns_str()}")
        return True