"""
Scoreboard for verification between APB and GAXI protocols
"""
from collections import deque, defaultdict
import cocotb
from cocotb.triggers import Timer

class APBGAXIScoreboard:
    """
    Scoreboard for verifying APB and GAXI transactions match.

    This scoreboard can:
    1. Verify APB transactions against GAXI transactions
    2. Track transactions by address
    3. Report mismatches in data or control signals
    4. Provide coverage statistics
    """

    def __init__(self, name, log=None):
        """
        Initialize the APB-GAXI scoreboard.

        Args:
            name: Scoreboard name
            log: Logger instance
        """
        self.name = name
        self.log = log

        # Transaction queues indexed by direction and address
        self.apb_writes = defaultdict(deque)
        self.apb_reads = defaultdict(deque)
        self.gaxi_writes = defaultdict(deque)
        self.gaxi_reads = defaultdict(deque)

        # Verification statistics
        self.total_matches = 0
        self.total_mismatches = 0
        self.total_dropped = 0
        self.total_verified = 0
        self.address_coverage = set()
        self.type_coverage = {"apb_write": 0, "apb_read": 0,
                              "gaxi_write": 0, "gaxi_read": 0}

    def add_apb_transaction(self, transaction):
        """
        Add an APB transaction to the scoreboard.

        Args:
            transaction: APB transaction to add
        """
        addr = transaction.paddr & 0xFFF  # Use 12-bit address for indexing

        if transaction.direction == "WRITE":
            self.apb_writes[addr].append(transaction)
            self.type_coverage["apb_write"] += 1
            self.log.debug(f"APB Write added to scoreboard: addr=0x{addr:08X}, data=0x{transaction.pwdata:08X}")
        else:
            self.apb_reads[addr].append(transaction)
            self.type_coverage["apb_read"] += 1
            self.log.debug(f"APB Read added to scoreboard: addr=0x{addr:08X}, data=0x{transaction.prdata:08X}")

        self.address_coverage.add(addr)

        # Check for matches
        if transaction.direction == "WRITE":
            self._check_write_matches(addr, transaction, is_apb=True)
        else:
            self._check_read_matches(addr, transaction, is_apb=True)

    def add_gaxi_transaction(self, transaction):
        """
        Add a GAXI transaction to the scoreboard.

        Args:
            transaction: GAXI transaction to add
        """
        addr = transaction.addr & 0xFFF  # Use 12-bit address for indexing

        if transaction.cmd == 1:  # Write
            self.gaxi_writes[addr].append(transaction)
            self.type_coverage["gaxi_write"] += 1
            self.log.debug(f"GAXI Write added to scoreboard: addr=0x{addr:08X}, data=0x{transaction.data:08X}")
        else:  # Read
            self.gaxi_reads[addr].append(transaction)
            self.type_coverage["gaxi_read"] += 1
            self.log.debug(f"GAXI Read added to scoreboard: addr=0x{addr:08X}, data=0x{transaction.data:08X}")

        self.address_coverage.add(addr)

        # Check for matches
        if transaction.cmd == 1:  # Write
            self._check_write_matches(addr, transaction, is_apb=False)
        else:  # Read
            self._check_read_matches(addr, transaction, is_apb=False)

    def _check_write_matches(self, addr, transaction, is_apb=True):
        """
        Check for write transaction matches.

        Args:
            addr: Transaction address
            transaction: New transaction
            is_apb: True if transaction is APB, False if GAXI
        """
        if is_apb:
            # Check if we have a matching GAXI write
            if self.gaxi_writes[addr]:
                gaxi_transaction = self.gaxi_writes[addr].popleft()
                if transaction.pwdata != gaxi_transaction.data:
                    self.log.error(
                        f"Write data mismatch at addr 0x{addr:08X}: "
                        f"APB=0x{transaction.pwdata:08X}, GAXI=0x{gaxi_transaction.data:08X}"
                    )
                    self.total_mismatches += 1
                else:
                    self.log.debug(
                        f"Matched write at addr 0x{addr:08X}: "
                        f"APB=0x{transaction.pwdata:08X}, GAXI=0x{gaxi_transaction.data:08X}"
                    )
                    self.total_matches += 1
                self.total_verified += 1
        else:
            # Check if we have a matching APB write
            if self.apb_writes[addr]:
                apb_transaction = self.apb_writes[addr].popleft()
                if apb_transaction.pwdata != transaction.data:
                    self.log.error(
                        f"Write data mismatch at addr 0x{addr:08X}: "
                        f"APB=0x{apb_transaction.pwdata:08X}, GAXI=0x{transaction.data:08X}"
                    )
                    self.total_mismatches += 1
                else:
                    self.log.debug(
                        f"Matched write at addr 0x{addr:08X}: "
                        f"APB=0x{apb_transaction.pwdata:08X}, GAXI=0x{transaction.data:08X}"
                    )
                    self.total_matches += 1
                self.total_verified += 1

    def _check_read_matches(self, addr, transaction, is_apb=True):
        """
        Check for read transaction matches.

        Args:
            addr: Transaction address
            transaction: New transaction
            is_apb: True if transaction is APB, False if GAXI
        """
        if is_apb:
            # Check if we have a matching GAXI read
            if self.gaxi_reads[addr]:
                gaxi_transaction = self.gaxi_reads[addr].popleft()
                if transaction.prdata != gaxi_transaction.data:
                    self.log.error(
                        f"Read data mismatch at addr 0x{addr:08X}: "
                        f"APB=0x{transaction.prdata:08X}, GAXI=0x{gaxi_transaction.data:08X}"
                    )
                    self.total_mismatches += 1
                else:
                    self.log.debug(
                        f"Matched read at addr 0x{addr:08X}: "
                        f"APB=0x{transaction.prdata:08X}, GAXI=0x{gaxi_transaction.data:08X}"
                    )
                    self.total_matches += 1
                self.total_verified += 1
        else:
            # Check if we have a matching APB read
            if self.apb_reads[addr]:
                apb_transaction = self.apb_reads[addr].popleft()
                if apb_transaction.prdata != transaction.data:
                    self.log.error(
                        f"Read data mismatch at addr 0x{addr:08X}: "
                        f"APB=0x{apb_transaction.prdata:08X}, GAXI=0x{transaction.data:08X}"
                    )
                    self.total_mismatches += 1
                else:
                    self.log.debug(
                        f"Matched read at addr 0x{addr:08X}: "
                        f"APB=0x{apb_transaction.prdata:08X}, GAXI=0x{transaction.data:08X}"
                    )
                    self.total_matches += 1
                self.total_verified += 1

    async def check_scoreboard(self, timeout=None):
        """
        Check scoreboard for unmatched transactions.

        Args:
            timeout: Optional timeout in ns before checking

        Returns:
            True if all transactions matched, False otherwise
        """
        if timeout:
            await Timer(timeout, units='ns')

        # Check for unmatched transactions
        unmatched = 0

        for addr, queue in self.apb_writes.items():
            if queue:
                unmatched += len(queue)
                self.log.warning(f"Unmatched APB writes at addr 0x{addr:08X}: {len(queue)}")
                for tx in queue:
                    self.log.warning(f"  APB write: data=0x{tx.pwdata:08X}")

        for addr, queue in self.apb_reads.items():
            if queue:
                unmatched += len(queue)
                self.log.warning(f"Unmatched APB reads at addr 0x{addr:08X}: {len(queue)}")
                for tx in queue:
                    self.log.warning(f"  APB read: data=0x{tx.prdata:08X}")

        for addr, queue in self.gaxi_writes.items():
            if queue:
                unmatched += len(queue)
                self.log.warning(f"Unmatched GAXI writes at addr 0x{addr:08X}: {len(queue)}")
                for tx in queue:
                    self.log.warning(f"  GAXI write: data=0x{tx.data:08X}")

        for addr, queue in self.gaxi_reads.items():
            if queue:
                unmatched += len(queue)
                self.log.warning(f"Unmatched GAXI reads at addr 0x{addr:08X}: {len(queue)}")
                for tx in queue:
                    self.log.warning(f"  GAXI read: data=0x{tx.data:08X}")

        self.total_dropped = unmatched
        self.log.info(f"Scoreboard check: {self.total_matches} matches, {self.total_mismatches} mismatches, {self.total_dropped} unmatched")

        # Report coverage statistics
        self.log.info(f"Address coverage: {len(self.address_coverage)} unique addresses")
        self.log.info(f"Transaction type coverage: {self.type_coverage}")

        # Calculate verification rate
        total = self.total_verified + self.total_dropped
        verification_rate = (self.total_verified / total) * 100 if total else 0
        self.log.info(f"Verification rate: {verification_rate:.1f}% ({self.total_verified}/{total})")

        return self.total_mismatches == 0 and self.total_dropped == 0

    def report(self):
        """
        Generate a report of scoreboard statistics.

        Returns:
            String with scoreboard report
        """
        report = [
            f"=== {self.name} Report ===",
            f"Total transactions verified: {self.total_verified}",
            f"Matching transactions: {self.total_matches}",
            f"Mismatched transactions: {self.total_mismatches}",
            f"Unmatched transactions: {self.total_dropped}",
            f"Unique addresses covered: {len(self.address_coverage)}",
            f"Transaction type coverage:",
            f"  APB writes: {self.type_coverage['apb_write']}",
            f"  APB reads: {self.type_coverage['apb_read']}",
            f"  GAXI writes: {self.type_coverage['gaxi_write']}",
            f"  GAXI reads: {self.type_coverage['gaxi_read']}",
        ]

        # Calculate verification rate
        total = self.total_verified + self.total_dropped
        verification_rate = (self.total_verified / total) * 100 if total else 0
        report.append(f"Verification rate: {verification_rate:.1f}%")

        return "\n".join(report)

    def clear(self):
        """Clear all transactions and reset statistics."""
        # Clear transaction queues
        self.apb_writes.clear()
        self.apb_reads.clear()
        self.gaxi_writes.clear()
        self.gaxi_reads.clear()

        # Reset statistics
        self.total_matches = 0
        self.total_mismatches = 0
        self.total_dropped = 0
        self.total_verified = 0
        self.address_coverage.clear()
        self.type_coverage = {"apb_write": 0, "apb_read": 0,
                             "gaxi_write": 0, "gaxi_read": 0}

        self.log.info(f"Scoreboard {self.name} cleared")

