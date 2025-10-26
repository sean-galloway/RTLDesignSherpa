# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2025 sean galloway
#
# RTL Design Sherpa - Industry-Standard RTL Design and Verification
# https://github.com/sean-galloway/RTLDesignSherpa
#
# Module: APBTransactionExtractor
# Purpose: Fixed APB-GAXI Scoreboard - Handles both read and write responses
#
# Documentation: bin/CocoTBFramework/README.md
# Subsystem: framework
#
# Author: sean galloway
# Created: 2025-10-18

"""
Fixed APB-GAXI Scoreboard - Handles both read and write responses

Key fix: Both APB reads and writes get responses (PREADY + PSLVERR + optional PRDATA).
The original scoreboard incorrectly assumed writes don't need response matching.
"""

from collections import deque
from cocotb.utils import get_sim_time


class APBTransactionExtractor:
    """
    Helper class to extract transaction fields from both APB and GAXI packets.
    Handles both APB attribute style and GAXI fields dict style.
    """

    @staticmethod
    def extract_command_fields(transaction):
        """Extract command interface fields from transaction."""
        fields = {}

        # Extract pwrite field - supports both storage methods
        fields['pwrite'] = APBTransactionExtractor._get_field_value(transaction, 'pwrite', 0)
        fields['is_write'] = fields['pwrite'] == 1
        fields['transaction_type'] = 'WRITE' if fields['is_write'] else 'READ'

        # Extract paddr field
        fields['paddr'] = APBTransactionExtractor._get_field_value(transaction, 'paddr', 0)

        # Extract pwdata field
        fields['pwdata'] = APBTransactionExtractor._get_field_value(transaction, 'pwdata', 0)

        # Extract pstrb field
        fields['pstrb'] = APBTransactionExtractor._get_field_value(transaction, 'pstrb', 0xF)

        # Extract pprot field
        fields['pprot'] = APBTransactionExtractor._get_field_value(transaction, 'pprot', 0)

        return fields

    @staticmethod
    def extract_response_fields(transaction):
        """Extract response interface fields from transaction."""
        fields = {}

        # Extract prdata field
        fields['prdata'] = APBTransactionExtractor._get_field_value(transaction, 'prdata', 0)

        # Extract pslverr field
        fields['pslverr'] = APBTransactionExtractor._get_field_value(transaction, 'pslverr', 0)
        fields['has_error'] = fields['pslverr'] == 1
        fields['error_status'] = 'ERROR' if fields['has_error'] else 'OK'

        return fields

    @staticmethod
    def _get_field_value(transaction, field_name, default_value):
        """
        Safely extract a field value from transaction supporting both storage methods.

        Priority order:
        1. transaction.fields[field_name] (GAXI style)
        2. transaction.field_name (APB style)
        3. transaction.field_name.lower() (case variations)
        4. default_value
        """
        # FIRST: Try fields dictionary (GAXI style)
        if hasattr(transaction, 'fields') and isinstance(transaction.fields, dict):
            if field_name in transaction.fields:
                value = transaction.fields[field_name]
                if value is not None:
                    return value

        # SECOND: Try direct attribute access (APB style)
        if hasattr(transaction, field_name):
            value = getattr(transaction, field_name)
            if value is not None:
                return value

        # THIRD: Try lowercase versions (handle case variations)
        if hasattr(transaction, field_name.lower()):
            value = getattr(transaction, field_name.lower())
            if value is not None:
                return value

        # FOURTH: Return default if nothing found
        return default_value

    @staticmethod
    def format_command_transaction(fields):
        """Format command transaction for logging."""
        return (f"{fields['transaction_type']} @ addr=0x{fields['paddr']:08X}, "
                f"data=0x{fields['pwdata']:08X}, strb=0x{fields['pstrb']:X}, "
                f"prot=0x{fields['pprot']:X}")

    @staticmethod
    def format_response_transaction(fields):
        """Format response transaction for logging."""
        return (f"RESPONSE data=0x{fields['prdata']:08X}, "
                f"status={fields['error_status']}")


class APBGAXIScoreboard:
    """
    FIXED: APB-GAXI Scoreboard that properly handles both read and write responses.

    Key fix: APB protocol always provides responses for both reads and writes:
    - PREADY: indicates transaction completion
    - PSLVERR: indicates success/error status
    - PRDATA: contains data for reads (ignored for writes)
    """

    def __init__(self, name, log=None):
        """Initialize the APB-GAXI scoreboard."""
        self.name = name
        self.log = log

        # Transaction queues
        self.apb_queue = deque()
        self.gaxi_cmd_queue = deque()
        self.gaxi_rsp_queue = deque()

        # Statistics tracking
        self.stats = {
            'apb_transactions': 0,
            'gaxi_cmd_transactions': 0,
            'gaxi_rsp_transactions': 0,
            'matched_pairs': 0,
            'matched_write_responses': 0,  # NEW: Track write response matches
            'matched_read_responses': 0,   # NEW: Track read response matches
            'unmatched_apb': 0,
            'unmatched_gaxi_cmd': 0,
            'unmatched_gaxi_rsp': 0,
            'error_transactions': 0,
            'field_extraction_errors': 0,
            'transaction_type_errors': 0
        }

        # Configuration
        self.match_timeout_ns = 10000  # 10us timeout for matching

    def add_apb_transaction(self, transaction):
        """Add an APB transaction to the scoreboard."""
        time_ns = get_sim_time('ns')

        try:
            # Extract APB transaction fields using the enhanced extractor
            apb_fields = {
                'pwrite': APBTransactionExtractor._get_field_value(transaction, 'pwrite', 0),
                'paddr': APBTransactionExtractor._get_field_value(transaction, 'paddr', 0),
                'pwdata': APBTransactionExtractor._get_field_value(transaction, 'pwdata', 0),
                'prdata': APBTransactionExtractor._get_field_value(transaction, 'prdata', 0),
                'pstrb': APBTransactionExtractor._get_field_value(transaction, 'pstrb', 0xF),
                'pprot': APBTransactionExtractor._get_field_value(transaction, 'pprot', 0),
                'pslverr': APBTransactionExtractor._get_field_value(transaction, 'pslverr', 0)
            }

            apb_fields['is_write'] = apb_fields['pwrite'] == 1
            apb_fields['transaction_type'] = 'WRITE' if apb_fields['is_write'] else 'READ'
            apb_fields['has_error'] = apb_fields['pslverr'] == 1

            # Store in APB queue
            self.apb_queue.append({
                'fields': apb_fields,
                'timestamp': time_ns,
                'transaction': transaction
            })

            self.stats['apb_transactions'] += 1

            if self.log:
                if apb_fields['is_write']:
                    self.log.debug(f"APB WRITE added @ {time_ns}ns: addr=0x{apb_fields['paddr']:08X}, "
                                    f"data=0x{apb_fields['pwdata']:08X}, strb=0x{apb_fields['pstrb']:X}, "
                                    f"err={apb_fields['has_error']}")
                else:
                    self.log.debug(f"APB READ added @ {time_ns}ns: addr=0x{apb_fields['paddr']:08X}, "
                                    f"data=0x{apb_fields['prdata']:08X}, err={apb_fields['has_error']}")

        except Exception as e:
            self.stats['field_extraction_errors'] += 1
            if self.log:
                self.log.error(f"Error extracting APB transaction fields: {e}")

        # Try to match transactions
        self._match_transactions()

    def add_gaxi_transaction(self, transaction):
        """Add a GAXI transaction to the scoreboard."""
        time_ns = get_sim_time('ns')

        try:
            # Improved transaction type detection using the enhanced field extraction
            has_cmd_fields = (
                APBTransactionExtractor._get_field_value(transaction, 'pwrite', None) is not None or
                APBTransactionExtractor._get_field_value(transaction, 'paddr', None) is not None or
                APBTransactionExtractor._get_field_value(transaction, 'pwdata', None) is not None
            )
            has_rsp_fields = (
                APBTransactionExtractor._get_field_value(transaction, 'prdata', None) is not None or
                APBTransactionExtractor._get_field_value(transaction, 'pslverr', None) is not None
            )

            if self.log:
                self.log.debug(f"GAXI transaction analysis: has_cmd_fields={has_cmd_fields}, "
                              f"has_rsp_fields={has_rsp_fields}")

            if has_cmd_fields and not has_rsp_fields:
                # This is a command transaction
                self._add_gaxi_command(transaction, time_ns)
            elif has_rsp_fields and not has_cmd_fields:
                # This is a response transaction
                self._add_gaxi_response(transaction, time_ns)
            else:
                # Mixed fields or unclear - try to determine primary type
                pwrite_val = APBTransactionExtractor._get_field_value(transaction, 'pwrite', None)
                paddr_val = APBTransactionExtractor._get_field_value(transaction, 'paddr', None)

                if pwrite_val is not None or paddr_val is not None:
                    if self.log:
                        self.log.debug(f"GAXI transaction has mixed fields, treating as command based on pwrite/paddr")
                    self._add_gaxi_command(transaction, time_ns)
                else:
                    if self.log:
                        self.log.debug(f"GAXI transaction has mixed fields, treating as response")
                    self._add_gaxi_response(transaction, time_ns)

        except Exception as e:
            self.stats['transaction_type_errors'] += 1
            if self.log:
                self.log.error(f"Error processing GAXI transaction: {e}")

    def _add_gaxi_command(self, transaction, time_ns):
        """Add GAXI command transaction."""
        try:
            cmd_fields = APBTransactionExtractor.extract_command_fields(transaction)

            # Store in GAXI command queue
            self.gaxi_cmd_queue.append({
                'fields': cmd_fields,
                'timestamp': time_ns,
                'transaction': transaction
            })

            self.stats['gaxi_cmd_transactions'] += 1

            if self.log:
                formatted = APBTransactionExtractor.format_command_transaction(cmd_fields)
                self.log.debug(f"GAXI CMD added @ {time_ns}ns: {formatted}")

        except Exception as e:
            self.stats['field_extraction_errors'] += 1
            if self.log:
                self.log.error(f"Error adding GAXI command: {e}")

        # Try to match transactions
        self._match_transactions()

    def _add_gaxi_response(self, transaction, time_ns):
        """Add GAXI response transaction."""
        try:
            rsp_fields = APBTransactionExtractor.extract_response_fields(transaction)

            # Store in GAXI response queue
            self.gaxi_rsp_queue.append({
                'fields': rsp_fields,
                'timestamp': time_ns,
                'transaction': transaction
            })

            self.stats['gaxi_rsp_transactions'] += 1

            if rsp_fields['has_error']:
                self.stats['error_transactions'] += 1

            if self.log:
                formatted = APBTransactionExtractor.format_response_transaction(rsp_fields)
                self.log.debug(f"GAXI RSP added @ {time_ns}ns: {formatted}")

        except Exception as e:
            self.stats['field_extraction_errors'] += 1
            if self.log:
                self.log.error(f"Error adding GAXI response: {e}")

        # Try to match transactions
        self._match_transactions()

    def _match_transactions(self):
        """
        FIXED: Match APB transactions with GAXI command/response pairs.

        Key fix: Both reads and writes get responses in APB protocol.
        """
        matched_indices = []

        for apb_idx, apb_item in enumerate(self.apb_queue):
            apb_fields = apb_item['fields']

            # Find matching GAXI command
            cmd_match = None
            for cmd_idx, cmd_item in enumerate(self.gaxi_cmd_queue):
                cmd_fields = cmd_item['fields']

                if self._commands_match(apb_fields, cmd_fields):
                    cmd_match = (cmd_idx, cmd_item)
                    break

            if cmd_match is None:
                continue

            cmd_idx, cmd_item = cmd_match

            # FIXED: Both reads and writes need response matching
            rsp_match = None
            for rsp_idx, rsp_item in enumerate(self.gaxi_rsp_queue):
                rsp_fields = rsp_item['fields']

                if apb_fields['is_write']:
                    # For writes, match based on error status
                    if self._write_response_matches_apb(apb_fields, rsp_fields):
                        rsp_match = (rsp_idx, rsp_item)
                        break
                else:
                    # For reads, match based on data and error status
                    if self._read_response_matches_apb(apb_fields, rsp_fields):
                        rsp_match = (rsp_idx, rsp_item)
                        break

            if rsp_match is None:
                continue

            rsp_idx, rsp_item = rsp_match

            # Remove matched transactions
            matched_indices.append(apb_idx)
            del self.gaxi_cmd_queue[cmd_idx]
            del self.gaxi_rsp_queue[rsp_idx]

            # Update statistics
            self.stats['matched_pairs'] += 1
            if apb_fields['is_write']:
                self.stats['matched_write_responses'] += 1
                if self.log:
                    self.log.info(f"✓ Matched APB WRITE with GAXI CMD+RSP: "
                                    f"addr=0x{apb_fields['paddr']:08X}, "
                                    f"data=0x{apb_fields['pwdata']:08X}, "
                                    f"err={apb_fields['has_error']}")
            else:
                self.stats['matched_read_responses'] += 1
                if self.log:
                    self.log.info(f"✓ Matched APB READ with GAXI CMD+RSP: "
                                    f"addr=0x{apb_fields['paddr']:08X}, "
                                    f"data=0x{apb_fields['prdata']:08X}, "
                                    f"err={apb_fields['has_error']}")

        # Remove matched APB transactions (in reverse order to maintain indices)
        for idx in reversed(matched_indices):
            del self.apb_queue[idx]

    def _commands_match(self, apb_fields, cmd_fields):
        """Check if APB transaction matches GAXI command."""
        # Address must match
        if apb_fields['paddr'] != cmd_fields['paddr']:
            if self.log:
                self.log.debug(f"Address mismatch: APB=0x{apb_fields['paddr']:08X}, "
                              f"GAXI=0x{cmd_fields['paddr']:08X}")
            return False

        # Transaction type must match
        if apb_fields['is_write'] != cmd_fields['is_write']:
            if self.log:
                self.log.debug(f"Transaction type mismatch: APB={apb_fields['transaction_type']}, "
                              f"GAXI={cmd_fields['transaction_type']}")
            return False

        # For writes, data must match
        if apb_fields['is_write'] and apb_fields['pwdata'] != cmd_fields['pwdata']:
            if self.log:
                self.log.debug(f"Write data mismatch: APB=0x{apb_fields['pwdata']:08X}, "
                              f"GAXI=0x{cmd_fields['pwdata']:08X}")
            return False

        return True

    def _write_response_matches_apb(self, apb_fields, rsp_fields):
        """
        NEW: Check if GAXI response matches APB write transaction.

        For writes, we primarily care about error status matching.
        The PRDATA field is ignored for writes (as per APB spec).
        """
        # Only for write transactions
        if not apb_fields['is_write']:
            return False

        # Error status should match
        if apb_fields['has_error'] != rsp_fields['has_error']:
            if self.log:
                self.log.debug(f"Write error status mismatch: APB={apb_fields['has_error']}, "
                              f"GAXI={rsp_fields['has_error']}")
            return False

        return True

    def _read_response_matches_apb(self, apb_fields, rsp_fields):
        """
        RENAMED: Check if GAXI response matches APB read transaction.

        For reads, we care about both data and error status matching.
        """
        # Only for read transactions
        if apb_fields['is_write']:
            return False

        # Read data must match
        if apb_fields['prdata'] != rsp_fields['prdata']:
            if self.log:
                self.log.debug(f"Read data mismatch: APB=0x{apb_fields['prdata']:08X}, "
                              f"GAXI=0x{rsp_fields['prdata']:08X}")
            return False

        # Error status should match
        if apb_fields['has_error'] != rsp_fields['has_error']:
            if self.log:
                self.log.debug(f"Read error status mismatch: APB={apb_fields['has_error']}, "
                              f"GAXI={rsp_fields['has_error']}")
            return False

        return True

    async def check_scoreboard(self, timeout_ns=1000):
        """Check scoreboard for unmatched transactions."""
        # Wait a bit for any pending transactions
        import cocotb
        from cocotb.triggers import Timer
        await Timer(timeout_ns, units='ns')

        # Final match attempt
        self._match_transactions()

        # Check for unmatched transactions
        self.stats['unmatched_apb'] = len(self.apb_queue)
        self.stats['unmatched_gaxi_cmd'] = len(self.gaxi_cmd_queue)
        self.stats['unmatched_gaxi_rsp'] = len(self.gaxi_rsp_queue)

        total_unmatched = (self.stats['unmatched_apb'] +
                            self.stats['unmatched_gaxi_cmd'] +
                            self.stats['unmatched_gaxi_rsp'])

        if total_unmatched > 0:
            if self.log:
                self.log.error(f"Scoreboard has {total_unmatched} unmatched transactions")
                self._log_unmatched_transactions()
            return False

        if self.log:
            self.log.info(f"✓ Scoreboard check passed: {self.stats['matched_pairs']} matched pairs "
                         f"({self.stats['matched_write_responses']} writes, {self.stats['matched_read_responses']} reads)")

        return True

    def _log_unmatched_transactions(self):
        """Log details of unmatched transactions."""
        if self.apb_queue:
            self.log.error(f"Unmatched APB transactions ({len(self.apb_queue)}):")
            for i, item in enumerate(self.apb_queue):
                fields = item['fields']
                txn_type = fields['transaction_type']
                addr = fields['paddr']
                if fields['is_write']:
                    data = fields['pwdata']
                    self.log.error(f"  {i}: {txn_type} @ addr=0x{addr:08X}, data=0x{data:08X}, err={fields['has_error']}")
                else:
                    data = fields['prdata']
                    self.log.error(f"  {i}: {txn_type} @ addr=0x{addr:08X}, data=0x{data:08X}, err={fields['has_error']}")

        if self.gaxi_cmd_queue:
            self.log.error(f"Unmatched GAXI commands ({len(self.gaxi_cmd_queue)}):")
            for i, item in enumerate(self.gaxi_cmd_queue):
                fields = item['fields']
                formatted = APBTransactionExtractor.format_command_transaction(fields)
                self.log.error(f"  {i}: {formatted}")

        if self.gaxi_rsp_queue:
            self.log.error(f"Unmatched GAXI responses ({len(self.gaxi_rsp_queue)}):")
            for i, item in enumerate(self.gaxi_rsp_queue):
                fields = item['fields']
                formatted = APBTransactionExtractor.format_response_transaction(fields)
                self.log.error(f"  {i}: {formatted}")

    def clear(self):
        """Clear all transactions from the scoreboard."""
        self.apb_queue.clear()
        self.gaxi_cmd_queue.clear()
        self.gaxi_rsp_queue.clear()

        # Reset statistics
        for key in self.stats:
            self.stats[key] = 0

    def report(self):
        """Generate comprehensive scoreboard report."""
        report = f"\n=== APB-GAXI Scoreboard Report ({self.name}) ===\n"
        report += f"APB Transactions: {self.stats['apb_transactions']}\n"
        report += f"GAXI Commands: {self.stats['gaxi_cmd_transactions']}\n"
        report += f"GAXI Responses: {self.stats['gaxi_rsp_transactions']}\n"
        report += f"Matched Pairs: {self.stats['matched_pairs']}\n"
        report += f"  - Write Responses: {self.stats['matched_write_responses']}\n"
        report += f"  - Read Responses: {self.stats['matched_read_responses']}\n"
        report += f"Error Transactions: {self.stats['error_transactions']}\n"
        report += f"Unmatched APB: {self.stats['unmatched_apb']}\n"
        report += f"Unmatched GAXI CMD: {self.stats['unmatched_gaxi_cmd']}\n"
        report += f"Unmatched GAXI RSP: {self.stats['unmatched_gaxi_rsp']}\n"
        report += f"Field Extraction Errors: {self.stats['field_extraction_errors']}\n"
        report += f"Transaction Type Errors: {self.stats['transaction_type_errors']}\n"
        report += "=" * 60

        return report

    def get_stats(self):
        """Get comprehensive scoreboard statistics."""
        return self.stats.copy()
