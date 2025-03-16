"""Base Scoreboard for verification components"""
from collections import deque


class BaseScoreboard:
    """Base class for all protocol scoreboards"""
    
    def __init__(self, name, log=None):
        self.name = name
        self.log = log
        self.expected_queue = deque()
        self.actual_queue = deque()
        self.error_count = 0
        self.transaction_count = 0
        self.transformer = None
        
    def add_expected(self, transaction):
        """Add transaction to expected queue"""
        if self.transformer:
            transformed_transactions = self.transformer.transform(transaction)
            for trans in transformed_transactions:
                self.expected_queue.append(trans)
        else:
            self.expected_queue.append(transaction)
        
    def add_actual(self, transaction):
        """Add transaction to actual queue and trigger comparison"""
        self.actual_queue.append(transaction)
        self.transaction_count += 1
        self._compare_next()
        
    def _compare_next(self):
        """Compare next transaction in queues if available"""
        if not self.expected_queue or not self.actual_queue:
            return
            
        expected = self.expected_queue.popleft()
        actual = self.actual_queue.popleft()
        
        if not self._compare_transactions(expected, actual):
            self.error_count += 1
            self._log_mismatch(expected, actual)
    
    def _compare_transactions(self, expected, actual):
        """Compare two transactions - override in derived classes"""
        raise NotImplementedError
        
    def _log_mismatch(self, expected, actual):
        """Log detailed information about mismatched transactions"""
        if self.log:
            self.log.error(f"{self.name} - Transaction mismatch:")
            self.log.error(f"  Expected: {expected}")
            self.log.error(f"  Actual:   {actual}")
    
    def report(self):
        """Generate report of scoreboard activity"""
        leftover_expected = len(self.expected_queue)
        leftover_actual = len(self.actual_queue)
        
        if leftover_expected > 0:
            if self.log:
                self.log.error(f"{self.name} - {leftover_expected} expected transactions not received")
                
        if leftover_actual > 0:
            if self.log:
                self.log.error(f"{self.name} - {leftover_actual} actual transactions without matching expected")
                
        total_errors = self.error_count + leftover_expected + leftover_actual
        
        if self.log:
            self.log.info(f"{self.name} - Scoreboard summary:")
            self.log.info(f"  Transactions: {self.transaction_count}")
            self.log.info(f"  Errors: {total_errors}")
            
        return total_errors
    
    def set_transformer(self, transformer):
        """Set a protocol transformer for the scoreboard"""
        self.transformer = transformer
        
    def clear(self):
        """Clear all queues and reset counters"""
        self.expected_queue.clear()
        self.actual_queue.clear()
        self.error_count = 0
        self.transaction_count = 0


class ProtocolTransformer:
    """Base class for protocol transformations"""
    
    def __init__(self, source_protocol, target_protocol, log=None):
        self.source_protocol = source_protocol
        self.target_protocol = target_protocol
        self.log = log
        
    def transform(self, source_transaction):
        """
        Transform source transaction to target protocol
        
        Args:
            source_transaction: Transaction to transform
            
        Returns:
            List of transformed transactions
        """
        raise NotImplementedError
