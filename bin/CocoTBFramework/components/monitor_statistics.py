class MonitorStatistics:
    """Wrapper class for storing Monitor statistics"""

    def __init__(self):
        self.received_transactions = 0
        self.transactions_observed = 0
        self.protocol_violations = 0
        self.x_z_violations = 0
        self.empty_cycles = 0
        self.full_cycles = 0
        self.read_while_empty = 0
        self.write_while_full = 0
