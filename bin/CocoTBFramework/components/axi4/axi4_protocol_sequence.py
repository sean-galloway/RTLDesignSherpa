        self.performance_sequences[name] = sequence
        self.stats['performance_sequences'] += 1
        self.stats['total_sequences'] += 1
        return self

    def register_protocol_violation(self, id_value: int, is_read: bool, message: str) -> 'AXI4ProtocolSequence':
        """
        Register a protocol violation for a specific transaction.
        
        Args:
            id_value: Transaction ID
            is_read: True if this is a read transaction, False for write
            message: Description of the violation
            
        Returns:
            Self for method chaining
        """
        key = f"{'R' if is_read else 'W'}-{id_value}"
        self.protocol_violations[key].append(message)
        self.stats['protocol_violations'] += 1
        return self

    def get_protocol_violations(self, id_value: int, is_read: bool) -> List[str]:
        """
        Get all protocol violations for a specific transaction.
        
        Args:
            id_value: Transaction ID
            is_read: True if this is a read transaction, False for write
            
        Returns:
            List of violation messages
        """
        key = f"{'R' if is_read else 'W'}-{id_value}"
        return self.protocol_violations.get(key, [])

    def has_protocol_violations(self, id_value: int, is_read: bool) -> bool:
        """
        Check if a transaction has any protocol violations.
        
        Args:
            id_value: Transaction ID
            is_read: True if this is a read transaction, False for write
            
        Returns:
            True if the transaction has any protocol violations
        """
        key = f"{'R' if is_read else 'W'}-{id_value}"
        return key in self.protocol_violations and len(self.protocol_violations[key]) > 0

    def get_transaction_sequence(self) -> AXI4TransactionSequence:
        """
        Get the main transaction sequence.
        
        Returns:
            The transaction sequence
        """
        return self.transaction_sequence

    def get_all_sequences(self) -> Dict[str, Dict[str, AXI4TransactionSequence]]:
        """
        Get all specialized sequences.
        
        Returns:
            Dictionary of all specialized sequences by category
        """
        return {
            'error': self.error_sequences,
            'boundary': self.boundary_sequences,
            'compliance': self.compliance_sequences,
            'performance': self.performance_sequences
        }

    def get_stats(self) -> Dict[str, Any]:
        """
        Get statistics about all sequences.
        
        Returns:
            Dictionary with statistics
        """
        stats = self.stats.copy()
        stats['transaction_stats'] = self.transaction_sequence.get_stats()
        return stats

    # ========================================================================
    # Error Sequence Factories
    # ========================================================================
    
    def create_slverr_response_sequence(self) -> 'AXI4ProtocolSequence':
        """
        Create a sequence that tests handling of SLVERR responses.
        
        Returns:
            Self for method chaining
        """
        # Create a transaction sequence
        sequence = AXI4TransactionSequence(
            name="slverr_resp",
            id_width=self.id_width,
            addr_width=self.addr_width,
            data_width=self.data_width,
            user_width=self.user_width
        )
        
        # Base address for test
        addr = 0x10000000
        
        # Add regular write transactions
        write_ids = []
        for i in range(5):
            write_id = sequence.add_write_transaction(
                addr=addr + (i * 4),
                data_values=[0xA0000000 + i]
            )
            write_ids.append(write_id)
        
        # Add read transactions that will receive error responses
        read_ids = []
        for i in range(5):
            read_id = sequence.add_read_transaction(
                addr=addr + (i * 4),
                dependencies=[write_ids[i]]  # Depend on corresponding write
            )
            read_ids.append(read_id)
            
            # Add expected error response
            sequence.add_read_response_data(
                id_value=read_id,
                data_values=[0],
                resp_values=[self.RESP_SLVERR]  # SLVERR response
            )
        
        # Add the sequence to our error sequences
        self.add_error_sequence("slverr_responses", sequence)
        
        return self

    def create_decerr_response_sequence(self) -> 'AXI4ProtocolSequence':
        """
        Create a sequence that tests handling of DECERR responses.
        
        Returns:
            Self for method chaining
        """
        # Create a transaction sequence
        sequence = AXI4TransactionSequence(
            name="decerr_resp",
            id_width=self.id_width,
            addr_width=self.addr_width,
            data_width=self.data_width,
            user_width=self.user_width
        )
        
        # Use addresses in potentially unmapped regions
        addrs = [0xF0000000, 0xF1000000, 0xF2000000, 0xF3000000, 0xF4000000]
        
        # Add read transactions to unmapped addresses
        for i, addr in enumerate(addrs):
            read_id = sequence.add_read_transaction(
                addr=addr,
                burst_len=0  # Single beat
            )
            
            # Add expected error response
            sequence.add_read_response_data(
                id_value=read_id,
                data_values=[0],
                resp_values=[self.RESP_DECERR]  # DECERR response
            )
            
            # Also test write to same address
            sequence.add_write_transaction(
                addr=addr,
                data_values=[0xD0000000 + i]
            )
            # Write response will be checked in simulation
        
        # Add the sequence to our error sequences
        self.add_error_sequence("decerr_responses", sequence)
        
        return self

    def create_exokay_response_sequence(self) -> 'AXI4ProtocolSequence':
        """
        Create a sequence that tests handling of EXOKAY responses for exclusive access.
        
        Returns:
            Self for method chaining
        """
        # Create a transaction sequence
        sequence = AXI4TransactionSequence(
            name="exokay_resp",
            id_width=self.id_width,
            addr_width=self.addr_width,
            data_width=self.data_width,
            user_width=self.user_width
        )
        
        # Base address for test
        addr = 0x20000000
        
        # Create several exclusive access sequences
        for i in range(5):
            # First, regular write to initialize the address
            init_write_id = sequence.add_write_transaction(
                addr=addr + (i * 4),
                data_values=[0xE0000000 + i]
            )
            
            # Then, exclusive read
            read_id = sequence.add_read_transaction(
                addr=addr + (i * 4),
                burst_len=0,  # Single beat
                lock=1,  # Exclusive access
                dependencies=[init_write_id]  # Depend on initial write
            )
            
            # Add normal read response (not EXOKAY - that's for writes)
            sequence.add_read_response_data(
                id_value=read_id,
                data_values=[0xE0000000 + i],
                resp_values=[self.RESP_OKAY]
            )
            
            # Finally, exclusive write
            sequence.add_write_transaction(
                addr=addr + (i * 4),
                data_values=[0xE1000000 + i],
                lock=1,  # Exclusive access
                dependencies=[read_id]  # Depend on exclusive read
            )
            # Write response will be checked in simulation (should be EXOKAY)
        
        # Add the sequence to our error sequences
        self.add_error_sequence("exokay_responses", sequence)
        
        return self

    # ========================================================================
    # Boundary Sequence Factories
    # ========================================================================
    
    def create_4k_boundary_sequence(self) -> 'AXI4ProtocolSequence':
        """
        Create a sequence that tests 4KB boundary conditions.
        
        Returns:
            Self for method chaining
        """
        # Create a transaction sequence
        sequence = AXI4TransactionSequence(
            name="4k_boundary",
            id_width=self.id_width,
            addr_width=self.addr_width,
            data_width=self.data_width,
            user_width=self.user_width
        )
        
        # Test addresses near 4KB boundaries
        base_addr = 0x30000000
        boundary_addr = base_addr + 0x1000  # Next 4KB boundary
        
        # Test cases:
        # 1. Just before boundary (valid)
        bytes_per_beat = self.data_width // 8
        addr1 = boundary_addr - bytes_per_beat
        data1 = [0xB1000000]
        
        # 2. At boundary (valid)
        addr2 = boundary_addr
        data2 = [0xB2000000]
        
        # 3. INCR burst crossing boundary (valid but inefficient)
        addr3 = boundary_addr - (2 * bytes_per_beat)
        data3 = [0xB3000001, 0xB3000002, 0xB3000003, 0xB3000004]
        
        # 4. WRAP burst that would wrap at boundary (valid)
        addr4 = boundary_addr - (3 * bytes_per_beat)
        data4 = [0xB4000001, 0xB4000002, 0xB4000003, 0xB4000004]
        
        # Add write transactions
        sequence.add_write_transaction(
            addr=addr1,
            data_values=data1,
            burst_type=1  # INCR
        )
        
        sequence.add_write_transaction(
            addr=addr2,
            data_values=data2,
            burst_type=1  # INCR
        )
        
        sequence.add_write_transaction(
            addr=addr3,
            data_values=data3,
            burst_type=1  # INCR
        )
        
        sequence.add_write_transaction(
            addr=addr4,
            data_values=data4,
            burst_type=2,  # WRAP
            burst_size=2  # 4 bytes
        )
        
        # Add similar read transactions
        sequence.add_read_transaction(
            addr=addr1,
            burst_len=0,  # Single beat
            burst_type=1  # INCR
        )
        
        sequence.add_read_transaction(
            addr=addr2,
            burst_len=0,  # Single beat
            burst_type=1  # INCR
        )
        
        sequence.add_read_transaction(
            addr=addr3,
            burst_len=3,  # 4 beats
            burst_type=1  # INCR
        )
        
        sequence.add_read_transaction(
            addr=addr4,
            burst_len=3,  # 4 beats
            burst_type=2,  # WRAP
            burst_size=2  # 4 bytes
        )
        
        # Add the sequence to our boundary sequences
        self.add_boundary_sequence("4k_boundary", sequence)
        
        return self

    def create_unaligned_address_sequence(self) -> 'AXI4ProtocolSequence':
        """
        Create a sequence that tests unaligned address handling.
        
        Returns:
            Self for method chaining
        """
        # Create a transaction sequence
        sequence = AXI4TransactionSequence(
            name="unaligned_addr",
            id_width=self.id_width,
            addr_width=self.addr_width,
            data_width=self.data_width,
            user_width=self.user_width
        )
        
        # Base address for test
        base_addr = 0x40000000
        
        # Test cases with different alignments
        test_cases = [
            # (offset, size) - offset added to base address
            (0, 2),   # Aligned for 4 bytes
            (1, 2),   # Unaligned for 4 bytes
            (2, 2),   # Aligned for 2 bytes, unaligned for 4 bytes
            (0, 3),   # Aligned for 8 bytes
            (4, 3),   # Aligned for 4 bytes, unaligned for 8 bytes
        ]
        
        # Add transactions
        for i, (offset, size) in enumerate(test_cases):
            addr = base_addr + offset
            
            if (addr % (1 << size)) == 0:
                # Address is aligned for this size, valid transaction
                sequence.add_write_transaction(
                    addr=addr,
                    data_values=[0xC0000000 + i],
                    burst_size=size
                )
                
                sequence.add_read_transaction(
                    addr=addr,
                    burst_len=0,  # Single beat
                    burst_size=size
                )
            else:
                # Address is unaligned for this size
                # This is a protocol violation, but we'll test handling
                unaligned_addr = addr
                
                # Register expected violation
                self.register_protocol_violation(
                    id_value=i,
                    is_read=False,
                    message=f"Address 0x{unaligned_addr:X} not aligned for size {size} ({1<<size} bytes)"
                )
                
                # The transaction sequence will automatically align the address
                sequence.add_write_transaction(
                    addr=unaligned_addr,
                    data_values=[0xC1000000 + i],
                    burst_size=size
                )
                
                # Also test read with unaligned address
                self.register_protocol_violation(
                    id_value=i+10,  # Different ID for read
                    is_read=True,
                    message=f"Address 0x{unaligned_addr:X} not aligned for size {size} ({1<<size} bytes)"
                )
                
                sequence.add_read_transaction(
                    addr=unaligned_addr,
                    burst_len=0,  # Single beat
                    burst_size=size
                )
        
        # Add the sequence to our boundary sequences
        self.add_boundary_sequence("unaligned_address", sequence)
        
        return self

    def create_max_burst_sequence(self) -> 'AXI4ProtocolSequence':
        """
        Create a sequence that tests maximum burst length and size.
        
        Returns:
            Self for method chaining
        """
        # Create a transaction sequence
        sequence = AXI4TransactionSequence(
            name="max_burst",
            id_width=self.id_width,
            addr_width=self.addr_width,
            data_width=self.data_width,
            user_width=self.user_width
        )
        
        # Base address for test
        base_addr = 0x50000000
        
        # Test maximum burst length (256 beats)
        max_burst_len = 255
        
        # Create data for max length burst
        data_values = [0xAA000000 + i for i in range(max_burst_len + 1)]
        
        # Add max length write
        sequence.add_write_transaction(
            addr=base_addr,
            data_values=data_values,
            burst_type=1  # INCR
        )
        
        # Add max length read
        sequence.add_read_transaction(
            addr=base_addr,
            burst_len=max_burst_len,
            burst_type=1  # INCR
        )
        
        # Test maximum burst size for current data width
        max_burst_size = 0
        while (1 << max_burst_size) <= (self.data_width // 8):
            max_burst_size += 1
        max_burst_size -= 1  # Back up to valid size
        
        # Test max burst size
        sequence.add_write_transaction(
            addr=base_addr + 0x1000,
            data_values=[0xBB000000],
            burst_size=max_burst_size
        )
        
        sequence.add_read_transaction(
            addr=base_addr + 0x1000,
            burst_len=0,  # Single beat
            burst_size=max_burst_size
        )
        
        # Add the sequence to our boundary sequences
        self.add_boundary_sequence("max_burst", sequence)
        
        return self

    # ========================================================================
    # Compliance Sequence Factories
    # ========================================================================
    
    def create_burst_type_sequence(self) -> 'AXI4ProtocolSequence':
        """
        Create a sequence that tests all burst types as specified in the AXI4 protocol.
        
        Returns:
            Self for method chaining
        """
        # Create a transaction sequence
        sequence = AXI4TransactionSequence(
            name="burst_types",
            id_width=self.id_width,
            addr_width=self.addr_width,
            data_width=self.data_width,
            user_width=self.user_width
        )
        
        # Base address for test
        base_addr = 0x60000000
        
        # 1. FIXED burst type (address doesn't change)
        fixed_addr = base_addr
        fixed_data = [0xF0000001, 0xF0000002, 0xF0000003, 0xF0000004]
        
        sequence.add_write_transaction(
            addr=fixed_addr,
            data_values=fixed_data,
            burst_type=0  # FIXED
        )
        
        sequence.add_read_transaction(
            addr=fixed_addr,
            burst_len=3,  # 4 beats
            burst_type=0  # FIXED
        )
        
        # 2. INCR burst type (address increments)
        incr_addr = base_addr + 0x1000
        incr_data = [0xF1000001, 0xF1000002, 0xF1000003, 0xF1000004]
        
        sequence.add_write_transaction(
            addr=incr_addr,
            data_values=incr_data,
            burst_type=1  # INCR
        )
        
        sequence.add_read_transaction(
            addr=incr_addr,
            burst_len=3,  # 4 beats
            burst_type=1  # INCR
        )
        
        # 3. WRAP burst type (address wraps at boundaries)
        # For WRAP, burst_len must be 1, 3, 7, or 15 (2, 4, 8, or 16 beats)
        for wrap_len in [1, 3, 7, 15]:
            wrap_addr = base_addr + 0x2000 + (wrap_len * 0x100)
            wrap_data = [0xF2000000 + i for i in range(wrap_len + 1)]
            
            sequence.add_write_transaction(
                addr=wrap_addr,
                data_values=wrap_data,
                burst_len=wrap_len,
                burst_type=2  # WRAP
            )
            
            sequence.add_read_transaction(
                addr=wrap_addr,
                burst_len=wrap_len,
                burst_type=2  # WRAP
            )
            
        # 4. Invalid burst type (3) - protocol violation
        invalid_addr = base_addr + 0x3000
        invalid_data = [0xF3000001]
        
        # Register expected violation
        self.register_protocol_violation(
            id_value=99,  # Special ID for this test
            is_read=False,
            message="Invalid burst type: 3"
        )
        
        # This will actually use INCR due to protocol fixes in transaction sequence
        sequence.add_write_transaction(
            addr=invalid_addr,
            data_values=invalid_data,
            burst_len=0,
            burst_type=1  # Force to valid INCR
        )
        
        # Add the sequence to our compliance sequences
        self.add_compliance_sequence("burst_types", sequence)
        
        return self

    def create_protection_sequence(self) -> 'AXI4ProtocolSequence':
        """
        Create a sequence that tests all protection types as specified in the AXI4 protocol.
        
        Returns:
            Self for method chaining
        """
        # Create a transaction sequence
        sequence = AXI4TransactionSequence(
            name="protection",
            id_width=self.id_width,
            addr_width=self.addr_width,
            data_width=self.data_width,
            user_width=self.user_width
        )
        
        # Base address for test
        base_addr = 0x70000000
        
        # Test all combinations of protection bits
        for prot in range(8):
            # Decode protection bits for testing
            # Bit 0: 0=Unprivileged, 1=Privileged
            # Bit 1: 0=Secure, 1=Non-secure
            # Bit 2: 0=Data, 1=Instruction
            
            privileged = "Privileged" if (prot & 0x1) else "Unprivileged"
            secure = "Non-secure" if (prot & 0x2) else "Secure"
            access_type = "Instruction" if (prot & 0x4) else "Data"
            
            addr = base_addr + (prot * 0x100)
            data = [0xD0000000 + prot]
            
            # Add write with this protection
            sequence.add_write_transaction(
                addr=addr,
                data_values=data,
                prot=prot
            )
            
            # Add read with this protection
            sequence.add_read_transaction(
                addr=addr,
                burst_len=0,  # Single beat
                prot=prot
            )
        
        # Add the sequence to our compliance sequences
        self.add_compliance_sequence("protection", sequence)
        
        return self

    def create_exclusive_sequence(self) -> 'AXI4ProtocolSequence':
        """
        Create a sequence that tests exclusive access as specified in the AXI4 protocol.
        
        Returns:
            Self for method chaining
        """
        # Create a transaction sequence
        sequence = AXI4TransactionSequence(
            name="exclusive",
            id_width=self.id_width,
            addr_width=self.addr_width,
            data_width=self.data_width,
            user_width=self.user_width
        )
        
        # Base address for test
        base_addr = 0x80000000
        
        # 1. Successful exclusive access pair
        addr1 = base_addr
        
        # Initial write to set up the memory
        write1_id = sequence.add_write_transaction(
            addr=addr1,
            data_values=[0xE1000000],
            burst_type=1  # INCR
        )
        
        # Exclusive read
        read1_id = sequence.add_read_transaction(
            addr=addr1,
            burst_len=0,  # Single beat
            burst_type=1,  # INCR
            lock=1,  # Exclusive
            dependencies=[write1_id]
        )
        
        # Exclusive write - should succeed
        sequence.add_write_transaction(
            addr=addr1,
            data_values=[0xE1000001],
            burst_type=1,  # INCR
            lock=1,  # Exclusive
            dependencies=[read1_id]
        )
        
        # 2. Exclusive read without matching exclusive write
        addr2 = base_addr + 0x100
        
        # Initial write
        write2_id = sequence.add_write_transaction(
            addr=addr2,
            data_values=[0xE2000000],
            burst_type=1  # INCR
        )
        
        # Exclusive read
        sequence.add_read_transaction(
            addr=addr2,
            burst_len=0,  # Single beat
            burst_type=1,  # INCR
            lock=1,  # Exclusive
            dependencies=[write2_id]
        )
        
        # Normal write instead of exclusive write
        sequence.add_write_transaction(
            addr=addr2,
            data_values=[0xE2000001],
            burst_type=1,  # INCR
            lock=0  # Normal
        )
        
        # 3. Exclusive write without matching exclusive read
        addr3 = base_addr + 0x200
        
        # Direct exclusive write (protocol violation)
        self.register_protocol_violation(
            id_value=33,  # Special ID for this test
            is_read=False,
            message="Exclusive write without preceding exclusive read"
        )
        
        sequence.add_write_transaction(
            addr=addr3,
            data_values=[0xE3000000],
            burst_type=1,  # INCR
            lock=1  # Exclusive - but without preceding read
        )
        
        # Add the sequence to our compliance sequences
        self.add_compliance_sequence("exclusive", sequence)
        
        return self

    # ========================================================================
    # Performance Sequence Factories
    # ========================================================================
    
    def create_throughput_sequence(self) -> 'AXI4ProtocolSequence':
        """
        Create a sequence that tests maximum throughput with back-to-back transactions.
        
        Returns:
            Self for method chaining
        """
        # Create a transaction sequence
        sequence = AXI4TransactionSequence(
            name="throughput",
            id_width=self.id_width,
            addr_width=self.addr_width,
            data_width=self.data_width,
            user_width=self.user_width
        )
        
        # Base address for test
        base_addr = 0x90000000
        
        # Generate a large number of back-to-back write transactions
        for i in range(100):
            addr = base_addr + (i * 4)
            data = [0xA0000000 + i]
            
            sequence.add_write_transaction(
                addr=addr,
                data_values=data,
                burst_type=1  # INCR
            )
        
        # Generate a large number of back-to-back read transactions
        for i in range(100):
            addr = base_addr + (i * 4)
            
            sequence.add_read_transaction(
                addr=addr,
                burst_len=0,  # Single beat
                burst_type=1  # INCR
            )
        
        # Add the sequence to our performance sequences
        self.add_performance_sequence("throughput", sequence)
        
        return self

    def create_interleaved_sequence(self) -> 'AXI4ProtocolSequence':
        """
        Create a sequence that tests interleaved transactions using multiple IDs.
        
        Returns:
            Self for method chaining
        """
        # Create a transaction sequence
        sequence = AXI4TransactionSequence(
            name="interleaved",
            id_width=self.id_width,
            addr_width=self.addr_width,
            data_width=self.data_width,
            user_width=self.user_width
        )
        
        # Base address for test
        base_addr = 0xA0000000
        
        # Generate interleaved write transactions with different IDs
        for i in range(10):
            for id_value in range(4):
                addr = base_addr + (id_value * 0x1000) + (i * 4)
                data = [0xB0000000 + (id_value << 8) + i]
                
                sequence.add_write_transaction(
                    addr=addr,
                    data_values=data,
                    id_value=id_value,
                    burst_type=1  # INCR
                )
        
        # Generate interleaved read transactions with different IDs
        for i in range(10):
            for id_value in range(4):
                addr = base_addr + (id_value * 0x1000) + (i * 4)
                
                sequence.add_read_transaction(
                    addr=addr,
                    burst_len=0,  # Single beat
                    id_value=id_value,
                    burst_type=1  # INCR
                )
        
        # Add the sequence to our performance sequences
        self.add_performance_sequence("interleaved", sequence)
        
        return self

    def create_quality_of_service_sequence(self) -> 'AXI4ProtocolSequence':
        """
        Create a sequence that tests Quality of Service (QoS) functionality.
        
        Returns:
            Self for method chaining
        """
        # Create a transaction sequence
        sequence = AXI4TransactionSequence(
            name="qos",
            id_width=self.id_width,
            addr_width=self.addr_width,
            data_width=self.data_width,
            user_width=self.user_width
        )
        
        # Base address for test
        base_addr = 0xB0000000
        
        # Test different QoS values
        for qos in [0, 1, 2, 4, 8, 15]:
            addr = base_addr + (qos * 0x1000)
            
            # Write with this QoS
            sequence.add_write_transaction(
                addr=addr,
                data_values=[0xC0000000 + qos],
                qos=qos
            )
            
            # Read with this QoS
            sequence.add_read_transaction(
                addr=addr,
                burst_len=0,  # Single beat
                qos=qos
            )
        
        # Test QoS prioritization:
        # - First, queue low-priority transactions
        # - Then, queue high-priority transactions that should be processed first
        
        # Low-priority writes (QoS=0)
        for i in range(10):
            addr = base_addr + 0x10000 + (i * 4)
            
            sequence.add_write_transaction(
                addr=addr,
                data_values=[0xC1000000 + i],
                qos=0
            )
        
        # High-priority writes (QoS=15)
        for i in range(5):
            addr = base_addr + 0x20000 + (i * 4)
            
            sequence.add_write_transaction(
                addr=addr,
                data_values=[0xC2000000 + i],
                qos=15
            )
        
        # Add the sequence to our performance sequences
        self.add_performance_sequence("qos", sequence)
        
        return self

    # ========================================================================
    # Complete Test Suite
    # ========================================================================
    
    @classmethod
    def create_protocol_test_suite(cls, 
                                 id_width: int = 8,
                                 addr_width: int = 32,
                                 data_width: int = 32,
                                 user_width: int = 1) -> 'AXI4ProtocolSequence':
        """
        Create a complete protocol test suite with all test sequences.
        
        Args:
            id_width: Width of ID field in bits
            addr_width: Width of address field in bits
            data_width: Width of data field in bits
            user_width: Width of user field in bits
            
        Returns:
            Configured AXI4ProtocolSequence with all test cases
        """
        # Create a protocol sequence
        protocol_sequence = cls(
            name="protocol_test_suite",
            id_width=id_width,
            addr_width=addr_width,
            data_width=data_width,
            user_width=user_width
        )
        
        # Create error sequences
        protocol_sequence.create_slverr_response_sequence()
        protocol_sequence.create_decerr_response_sequence()
        protocol_sequence.create_exokay_response_sequence()
        
        # Create boundary sequences
        protocol_sequence.create_4k_boundary_sequence()
        protocol_sequence.create_unaligned_address_sequence()
        protocol_sequence.create_max_burst_sequence()
        
        # Create compliance sequences
        protocol_sequence.create_burst_type_sequence()
        protocol_sequence.create_protection_sequence()
        protocol_sequence.create_exclusive_sequence()
        
        # Create performance sequences
        protocol_sequence.create_throughput_sequence()
        protocol_sequence.create_interleaved_sequence()
        protocol_sequence.create_quality_of_service_sequence()
        
        return protocol_sequence

    @classmethod
    def create_basic_protocol_test(cls,
                                  id_width: int = 8,
                                  addr_width: int = 32,
                                  data_width: int = 32,
                                  user_width: int = 1) -> 'AXI4ProtocolSequence':
        """
        Create a minimal protocol test with key test sequences.
        
        Args:
            id_width: Width of ID field in bits
            addr_width: Width of address field in bits
            data_width: Width of data field in bits
            user_width: Width of user field in bits
            
        Returns:
            Configured AXI4ProtocolSequence with basic test cases
        """
        # Create a protocol sequence
        protocol_sequence = cls(
            name="basic_protocol_test",
            id_width=id_width,
            addr_width=addr_width,
            data_width=data_width,
            user_width=user_width
        )
        
        # Create one sequence from each category
        protocol_sequence.create_slverr_response_sequence()
        protocol_sequence.create_4k_boundary_sequence()
        protocol_sequence.create_burst_type_sequence()
        protocol_sequence.create_interleaved_sequence()
        
        return protocol_sequence
"""
AXI4 Protocol Sequence

This module provides specialized sequences for AXI4 protocol verification, focusing
on protocol edge cases, error conditions, and compliance testing.
"""

import random
from typing import List, Dict, Any, Optional, Tuple, Union, Set
from collections import deque, defaultdict

from CocoTBFramework.components.field_config import FieldConfig
from CocoTBFramework.components.flex_randomizer import FlexRandomizer
from CocoTBFramework.components.axi4.axi4_packet import AXI4Packet
from CocoTBFramework.components.axi4.axi4_transaction_sequence import AXI4TransactionSequence


class AXI4ProtocolSequence:
    """
    AXI4 Protocol Sequence for compliance testing and edge cases.
    
    This class provides specialized test sequences that focus on AXI4 protocol
    compliance, boundary conditions, and error handling, building on the transaction
    sequence foundation.
    """

    # AXI4 response codes
    RESP_OKAY = 0
    RESP_EXOKAY = 1
    RESP_SLVERR = 2
    RESP_DECERR = 3

    def __init__(self, name: str = "axi4_protocol",
                 id_width: int = 8,
                 addr_width: int = 32,
                 data_width: int = 32,
                 user_width: int = 1):
        """
        Initialize the AXI4 Protocol Sequence.

        Args:
            name: Sequence name
            id_width: Width of ID field in bits
            addr_width: Width of address field in bits
            data_width: Width of data field in bits
            user_width: Width of user field in bits
        """
        self.name = name
        self.id_width = id_width
        self.addr_width = addr_width
        self.data_width = data_width
        self.user_width = user_width
        
        # Create transaction sequence for generating transactions
        self.transaction_sequence = AXI4TransactionSequence(
            name=name,
            id_width=id_width,
            addr_width=addr_width,
            data_width=data_width,
            user_width=user_width
        )
        
        # Specialized sequences for protocol testing
        self.error_sequences = {}  # Maps sequence name to transactions
        self.boundary_sequences = {}  # Maps sequence name to transactions
        self.compliance_sequences = {}  # Maps sequence name to transactions
        self.performance_sequences = {}  # Maps sequence name to transactions
        
        # Protocol validation tracking
        self.protocol_violations = defaultdict(list)  # Maps transaction ID to violations
        
        # Statistics
        self.stats = {
            'total_sequences': 0,
            'error_sequences': 0,
            'boundary_sequences': 0,
            'compliance_sequences': 0,
            'performance_sequences': 0,
            'protocol_violations': 0
        }

    def add_error_sequence(self, name: str, sequence: AXI4TransactionSequence) -> 'AXI4ProtocolSequence':
        """
        Add a sequence that tests error handling.
        
        Args:
            name: Name for this error sequence
            sequence: Transaction sequence to add
            
        Returns:
            Self for method chaining
        """
        self.error_sequences[name] = sequence
        self.stats['error_sequences'] += 1
        self.stats['total_sequences'] += 1
        return self

    def add_boundary_sequence(self, name: str, sequence: AXI4TransactionSequence) -> 'AXI4ProtocolSequence':
        """
        Add a sequence that tests boundary conditions.
        
        Args:
            name: Name for this boundary sequence
            sequence: Transaction sequence to add
            
        Returns:
            Self for method chaining
        """
        self.boundary_sequences[name] = sequence
        self.stats['boundary_sequences'] += 1
        self.stats['total_sequences'] += 1
        return self

    def add_compliance_sequence(self, name: str, sequence: AXI4TransactionSequence) -> 'AXI4ProtocolSequence':
        """
        Add a sequence that tests protocol compliance.
        
        Args:
            name: Name for this compliance sequence
            sequence: Transaction sequence to add
            
        Returns:
            Self for method chaining
        """
        self.compliance_sequences[name] = sequence
        self.stats['compliance_sequences'] += 1
        self.stats['total_sequences'] += 1
        return self

    def add_performance_sequence(self, name: str, sequence: AXI4TransactionSequence) -> 'AXI4ProtocolSequence':
        """
        Add a sequence that tests performance aspects.
        
        Args:
            name: Name for this performance sequence
            sequence: Transaction sequence to add
            
        Returns:
            Self for method chaining
        """
        self.