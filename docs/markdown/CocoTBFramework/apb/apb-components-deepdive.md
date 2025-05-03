# APB Components Deep Dive

This document examines the internals of the core APB components: `APBMonitor`, `APBSlave`, and `APBMaster` from `apb_components.py`.

## Component Base Architecture

All APB components are built upon CocoTB's bus component classes:
- `APBMonitor` extends `BusMonitor`
- `APBSlave` extends `BusMonitor`
- `APBMaster` extends `BusDriver`

These base classes provide foundational functionality like signal handling, callbacks, and event management.

## Signal Handling

Each component manages a set of signals that correspond to the APB protocol:

```python
apb_signals = [
    "PSEL",
    "PWRITE",
    "PENABLE",
    "PADDR",
    "PWDATA",
    "PRDATA",
    "PREADY"
]
apb_optional_signals = [
    "PPROT",
    "PSLVERR",
    "PSTRB"
]
```

Components handle both required and optional signals to support different APB implementations. The `is_signal_present` method provides a safe way to check for optional signals:

```python
def is_signal_present(self, signal_name):
    # Check if the bus has the attribute and that it is not None
    return hasattr(self.bus, signal_name) and getattr(self.bus, signal_name) is not None
```

## APBMonitor Class

The `APBMonitor` passively observes APB bus activity and captures transactions.

### Key Fields

```python
def __init__(self, entity, title, prefix, clock, signals=None,
             bus_width=32, addr_width=12, log=None, **kwargs):
    # Initialize signals
    if signals:
        self._signals = signals
    else:
        self._signals = apb_signals + apb_optional_signals
        self._optional_signals = apb_optional_signals

    self.count = 0
    self.bus_width = bus_width
    BusMonitor.__init__(self, entity, prefix, clock, **kwargs)
    self.clock = clock
    self.title = title
    self.log = log or self.entity._log
    self.bus_width = bus_width
    self.addr_width = addr_width
    self.strb_width = bus_width // 8
```

### Transaction Monitoring

The core monitoring logic happens in the `_monitor_recv` method:

```python
async def _monitor_recv(self):
    while True:
        await FallingEdge(self.clock)
        await Timer(200, units='ps')
        if (self.bus.PSEL.value.is_resolvable and 
            self.bus.PSEL.value.integer and 
            self.bus.PENABLE.value.integer and 
            self.bus.PREADY.value.is_resolvable and 
            self.bus.PREADY.value.integer):
            start_time = get_sim_time('ns')
            address    = self.bus.PADDR.value.integer
            direction  = pwrite[self.bus.PWRITE.value.integer]
            loc_pwrite = self.bus.PWRITE.value.integer
            error      = self.bus.PSLVERR.value.integer if self.is_signal_present('PSLVERR') else 0

            # Capture data based on direction
            if direction == 'READ':
                if self.bus.PRDATA.value.is_resolvable:
                    data = self.bus.PRDATA.value.integer
                else:
                    data = self.bus.PRDATA.value
            else:
                data = self.bus.PWDATA.value.integer
            strb = self.bus.PSTRB.value.integer if self.is_signal_present('PSTRB') else 0
            pprot = self.bus.PPROT.value.integer if self.is_signal_present('PPROT') else 0
            
            # Create transaction
            transaction = APBPacket(
                start_time=start_time,
                count=self.count,
                pwrite=loc_pwrite,
                paddr=address,
                pwdata=data if direction == 'WRITE' else 0,
                prdata=data if direction == 'READ' else 0,
                pstrb=strb,
                pprot=pprot,
                pslverr=error
            )
            
            # Notify callbacks
            self._recv(transaction)
            self.print(transaction)
```

This method:
1. Waits for the falling edge of the clock
2. Checks if there's a valid APB transaction (PSEL, PENABLE, PREADY)
3. Captures the transaction details from bus signals
4. Creates an APBPacket with the captured data
5. Notifies callbacks with the transaction

## APBSlave Class

The `APBSlave` responds to APB transactions by modeling a memory-mapped peripheral.

### Key Fields

```python
def __init__(self, entity, title, prefix, clock, registers, signals=None,
              bus_width=32, addr_width=12, randomizer=None,
              log=None, error_overflow=False, **kwargs):
    # Initialize signals and randomizer
    # ...
    
    # Create the memory model
    self.mem = MemoryModel(num_lines=self.num_lines, bytes_per_line=self.strb_bits, 
                           log=self.log, preset_values=registers)
    self.sentQ = deque()

    # Initialize outputs
    self.bus.PRDATA.setimmediatevalue(0)
    self.bus.PREADY.setimmediatevalue(0)
    if self.is_signal_present('PSLVERR'):
        self.bus.PSLVERR.setimmediatevalue(0)
```

### Transaction Processing

The `_monitor_recv` method monitors for APB transactions:

```python
async def _monitor_recv(self):
    while True:
        await RisingEdge(self.clock)
        self.bus.PREADY.value = 0
        self.bus.PRDATA.value = 0
        if self.is_signal_present('PSLVERR'):
            self.bus.PSLVERR.value = 0

        await Timer(200, units='ps')
        if self.bus.PSEL.value.is_resolvable and self.bus.PSEL.value.integer:
            rand_dict = self.randomizer.next()
            ready_delay = rand_dict['ready']
            slv_error = rand_dict['error']
            for _ in range(ready_delay):
                await RisingEdge(self.clock)

            self.bus.PREADY.value = 1
            await Timer(200, units='ps')
            while not self.bus.PENABLE.value.integer:
                await RisingEdge(self.clock)
                await Timer(200, units='ps')
            self._finish_recv(slv_error)
```

The `_finish_recv` method handles the actual data transfer:

```python
def _finish_recv(self, slv_error):
    address    =  self.bus.PADDR.value.integer
    word_index =  (address & ~self.addr_mask)
    pprot      =  self.bus.PPROT.value.integer if self.is_signal_present('PPROT') else 0
    self.count += 1

    # Handle address overflow
    if word_index >= self.num_lines:
        if self.error_overflow:
            # Signal error for overflow
            self.bus.PSLVERR.value = 1
        else:
            # Expand memory to handle overflow
            expand = word_index - self.num_lines + 10
            self.mem.expand(expand)
            self.num_lines += expand

    # Set error if requested
    if slv_error and self.is_signal_present('PSLVERR'):
        self.bus.PSLVERR.value = 1

    if self.bus.PWRITE.value.integer:  # Write transaction
        strobes   = self.bus.PSTRB.value.integer if self.is_signal_present('PSTRB') else (1 << self.strb_bits) - 1
        pwdata    = self.bus.PWDATA.value.integer
        pwdata_ba = self.mem.integer_to_bytearray(pwdata, self.strb_bits)
        self.mem.write(address & 0xFFF, pwdata_ba, strobes)
    else:  # Read transaction
        prdata_ba = self.mem.read(address & 0xFFF, self.strb_bits)
        prdata = self.mem.bytearray_to_integer(prdata_ba)
        self.bus.PRDATA.value = prdata
```

This method:
1. Gets the transaction address and calculates the word index
2. Handles address overflow (either by error or expansion)
3. Sets the error flag if requested
4. For write transactions: converts data to byte array and writes to memory
5. For read transactions: reads from memory, converts to integer, and drives PRDATA

## APBMaster Class

The `APBMaster` initiates APB transactions by driving the bus signals.

### Key Fields

```python
def __init__(self, entity, title, prefix, clock, signals=None,
              bus_width=32, addr_width=12, randomizer=None,
              log=None, **kwargs):
    # Initialize signals and randomizer
    # ...
    
    self.title = title
    self.prefix = prefix
    self.log = log or self.entity._log
    self.clock          = clock
    self.addr_width     = addr_width
    self.bus_width      = bus_width
    self.strb_bits      = bus_width // 8
    self.addr_mask      = (2**self.strb_bits - 1)
    self.sentQ = deque()

    # Initialize outputs
    self.bus.PADDR.setimmediatevalue(0)
    self.bus.PWRITE.setimmediatevalue(0)
    self.bus.PSEL.setimmediatevalue(0)
    self.bus.PENABLE.setimmediatevalue(0)
    self.bus.PWDATA.setimmediatevalue(0)
    if self.is_signal_present('PSTRB'):
        self.bus.PSTRB.setimmediatevalue(0)
    self.transmit_queue = deque()
```

### Transaction Driving

The `_driver_send` method queues transactions and starts the transmit pipeline:

```python
async def _driver_send(self, transaction, sync=True, hold=False, **kwargs):
    '''
        Append a new transaction to be transmitted
    '''
    # add new transaction
    self.transmit_queue.append(transaction)
    msg = f'Adding to the transmit_queue: {transaction.formatted(compact=True)}'
    self.log.debug(msg)

    # launch new transmit pipeline coroutine if aren't holding for and the
    #   the coroutine isn't already running.
    #   If it is running it will just collect the transactions in the
    #   queue once it gets to them.
    if not hold and not self.transmit_coroutine:
        self.transmit_coroutine = cocotb.start_soon(self._transmit_pipeline())
```

The `_transmit_pipeline` method processes the queue and transmits transactions:

```python
async def _transmit_pipeline(self):
    """Internal function to transmit queued transactions."""
    # default values
    self.transfer_busy = True

    # while there's data in the queue keep transmitting
    while len(self.transmit_queue):
        # clear out the bus
        self.bus.PSEL.value     = 0
        self.bus.PENABLE.value  = 0
        self.bus.PWRITE.value   = 0
        self.bus.PADDR.value    = 0
        self.bus.PWDATA.value   = 0
        # Reset optional signals
        # ...

        rand_dict = self.randomizer.next()
        psel_delay = rand_dict['psel']
        penable_delay = rand_dict['penable']

        transaction = self.transmit_queue.popleft()
        transaction.start_time = cocotb.utils.get_sim_time('ns')

        # finish the packet transmit
        await self._finish_xmit(transaction, psel_delay, penable_delay)

    # clear out the bus
    self.transfer_busy = False
    # Reset signals
    # ...
```

The `_finish_xmit` method handles the APB protocol sequence:

```python
async def _finish_xmit(self, transaction, psel_delay, penable_delay):
    """Completes an APB transaction."""
    # Wait for psel_delay cycles
    for _ in range(psel_delay):
        await RisingEdge(self.clock)

    # Setup phase
    self.bus.PSEL.value   = 1
    self.bus.PWRITE.value = transaction.fields['pwrite']
    self.bus.PADDR.value  = transaction.fields['paddr']
    if self.is_signal_present('PPROT'):
        self.bus.PPROT.value = transaction.fields['pprot']
    if self.is_signal_present('PSTRB'):
        self.bus.PSTRB.value = transaction.fields['pstrb']
    # Set data for write
    if transaction.direction == 'WRITE':
        self.bus.PWDATA.value = transaction.fields['pwdata']

    await RisingEdge(self.clock)
    await Timer(200, units='ps')

    # Wait for penable_delay cycles
    for _ in range(penable_delay):
        await RisingEdge(self.clock)

    # Access phase
    self.bus.PENABLE.value = 1
    await FallingEdge(self.clock)

    # Wait for PREADY
    while not self.bus.PREADY.value:
        await FallingEdge(self.clock)

    # Check for slave error
    if self.is_signal_present('PSLVERR') and self.bus.PSLVERR.value:
        transaction.fields['pslverr'] = self.bus.PSLVERR.value.integer

    # Capture read data
    if transaction.direction == 'READ':
        if self.bus.PRDATA.value.is_resolvable:
            transaction.fields['prdata'] = self.bus.PRDATA.value.integer
        else:
            transaction.fields['prdata'] = self.bus.PRDATA.value

    # Add to completed transactions queue
    self.sentQ.append(transaction)
    await RisingEdge(self.clock)
```

This method implements the APB protocol sequence:
1. Setup phase: Assert PSEL and set address, data, and control signals
2. Access phase: Assert PENABLE and wait for PREADY
3. Capture response: Record any errors and read data
4. Queue the completed transaction

## Timing and Randomization

Both `APBMaster` and `APBSlave` use randomization to create realistic timing variations:

- `APBMaster` randomizes the delays between setup and access phases
- `APBSlave` randomizes the PREADY assertion delay and error generation

This example shows the `APBMaster` randomization:

```python
rand_dict = self.randomizer.next()
psel_delay = rand_dict['psel']
penable_delay = rand_dict['penable']
```

The default randomization distributions are:

```python
self.randomizer = FlexRandomizer({
    'psel':    ([[0, 0], [1, 5], [6, 10]], [5, 2, 1]),
    'penable': ([[0, 0], [1, 2]], [4, 1]),
})
```

This creates weighted probability distributions, adding realism to the simulation.

## Memory Model Integration

The `APBSlave` uses a `MemoryModel` to store and retrieve data:

```python
# For write transactions
pwdata_ba = self.mem.integer_to_bytearray(pwdata, self.strb_bits)
self.mem.write(address & 0xFFF, pwdata_ba, strobes)

# For read transactions
prdata_ba = self.mem.read(address & 0xFFF, self.strb_bits)
prdata = self.mem.bytearray_to_integer(prdata_ba)
```

The memory model:
1. Converts between integers and byte arrays
2. Handles byte-enable strobes for partial writes
3. Manages memory allocation and expansion
4. Provides register-like functionality

## Protocol Compliance Details

The components enforce APB protocol rules:

1. **Two-phase protocol**: Setup phase followed by access phase
2. **Signal sequencing**: PSEL before PENABLE
3. **Handshaking**: Wait for PREADY before completing transaction
4. **Error handling**: Capture PSLVERR when present
5. **Data direction**: Drive or capture data based on PWRITE

## Implementation Insights

1. **Non-blocking design**: Components use asynchronous methods with CocoTB triggers
2. **Graceful degradation**: Optional signals are checked before use
3. **Queuing mechanism**: Transactions are queued and processed in order
4. **Realistic timing**: Randomized delays simulate real system behavior
5. **Memory modeling**: Byte-addressable memory with strobes for partial access
6. **Error handling**: Memory overflow detection and optional error generation
7. **Debug support**: Comprehensive logging and transaction recording
