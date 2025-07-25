# Round Robin Arbiter

## Purpose
The `arbiter_round_robin` module implements a fair round-robin arbitration scheme for multiple clients. It ensures that all requesting clients receive equal access to a shared resource by cycling through them in order, preventing starvation of any client.

## Parameters
- `CLIENTS`: Number of clients (default: 4)
- `WAIT_GNT_ACK`: When set to 1, waits for grant acknowledgment before moving to next client (default: 0)
- `N`: Internal parameter for address width calculation (`$clog2(CLIENTS)`)

## Ports

### Inputs
- `clk`: System clock
- `rst_n`: Active-low asynchronous reset
- `block_arb`: When asserted, blocks all arbitration (forces no grants)
- `req[CLIENTS-1:0]`: Request signals from each client
- `gnt_ack[CLIENTS-1:0]`: Grant acknowledgment signals (used when `WAIT_GNT_ACK = 1`)

### Outputs
- `gnt_valid`: Indicates when a valid grant is being issued
- `gnt[CLIENTS-1:0]`: One-hot encoded grant signals
- `gnt_id[N-1:0]`: Binary encoded ID of the granted client

## Key Internal Signals
- `r_mask`: Priority mask that determines which clients have lower priority
- `r_win_mask_only`: Mask to prevent consecutive grants to the same client
- `w_req_masked`: Requests ANDed with the priority mask
- `w_req_win_mask`: Conditional masking based on number of active requests

## Implementation Details

### Priority Mechanism
The arbiter uses two complementary mechanisms:

1. **Priority Mask (`r_mask`)**: Creates a mask where bits below the last winner are set to 1, giving them higher priority
2. **Win Mask (`r_win_mask_only`)**: Prevents the same client from winning consecutive cycles

### Leading One Detection
The module uses `leading_one_trailing_one` submodules to find the highest priority requesting client in both masked and unmasked request vectors.

### Winner Selection Logic
```systemverilog
always_comb begin
    if (w_vld_ffs_reqm) begin
        w_winner  = w_reqm_location;    // Use masked result (lower priority clients)
        w_win_vld = 1'b1;
    end else if (w_vld_ffs_req) begin
        w_winner  = w_req_location;     // Use unmasked result (wrap around)
        w_win_vld = 1'b1;
    end else begin
        w_winner  = {{N{1'b0}}};        // No valid requests
        w_win_vld = 1'b0;
    end
end
```

### Mask Update Logic
- **Priority Mask**: Updates when a grant is issued, setting all bits below the winner to 1
- **Win Mask**: Clears only the bit corresponding to the current winner to prevent immediate re-grant

## Special Features

### Block Arbitration
When `block_arb` is asserted, all requests are masked to zero, effectively disabling arbitration.

### Grant Acknowledgment Support
When `WAIT_GNT_ACK = 1`, the arbiter waits for the granted client to acknowledge receipt before updating internal state and moving to the next client.

### Fair Round-Robin Operation
The algorithm ensures fairness by:
1. Serving lower-indexed clients first within each round
2. After serving a client, giving priority to all lower-indexed clients
3. When no lower-indexed clients are requesting, wrapping around to serve from the top

## Usage Notes
- The arbiter prioritizes lower-indexed clients when multiple requests arrive simultaneously
- The round-robin nature ensures long-term fairness across all clients
- Grant acknowledgment feature is useful in systems where the granted client needs time to process the grant