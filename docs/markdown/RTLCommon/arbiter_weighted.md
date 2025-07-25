# Weighted Round Robin Arbiter

## Purpose
The `arbiter_round_robin_weighted` module implements a weighted round-robin arbitration scheme where different clients can be assigned different priorities through configurable weight thresholds. Clients with higher weights get more frequent access to the shared resource.

## Parameters
- `MAX_THRESH`: Maximum threshold value for weights (default: 16)
- `MAX_THRESH_WIDTH`: Width of threshold values (`$clog2(MAX_THRESH)`)
- `CLIENTS`: Number of clients (default: 4)
- `WAIT_GNT_ACK`: Grant acknowledgment mode (default: 0)
- `C`, `N`, `MTW`, `CXMTW`: Convenience parameters for width calculations

## Ports

### Inputs
- `clk`: System clock
- `rst_n`: Active-low asynchronous reset
- `block_arb`: Arbitration blocking signal
- `max_thresh[CXMTW-1:0]`: Flattened array of weight thresholds for each client
- `req[C-1:0]`: Request signals from clients
- `gnt_ack[C-1:0]`: Grant acknowledgment signals

### Outputs
- `gnt_valid`: Valid grant indicator
- `gnt[C-1:0]`: One-hot grant vector
- `gnt_id[N-1:0]`: Binary-encoded grant ID

## Key Internal Signals
- `r_crd_cnt[CXMTW-1:0]`: Credit counters for each client (flattened array)
- `w_has_crd[C-1:0]`: Indicates which clients have available credits
- `w_mask_req[C-1:0]`: Masked request signals based on credit availability
- `w_replenish`: Signal to replenish all credits when needed

## Implementation Details

### Credit-Based Weighting System
Each client has an associated credit counter that tracks how many times it has been granted access relative to its configured weight:

```systemverilog
assign w_has_crd[i] = (w_crd_cnt_incr[EndIdx-:MTW] <= max_thresh[EndIdx-:MTW]) &&
                      (max_thresh[EndIdx-:MTW] > 0);
```

### Credit Replenishment Logic
When no requesting clients have available credits, the system replenishes all credits:

```systemverilog
assign w_replenish = ((req & w_has_crd) == '0) && (req != '0);
```

### Per-Client Credit Management
Each client's credit counter is managed independently:

```systemverilog
always_comb begin
    w_crd_cnt_next[EndIdx-:MTW] = r_crd_cnt[EndIdx-:MTW];
    
    if (max_thresh[EndIdx-:MTW] > 0) begin
        if (w_replenish) begin
            if (gnt[i])
                w_crd_cnt_next[EndIdx-:MTW] = 1;
            else
                w_crd_cnt_next[EndIdx-:MTW] = 0;
        end else if (gnt[i] && w_has_crd[i]) begin
            w_crd_cnt_next[EndIdx-:MTW] = w_crd_cnt_incr[EndIdx-:MTW];
        end
    end else begin
        w_crd_cnt_next[EndIdx-:MTW] = 0;  // Zero-weight clients
    end
end
```

## Sub-Modules

### arbiter_round_robin_weighted_subinst
Handles the actual round-robin arbitration logic with masking:
- Maintains a round-robin mask to ensure fairness among clients with credits
- Uses fixed-priority arbiters for both masked and unmasked requests
- Selects between raw and masked grants based on replenish signal

### arbiter_round_robin_weighted_fixed_priority
Simple fixed-priority arbiter that grants to the lowest-indexed requesting client:

```systemverilog
always_comb begin
    grant = {CLIENTS{1'b0}};
    w_found = 1'b0;
    for (int i = 0; i < CLIENTS; i++) begin
        if (req[i] && !w_found) begin
            grant[i] = 1'b1;
            w_found = 1'b1;
        end
    end
end
```

## Special Features

### Zero-Weight Client Handling
Clients with `max_thresh = 0` are effectively disabled:
- Never accumulate credits
- Never participate in arbitration
- Credit counters remain at zero

### Dynamic Weight Configuration
Weight thresholds can be changed during operation, immediately affecting arbitration behavior.

### Credit Counter Synchronization
Credit updates are synchronized with grant acknowledgments when `WAIT_GNT_ACK = 1`:

```systemverilog
if ((WAIT_GNT_ACK == 0) || gnt_ack[i]) begin
    r_crd_cnt[EndIdx-:MTW] <= w_crd_cnt_next[EndIdx-:MTW];
end
```

## Operation Example
1. **Client weights**: A=3, B=1, C=2, D=0
2. **Sequence**: A, A, A, C, B, C, (replenish), A, A, A, C, B, C, ...
3. **Client D**: Never gets grants due to zero weight

## Usage Notes
- Higher `max_thresh` values provide more frequent access
- Zero weights completely disable clients
- The system automatically handles credit replenishment
- Fairness is maintained through the underlying round-robin mechanism
- Grant acknowledgment support ensures proper credit accounting in slow systems