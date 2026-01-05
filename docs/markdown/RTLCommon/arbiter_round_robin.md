<!-- RTL Design Sherpa Documentation Header -->
<table>
<tr>
<td width="80">
  <a href="https://github.com/sean-galloway/RTLDesignSherpa">
    <img src="https://raw.githubusercontent.com/sean-galloway/RTLDesignSherpa/main/docs/logos/Logo_200px.png" alt="RTL Design Sherpa" width="70">
  </a>
</td>
<td>
  <strong>RTL Design Sherpa</strong> · <em>Learning Hardware Design Through Practice</em><br>
  <sub>
    <a href="https://github.com/sean-galloway/RTLDesignSherpa">GitHub</a> ·
    <a href="https://github.com/sean-galloway/RTLDesignSherpa/blob/main/docs/DOCUMENTATION_INDEX.md">Documentation Index</a> ·
    <a href="https://github.com/sean-galloway/RTLDesignSherpa/blob/main/LICENSE">MIT License</a>
  </sub>
</td>
</tr>
</table>

---

<!-- End Header -->

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
- `request[CLIENTS-1:0]`: Request signals from each client
- `grant_ack[CLIENTS-1:0]`: Grant acknowledgment signals (used when `WAIT_GNT_ACK = 1`)

### Outputs
- `grant_valid`: Indicates when a valid grant is being issued
- `grant[CLIENTS-1:0]`: One-hot encoded grant signals
- `grant_id[N-1:0]`: Binary encoded ID of the granted client
- `last_grant[CLIENTS-1:0]`: Previous cycle's grant (for debugging/history)

## Key Internal Signals
- `r_last_grant_id`: Tracks the last winner's client ID (smaller than full mask)
- `r_last_valid`: Indicates if last winner should be used for mask generation
- `r_pending_ack`: ACK mode state (indicates ACK pending)
- `r_pending_client`: Which client has pending ACK (only in ACK mode)
- `w_requests_masked`: Requests with priority mask applied
- `w_requests_unmasked`: Raw gated requests without masking

## Implementation Details

### Priority Mechanism
The arbiter uses a pre-computed mask lookup table approach:

1. **Mask Lookup Tables**: Pre-computed at elaboration time (no logic cost)
   - `w_mask_decode[i]`: Mask for clients 0 through i (give priority after i)
   - `w_win_mask_decode[i]`: Mask to give priority to clients above i+1

2. **Fast Request Preprocessing**: Single LUT level for request gating
   - Block arbitration immediately gates all requests
   - Masked and unmasked request vectors computed in parallel

3. **Last Winner Tracking**: Uses client ID instead of full one-hot mask
   - `r_last_grant_id`: More efficient than storing full grant vector
   - `r_last_valid`: Indicates if mask should be applied

### Priority Encoder
Uses `arbiter_priority_encoder` submodule for winner selection:
- Takes both masked and unmasked request vectors
- Returns binary-encoded winner ID
- Outputs validity signal

### Winner Selection Logic
```systemverilog
// Priority encoder selects highest priority requester
arbiter_priority_encoder #(.CLIENTS(CLIENTS), .N(N)) u_priority_encoder (
    .requests_masked    (w_requests_masked),
    .requests_unmasked  (w_requests_unmasked),
    .any_masked_requests(w_any_masked_requests),
    .winner             (w_winner),
    .winner_valid       (w_winner_valid)
);

// Grant decision with ACK permission check
assign w_should_grant = w_winner_valid && w_any_requests && w_can_grant;
```

### Mask Update Logic
- **No-ACK Mode**: Mask updates immediately when grant issued (1-cycle round-robin)
- **ACK Mode**: Mask updates only when ACK received (prevents premature rotation)

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

## Navigation

- **[← Back to RTLCommon Index](index.md)**
- **[← Back to Main Documentation Index](../../index.md)**
