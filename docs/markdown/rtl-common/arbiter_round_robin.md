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
The `arbiter_round_robin` module implements fair round-robin arbitration for multiple clients. Every requesting client gets equal access to the shared resource — the arbiter cycles through them in order, so no client starves.

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
The arbiter is built around a pre-computed mask lookup table:

1. **Mask Lookup Tables**: Pre-computed at elaboration time (no logic cost)
   - `w_win_mask_decode[i] = ~((1 << (i+1)) - 1)`: selects clients **i+1 and
     above** (all higher indices). After client `i` wins, this is the mask that
     gives priority to the next-higher clients. This is the only LUT the
     arbiter actually reads (via `w_curr_mask_decode`).
   - `w_mask_decode[i] = (1 << i) - 1`: covers clients **0 through i-1**. Note:
     this table is generated but **never read** in the current RTL — it is dead
     logic left from an earlier scheme, not part of the active datapath.

2. **Fast Request Preprocessing**: Single LUT level for request gating
   - Block arbitration immediately gates all requests
   - Masked and unmasked request vectors computed in parallel

3. **Last Winner Tracking**: Uses client ID instead of full one-hot mask
   - `r_last_grant_id`: More efficient than storing full grant vector
   - `r_last_valid`: Indicates if mask should be applied

### Priority Encoder
Winner selection is delegated to the `arbiter_priority_encoder` submodule:
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
Assert `block_arb` and all requests are masked to zero — arbitration is effectively disabled.

### Grant Acknowledgment Support
When `WAIT_GNT_ACK = 1`, the arbiter waits for the granted client to acknowledge receipt before updating internal state and moving to the next client.

### Fair Round-Robin Operation
The rotation order is `0 → 1 → 2 → ... → (CLIENTS-1) → 0` (see the RTL header).
The algorithm ensures fairness by:
1. After serving client `i`, giving priority to the **higher-indexed** clients
   (`i+1 .. CLIENTS-1`) via `w_win_mask_decode[i]`
2. Checking those masked (higher-index) requests first
3. When no higher-indexed clients are requesting, wrapping around to the
   **lowest** indices (client 0 upward)

## Usage Notes
- On the first grant after reset (no last winner), the mask defaults to client 0,
  so the lowest-indexed requester wins ties initially; thereafter priority
  rotates upward from the last winner
- The round-robin nature ensures long-term fairness across all clients
- Grant acknowledgment feature is useful in systems where the granted client needs time to process the grant

## Navigation

- **[← Back to rtl-common Index](index.md)**
- **[← Back to Main Documentation Index](../index.md)**
