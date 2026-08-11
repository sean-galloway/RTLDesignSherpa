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

**[← Back to Main Index](../index.md)** | **[rtl-common Index](index.md)**

# Round Robin Arbiter

Fair round-robin arbitration for multiple clients — every requesting client gets equal access to the shared resource, and no client starves.

## Overview

The `arbiter_round_robin` module cycles through requesting clients in order, so access to the shared resource stays fair over time. It is built around a pre-computed mask lookup table (no logic cost at runtime) and delegates winner selection to the `arbiter_priority_encoder` submodule.

## Parameters

| Parameter | Type | Default | Description |
|-----------|------|---------|-------------|
| CLIENTS | int | 4 | Number of clients |
| WAIT_GNT_ACK | int | 0 | When set to 1, waits for grant acknowledgment before moving to next client |
| N | int | $clog2(CLIENTS) | Internal parameter for address width calculation |

## Ports

### Inputs

| Port | Width | Description |
|------|-------|-------------|
| clk | 1 | System clock |
| rst_n | 1 | Active-low asynchronous reset |
| block_arb | 1 | When asserted, blocks all arbitration (forces no grants) |
| request | CLIENTS | Request signals from each client |
| grant_ack | CLIENTS | Grant acknowledgment signals (used when `WAIT_GNT_ACK = 1`) |

### Outputs

| Port | Width | Description |
|------|-------|-------------|
| grant_valid | 1 | Indicates when a valid grant is being issued |
| grant | CLIENTS | One-hot encoded grant signals |
| grant_id | N | Binary encoded ID of the granted client |
| last_grant | CLIENTS | Previous cycle's grant (for debugging/history) |

## Functional Description

### Fair Round-Robin Operation

The rotation order is `0 → 1 → 2 → ... → (CLIENTS-1) → 0` (see the RTL header).
The algorithm ensures fairness by:
1. After serving client `i`, giving priority to the **higher-indexed** clients
   (`i+1 .. CLIENTS-1`) via `w_win_mask_decode[i]`
2. Checking those masked (higher-index) requests first
3. When no higher-indexed clients are requesting, wrapping around to the
   **lowest** indices (client 0 upward)

### Block Arbitration

Assert `block_arb` and all requests are masked to zero — arbitration is effectively disabled.

**A blocked interval RESETS the rotation.** This is the part that surprises
people. `r_last_valid` follows `grant_valid` every cycle, and a block produces
no grants, so `r_last_valid` falls to 0 and the mask select drops to its third
branch:

```systemverilog
assign w_curr_mask_decode = grant_valid  ? w_win_mask_decode[grant_id]        :
                            r_last_valid ? w_win_mask_decode[r_last_grant_id] :
                                           CLIENTS'(1);
```

`CLIENTS'(1)` masks off everything except client 0, so **the first grant after
`block_arb` releases goes to the lowest-numbered requester, not to the client
that was next in line.** Traced on a 32-client instance: block released at
25060 ns, and the next two grants went to clients 0 and 3 while the pre-block
rotation had reached the high teens.

If you need fairness to survive a blocked interval, `block_arb` is the wrong
tool — gate the requests upstream instead, so the arbiter keeps seeing a valid
grant history.

### Grant Acknowledgment Support

When `WAIT_GNT_ACK = 1`, the arbiter waits for the granted client to acknowledge receipt before updating internal state and moving to the next client.

### Key Internal Signals

- `r_last_grant_id`: Tracks the last winner's client ID (smaller than full mask)
- `r_last_valid`: Indicates if last winner should be used for mask generation
- `r_pending_ack`: ACK mode state (indicates ACK pending)
- `r_pending_client`: Which client has pending ACK (only in ACK mode)
- `w_requests_masked`: Requests with priority mask applied
- `w_requests_unmasked`: Raw gated requests without masking

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

### Winner Selection

Winner selection is delegated to the `arbiter_priority_encoder` submodule:
- Takes both masked and unmasked request vectors
- Returns binary-encoded winner ID
- Outputs validity signal

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

## Design Notes

### Usage Notes

- On the first grant after reset (no last winner), the mask defaults to client 0,
  so the lowest-indexed requester wins ties initially; thereafter priority
  rotates upward from the last winner
- The round-robin nature ensures long-term fairness across all clients
- Grant acknowledgment feature is useful in systems where the granted client needs time to process the grant

## Navigation

- **[← Back to rtl-common Index](index.md)**
- **[← Back to Main Documentation Index](../index.md)**
