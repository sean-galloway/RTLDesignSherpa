

// Generic rotating-priority arbiter with masking/rotation (no if/case ladders in priority path)
// - Parameterizable number of agents N (N >= 1)
// - Remembers last granted index in a flop (r_last_grant)
// - Uses rotation and lowest-set-bit isolate: x & (~x + 1)
// - Prefixes: w_* = wires, r_* = flops
module arbiter_round_robin_simple #(
    parameter int unsigned N = 4
) (
    input  logic                  clk,
    input  logic                  rst_n,         // active-low reset
    input  logic [N-1:0]          request,       // request bits [N-1:0]
    output logic                  grant_valid,   // any grant
    output logic [N-1:0]          grant,         // one-hot grant
    output logic [$clog2(N)-1:0]  grant_id       // encoded grant (undef if grant_valid==0)
);
    // ------------------------------
    // State: last granted index
    // ------------------------------
    logic [$clog2(N)-1:0] r_last_grant;

    // ------------------------------
    // Combinational priority logic
    // ------------------------------
    logic [$clog2(N)-1:0] w_grant_id;
    logic [N-1:0]         w_rot_req;
    logic [N-1:0]         w_rot_sel;
    logic [N-1:0]         w_nxt_grant;
    logic                 w_grant_valid;

    // Shift amount = last_grant + 1 (mod N), renamed per your request.
    logic [$clog2(N)-1:0] w_shift_amount;       // 0..N-1
    assign w_shift_amount = (r_last_grant == ($clog2(N))'(N-1)) ? '0 : (r_last_grant + 1);

    // Rotate-left request by w_shift_amount, with a guard for 0 to avoid shifting by N
    always_comb begin
        if (w_shift_amount == '0) begin
            w_rot_req = request;
        end else begin
            w_rot_req = (request << w_shift_amount) | (request >> (($clog2(N))'(N) - w_shift_amount));
        end
        // Isolate lowest set bit (one-hot). Works for zero too (yields zero).
        w_rot_sel = w_rot_req & ((~w_rot_req) + {{(N-1){1'b0}}, 1'b1});

        // Rotate-right by the same amount to restore original bit positions
        if (w_shift_amount == '0) begin
            w_nxt_grant = w_rot_sel;
        end else begin
            w_nxt_grant = (w_rot_sel >> w_shift_amount) | (w_rot_sel << (($clog2(N))'(N) - w_shift_amount));
        end
    end

    assign grant = w_nxt_grant;
    assign w_grant_valid = |w_nxt_grant;
    assign grant_valid = w_grant_valid;

    // One-hot to index encoder (compact & synth-friendly)
    always_comb begin
        w_grant_id = r_last_grant; // don't-care if no grant; default to last
        for (int i = 0; i < N; i++) begin
            if (w_nxt_grant[i]) w_grant_id = i[$clog2(N)-1:0];
        end
    end
    assign grant_id = w_grant_id;

    // ------------------------------
    // State update
    // ------------------------------
    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            r_last_grant <= ($clog2(N))'(N-1); // first pass starts at agent 0
        end else if (w_grant_valid) begin
            r_last_grant <= w_grant_id;
        end
    end

endmodule : arbiter_round_robin_simple
