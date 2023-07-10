`timescale 1ns / 1ps

module pwm #(
    parameter MAX = 16
    )(
    input                         clk, rst_n,
    input [$clog2(MAX)-1:0]       high_count, low_count,
    input [$clog2(MAX)-1:0]       repeat_count,
    input                         start,
    output reg                    done, pwm_sig,
    output reg [$clog2(MAX)-1:0]  count
);

    // Enum the States
    parameter   IDLE           = 5'b00001,
                COUNT_UP_PRE   = 5'b00010,
                COUNT_UP       = 5'b00100,
                COUNT_DOWN_PRE = 5'b01000,
                COUNT_DOWN     = 5'b10000;

    logic [4:0]             current_state, next_state;
    logic [$clog2(MAX)-1:0] repeated_d, repeated_q;
    logic [$clog2(MAX)-1:0] loadval_lcc;
    logic                   load_lcc, increment_lcc, done_d, pwm_sig_d;
    logic                   done_lcc_d, done_lcc_q, done_lcc_re;

    assign done_lcc_re = !done_lcc_q && done_lcc_d;

    // Mealy FSM Design Since it is so simple
    always @(*) begin
        load_lcc = 0;
        loadval_lcc = 0;
        increment_lcc = 0;
        repeated_d = repeated_q;
        done_d = 'b0;
        pwm_sig_d = 0;

        case (current_state)
            IDLE:
                if (start) begin
                    next_state = COUNT_UP_PRE;
                    load_lcc = 1;
                    loadval_lcc = high_count;
                end

            COUNT_UP_PRE:
                begin
                    next_state = COUNT_UP;
                    load_lcc = 0;
                    loadval_lcc = high_count;
                    pwm_sig_d = 0;
                end

            COUNT_UP:
                begin
                    if (done_lcc_re) begin
                        next_state = COUNT_DOWN_PRE;
                        load_lcc = 0;
                        loadval_lcc = low_count;
                        increment_lcc = 1;
                        pwm_sig_d = 0;
                    end
                    else begin
                        next_state = COUNT_UP;
                        increment_lcc = 1;
                        pwm_sig_d = 1;
                    end
                end


            COUNT_DOWN_PRE:
                begin
                    next_state = COUNT_DOWN;
                    load_lcc = 1;
                    loadval_lcc = low_count;
                    pwm_sig_d = 0;
                end

            COUNT_DOWN:
            begin
                if (done_lcc_re) begin
                    if (repeated_q == repeat_count) begin
                        next_state = IDLE;
                        load_lcc = 0;
                        loadval_lcc = low_count;
                        increment_lcc = 0;
                        done_d = 'b1;
                    end
                    else begin
                        next_state = COUNT_UP_PRE;
                        load_lcc = 1;
                        loadval_lcc = high_count;
                        increment_lcc = 1;
                        repeated_d = repeated_d + 1;
                    end
                end
                else begin
                    next_state = COUNT_DOWN;
                    increment_lcc = 1;
                end
            end


            default: begin
                next_state = IDLE;
                load_lcc = 0;
                loadval_lcc = low_count;
            end
        endcase
    end

    // flops for state, repeat, and done
    always @(posedge clk, negedge rst_n) begin
        if (!rst_n) begin
            current_state <= IDLE;
            repeated_q <= 0;
            done <= 'b0;
            pwm_sig <= 'b0;
            done_lcc_q <= 'b0;
        end
        else begin
            current_state <= next_state;
            repeated_q <= repeated_d;
            done <= done_d;
            pwm_sig <= pwm_sig_d;
            done_lcc_q <= done_lcc_d;
        end
    end

    // Load/Clear Counter Instance
    load_clear_counter
    #(
        .MAX  (MAX)
    )
    u_load_clear_counter(
        .clk       (clk),
        .rst_n     (rst_n),
        .clear     (1'b0),
        .increment (increment_lcc),
        .load      (load_lcc),
        .loadval   (loadval_lcc),
        .count     (count),
        .done      (done_lcc_d)
    );

	// synopsys translate_off
	initial begin
		$dumpfile("dump.vcd");
		$dumpvars(0, pwm);
	end
	// synopsys translate_on
endmodule
