module ioapic_lowest_pri_arb (
	deliv_valid,
	deliv_vector,
	deliv_dest,
	deliv_dest_mode,
	deliv_deliv_mode,
	deliv_ready,
	deliv_retry,
	cpu_apic_id,
	cpu_logical_dest,
	cpu_priority,
	cpu_can_accept,
	cpu_irq_valid,
	cpu_irq_vector,
	cpu_irq_deliv_mode
);
	reg _sv2v_0;
	parameter signed [31:0] NUM_CPUS = 4;
	input wire deliv_valid;
	input wire [7:0] deliv_vector;
	input wire [7:0] deliv_dest;
	input wire deliv_dest_mode;
	input wire [2:0] deliv_deliv_mode;
	output wire deliv_ready;
	output wire deliv_retry;
	input wire [(NUM_CPUS * 8) - 1:0] cpu_apic_id;
	input wire [(NUM_CPUS * 8) - 1:0] cpu_logical_dest;
	input wire [(NUM_CPUS * 8) - 1:0] cpu_priority;
	input wire [NUM_CPUS - 1:0] cpu_can_accept;
	output wire [NUM_CPUS - 1:0] cpu_irq_valid;
	output wire [7:0] cpu_irq_vector;
	output wire [2:0] cpu_irq_deliv_mode;
	localparam [2:0] DELIV_LOWEST_PRI = 3'b001;
	localparam signed [31:0] IDX_W = (NUM_CPUS > 1 ? $clog2(NUM_CPUS) : 1);
	reg [NUM_CPUS - 1:0] w_in_set;
	wire [NUM_CPUS - 1:0] w_eligible;
	reg [NUM_CPUS - 1:0] w_grant;
	reg w_have_lowest;
	reg [7:0] w_best_pri;
	reg [IDX_W - 1:0] w_best_idx;
	always @(*) begin
		if (_sv2v_0)
			;
		begin : sv2v_autoblock_1
			reg signed [31:0] i;
			for (i = 0; i < NUM_CPUS; i = i + 1)
				w_in_set[i] = (deliv_dest_mode ? (cpu_logical_dest[((NUM_CPUS - 1) - i) * 8+:8] & deliv_dest) != 8'h00 : cpu_apic_id[((NUM_CPUS - 1) - i) * 8+:8] == deliv_dest);
		end
	end
	assign w_eligible = w_in_set & cpu_can_accept;
	function automatic signed [IDX_W - 1:0] sv2v_cast_ADDFD_signed;
		input reg signed [IDX_W - 1:0] inp;
		sv2v_cast_ADDFD_signed = inp;
	endfunction
	always @(*) begin
		if (_sv2v_0)
			;
		w_have_lowest = 1'b0;
		w_best_pri = 8'hff;
		w_best_idx = 0;
		begin : sv2v_autoblock_2
			reg signed [31:0] i;
			for (i = 0; i < NUM_CPUS; i = i + 1)
				if (w_eligible[i] && (!w_have_lowest || (cpu_priority[((NUM_CPUS - 1) - i) * 8+:8] < w_best_pri))) begin
					w_have_lowest = 1'b1;
					w_best_pri = cpu_priority[((NUM_CPUS - 1) - i) * 8+:8];
					w_best_idx = sv2v_cast_ADDFD_signed(i);
				end
		end
	end
	always @(*) begin
		if (_sv2v_0)
			;
		w_grant = 1'sb0;
		if (deliv_deliv_mode == DELIV_LOWEST_PRI) begin
			if (w_have_lowest)
				w_grant[w_best_idx] = 1'b1;
		end
		else
			w_grant = w_eligible;
	end
	assign deliv_ready = deliv_valid;
	assign deliv_retry = deliv_valid && (w_grant == {NUM_CPUS {1'sb0}});
	assign cpu_irq_valid = (deliv_valid ? w_grant : {NUM_CPUS {1'sb0}});
	assign cpu_irq_vector = deliv_vector;
	assign cpu_irq_deliv_mode = deliv_deliv_mode;
	initial begin : param_check
		if ((NUM_CPUS < 1) || (NUM_CPUS > 255))
			$display("Error [%0t] /mnt/data/github/RTLDesignSherpa/projects/components/retro_legacy_blocks/rtl/ioapic/ioapic_lowest_pri_arb.sv:161:13 - ioapic_lowest_pri_arb.param_check.<unnamed_block>\n msg: ", $time, "ioapic_lowest_pri_arb: NUM_CPUS=%0d out of range [1,255]", NUM_CPUS);
	end
	initial _sv2v_0 = 0;
endmodule
