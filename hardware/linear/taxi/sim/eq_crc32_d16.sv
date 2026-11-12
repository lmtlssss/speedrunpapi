module eq; logic [15:0] d; logic [31:0] s, a, b, c; int bad=0;
taxi_lfsr #(.LFSR_W(32),.LFSR_POLY(32'h4c11db7),.LFSR_GALOIS(1),.LFSR_FEED_FORWARD(0),.REVERSE(1),.DATA_W(16),.DATA_IN_EN(1'b1),.DATA_OUT_EN(1'b0),.STATE_SHIFT_PRE(0),.STATE_SHIFT_POST(0)) u(.data_in(d),.state_in(s),.data_out(),.state_out(a));
crc32_d16 p(.data_in(d),.state_in(s),.state_out(b)); crc32_d16_lut6 q(.data_in(d),.state_in(s),.state_out(c));
initial begin for (int i=0;i<200000;i++) begin d = 16'({$urandom,$urandom,$urandom}) + 0*16*16; s=$urandom; if (i==0) begin d='0; s='0; end if (i==1) begin d='1; s='1; end #1 if (a!==b || a!==c) bad++; end
 $display("R %0d",bad); $finish; end endmodule
