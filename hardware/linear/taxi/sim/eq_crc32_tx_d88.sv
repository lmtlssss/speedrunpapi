module eq; logic [87:0] d; logic [31:0] s, a, b, c; int bad=0;
taxi_lfsr #(.LFSR_W(32),.LFSR_POLY(32'h4c11db7),.LFSR_GALOIS(1),.LFSR_FEED_FORWARD(0),.REVERSE(1),.DATA_W(88),.DATA_IN_EN(1'b1),.DATA_OUT_EN(1'b0),.STATE_SHIFT_PRE(0),.STATE_SHIFT_POST(-24)) u(.data_in(d),.state_in(s),.data_out(),.state_out(a));
crc32_tx_d88 p(.data_in(d),.state_out(b)); crc32_tx_d88_lut6 q(.data_in(d),.state_out(c));
initial begin for (int i=0;i<200000;i++) begin d = 88'({$urandom,$urandom,$urandom}) + 0*88*88; s='0; if (i==0) begin d='0; s='0; end if (i==1) begin d='1; s='0; end #1 if (a!==b || a!==c) bad++; end
 $display("R %0d",bad); $finish; end endmodule
