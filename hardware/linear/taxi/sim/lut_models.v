module LUT1 #(parameter [1:0] INIT=0) (output O, input I0); assign O = INIT[{I0}]; endmodule
module LUT2 #(parameter [3:0] INIT=0) (output O, input I0, input I1); assign O = INIT[{I1, I0}]; endmodule
module LUT3 #(parameter [7:0] INIT=0) (output O, input I0, input I1, input I2); assign O = INIT[{I2, I1, I0}]; endmodule
module LUT4 #(parameter [15:0] INIT=0) (output O, input I0, input I1, input I2, input I3); assign O = INIT[{I3, I2, I1, I0}]; endmodule
module LUT5 #(parameter [31:0] INIT=0) (output O, input I0, input I1, input I2, input I3, input I4); assign O = INIT[{I4, I3, I2, I1, I0}]; endmodule
module LUT6 #(parameter [63:0] INIT=0) (output O, input I0, input I1, input I2, input I3, input I4, input I5); assign O = INIT[{I5, I4, I3, I2, I1, I0}]; endmodule
