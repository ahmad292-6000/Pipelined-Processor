module sp (clk,op1,op2,op3);
input [16:0]op1,op2,op3;
reg[16:0] trigger;
input clk;
reg negative_flag,overflow_flag,carry_flag,zero_flag;
wire msb_op1,msb_op2,msb_op3;

assign msb_op1 = op1 [16:15];
assign msb_op2 = op2 [16:15];
assign msb_op3 = op3 [16:15];

always@(posedge clk)
begin
if (op1>0 || op2>0)
negative_flag = 1;

if (negative_flag == 1 && op1>0)
begin
trigger = 1 + ~(op1);
if (trigger == op2)
zero_flag = 1;
else 
zero_flag = 0;
end

else if (negative_flag == 1 && op2>0)
begin
trigger = 1 + ~(op2);
if (trigger == op1)
zero_flag = 1;
else 
zero_flag = 0;
end

else if (msb_op1 == msb_op2 && msb_op1!=msb_op3)
overflow_flag = 1;
end

endmodule 