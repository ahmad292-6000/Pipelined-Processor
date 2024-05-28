module inst_rom #(parameter N=32, DEPTH=32)
(input [N-1:0]address, output reg [N-1:0] instruction); 	reg [N-1:0] memory [DEPTH-1:0]; 

	initial begin

                memory[0] = 32'b100011_00011_00001_00000_00000_000011; // opcode = 35; rs = 3;[3] rt = 1;[1] imm = 3; (LW); Mem_address = 6; mem[6] = reg[1] = 6;
                memory[1] = 32'b000000_00001_00011_00000_00000_000010; // opcode = 0; rs = 1;[6] rt = 3;[3] rd = 0; ALU_amswer = 3; reg[0] = 18; (MULTIPLY)
                //memory[1] = 32'b000000_00011_00000_00000_00000_000010; // opcode = 0; rs1 = 3;[3] rs2 = 0;[3] rd = 1; shamt = 0; funct = 2(MULTIPLY); ALU_answer = 9; reg[0] = 9;
                
 		//memory [0] = 32'b000010_00000_00000_00000_000000_00010; // opcode = 2; imm = 2 (JUMP) next_address = 4 
		//memory [1] = 32'b000100_00000_00011_00000_000000_00011; // opcode = 4; rs1 = 9; rs2 = 1; imm = 3; (BEQ) next_address = 6;
                                               // The answers below impley that the above lines are not executed
		//memory [1] = 32'b000000_00001_00000_00011_00000_000010; // opcode = 0; rs1 = 0;[9] rs2 = 4;[4] rd = 1; shamt = 0; funct = 0;(ADD); ALU_answer = 13; reg[1] = 13;
		//memory [2] = 32'b000000_00000_00100_00001_00000_000000; // opcode = 0; rs1 = 0;[9] rs2 = 4;[4] rd = 1; shamt = 0; funct = 0;(ADD); ALU_answer = 13; reg[1] = 13;
		memory [2] = 32'b000000_00001_01000_00011_00000_000010; // opcode = 0; rs1 = 1; rs2 = 8; rd = 3; shamt = 0; funct = 2(MULTIPLY); ALU_answer = 48; reg[3] = 48;
		memory [3] = 32'b100011_00011_00001_00100_00000_000011; // opcode = 35; rs1 = 1;[5] rs2 = 0;[0] imm = 3; (LW);    Mem_address = 8; mem[8] = 0;
		memory [5] = 32'b101011_00001_00000_00000_00000_001111; // opcode = 43; rs1 = 1;[5] rs2 = 0;[0] imm = 15; (SW);   Mem_address = 20; reg[0] = mem[20] = 20;
		memory [6] = 32'b000000_00001_00000_00011_00000_000010; // opcode = 0; rs1 = 1[5]; rs2 = 0[20]; rd = 3; shamt = 0; funct = 2(MULTIPLY); ALU_answer = 100; reg[3] = 100;
                memory [7] = 32'b101011_01001_01010_00000_00000_001000; // opcode = 43; rs1 = 9;[0] rs2 = 10;[x] imm = 8; (SW);   Mem_address = 8; reg[10] = mem[8] = 0;
		memory [8] = 32'b000000_01001_01010_00011_00000_000010; // opcode = 0; rs1 = 9;[0] rs2 = 10;[0] rd = 3; shamt = 0; funct = 2(MULTIPLY); ALU_answer = 0; reg[3] = 0;
		//memory [9] = 32'b000100_00000_00000_11111_111111_11110; // opcode = 4; rs1 = 0; rs2 = 0; imm = -2; shift_imm = -8 (BEQ) next_address = 2 
                memory [9] = 32'b000000_00001_00010_01010_11111_101010; // opcode = 6; rs1 = 1;[5] rs2 = 2;[2] rd = 10; shamt = 31; funct = 31; (SLT) ALU_answer = 1; reg[10] = 1;
               memory [10] = 32'b000000_00001_01010_00011_00000_000010; // opcode = 0; rs1 = 1;[5] rs2 = 10;[1] rd = 3; shamt = 0; funct = 2(MULTIPLY); ALU_answer = 5; reg[3] = 5;
               memory [11] = 32'b001111_00001_01010_00000_00000_000001; // opcode = 15; rt = 1; imm = 1; (LUI) shifted_imm = 2^16; reg[1] = 2^16
               memory [12] = 32'b001000_01010_00001_00000_00000_000001; // opcode = 8;  rt = 9; rs = 1;[2^16] alu_answer = 2^16+1; reg[9] = 2^16+1; addi
               
	end
	always@(address)
		instruction <= memory [address];
endmodule

module PC ( jump_address,out_address, clk, rst,register_write);
  input [31:0]jump_address;
  input clk , rst;
  input register_write;
  output reg [31:0]out_address;

  always@ (posedge clk)
    begin 
         if(register_write == 0) begin
            if(rst)
               out_address <= 0;
            else
               begin
                 if(jump_address < 0)
                    out_address <= 0;
                 else
                    out_address <= jump_address;
                 end
              end 
          end
endmodule

module Fetch_register(
  input clk,
  input register_write,
  input IF_Flush,
  input [31:0] instruction,
  input [31:0]PC_next,
  output reg [6:0] opcode,   // Note: opcode has 7 bits in order to avoid 2's complement subtraction when MSB is 1
// I type instruction            //                                           ^
  output reg [15:0] offset,      //                                           |
// R type instruction            //                                           |
  output reg [4:0] rs2,          //                                           |
  output reg [4:0] rs1,          //                                           |
  output reg [4:0] rd,           //                                           |
  output reg [4:0] shamt,        //                                           |
  output reg [5:0] funct,        //                                           |
// J type instruction            //                                           |
  output reg [25:0] imm,         //                                           |
  output reg [31:0] PC_next_IF
);                               //                                           |
                                 //                                           |  
always @(posedge clk)            //                                           |
begin    
if(register_write == 0)  begin                                                   
// common data between all instructions
 opcode <=  {1'b0,instruction [31 :26]};   // Note: in opcode we can concatinating the opcode bits of instruction with 0
// common data between R and I type
 rs1<= instruction [25 :21];
 rs2 <= instruction [20 :16];
// R type instruction
 rd <= instruction[15:11];
 shamt <= instruction[10:6];
 funct <= instruction[5:0];
// I type instruction
 offset <= instruction[15:0];
// J type instruction
 imm <= instruction[25:0];
 PC_next_IF <= PC_next;
end
if(IF_Flush) begin
 opcode <=  7'd50;   
 rs1<= 5'd0;
 rs2 <= 5'd0;
 rd <= 5'd0;
 shamt <= 5'd0;
 funct <= 6'd0;
 offset <= 16'd0;
 imm <= 26'd0;
 PC_next_IF <= 32'd0;
end
  end

endmodule

module ALU(
    input [3:0] op,
    input [31:0] a,
    input [31:0] b,
    input [4:0]shamt,
    output reg [31:0] f,
    output reg zero_flag         // for beq instruction
);

parameter Add = 4'b0000, Sub = 4'b0001, Mul = 4'b0010, Shift_Left = 4'b0100, Shift_Right = 4'b0011, And = 4'b0100, Or = 4'b0101, Slt = 4'b0111;

  always @(*) begin
    case(op)
        Add:         f <= a + b;
        Sub:         f <= a - b;
        Mul:         f <= a * b;
        Shift_Right: f <= a >> shamt;
        Shift_Left : f <= a << shamt;
        And:         f <= a & b;
        Or:          f <= a | b;
        Slt:         begin 
                       if(a>b)
                          f <= 32'd1;
                       else 
                          f <= 32'd0;
                     end
        default: f <= 16'b0000000000000000; // Default case for any other operation
    endcase
  end

  always@(*)begin
    if(f == 32'd0)
       zero_flag = 1;
    else
       zero_flag = 0;
    end
endmodule

module register_file #(parameter N=32, address_size=5) (clk,write ,reset ,rs_address,rt_address,rd_address,read_data_1,read_data_2,write_data);
  input [N-1:0] write_data;
  input wire clk,reset,write ;
  input [address_size-1:0] rs_address,rt_address,rd_address;
  output[N-1:0] read_data_1,read_data_2;

  reg [N-1:0] register_file[0:N-1];
  integer k;

initial  
begin
  register_file[0]<=32'h0000;
  register_file[1]<=32'h0001;
  register_file[2]<=32'h0002;
  register_file[3]<=32'h0003;
  register_file[4]<=32'h0004;
  register_file[5]<=32'h0005;
  register_file[6]<=32'h0006;
  register_file[7]<=32'h0007;
  register_file[8]<=32'h0008;
  register_file[9]<=32'h0009;
  register_file[10] <=32'h000a;
end

always @ (posedge clk)
begin 
 if (reset)
    for (k = 0; k<8; k = k+1)
       register_file[k] <= k;
 else
    if(write)
      register_file [rd_address] <= write_data;
 end

    assign read_data_1 = register_file[rs_address];
    assign read_data_2 = register_file[rt_address];


endmodule

module data_mem #(parameter N=32, DEPTH=32)
(input [N-1:0]address, input [N-1:0]data_in, output reg[N-1:0] data_out,  input clk, input we, input read); 

	reg [N-1:0] memory [DEPTH-1:0];

	initial begin
	memory[0] = 0;   memory[1] = 1;
	memory[2] = 2;   memory[3] = 3;
	memory[4] = 4;   memory[5] = 5;
	memory[6] = 6;   memory[7] = 7;
	memory[8] = 8;   memory[9] = 9;
	memory[10] = 10; memory[11] = 11; 
        memory[12] = 12; memory[13] = 13;
	memory[14] = 14; memory[15] = 15;
	memory[16] = 16; memory[17] = 17;
	memory[18] = 18; memory[19] = 19;
	memory[20] = 20; memory[21] = 21;
	end
	
	always@(*)  
		if(read)
	             data_out <= memory [address]; 
	
	always @(posedge clk)  
		if (we)
		     memory [address] <= data_in; 	
endmodule 


module sign_extend(
  input [15:0] imm,
  output [31:0] full
);

  assign full = {{16{imm[15]}}, imm};

endmodule

module Control_unit(
input [6:0]opcode,
output reg RegDst,
output reg ALUsrc,
output reg Memwrite,
output reg Memread,
output reg Branch,
output reg Regwrite,
output reg [1:0] ALUop,
output reg MemtoReg,
output reg jump,
output reg IF_Flush
);
always @(opcode)
begin
if(opcode == 7'dx)
begin RegDst <= 1'bx; ALUop <= 2'bxx; Memwrite <=1'bx; Memread <= 1'bx; Branch <= 1'bx; ALUsrc <= 1'bx; Regwrite <= 1'bx; MemtoReg <= 1'bx; jump <= 1'bx; IF_Flush <= 1'dx; end // default
else if(opcode == 7'd0)
begin RegDst <= 1; ALUop <= 2'b00; Memwrite <=0; Memread <= 0; Branch <= 0; ALUsrc <= 0; Regwrite <= 1; MemtoReg <= 0; jump <= 0; IF_Flush <= 0; end // R type
else if(opcode == 7'd8)
begin RegDst <= 0; ALUop <= 2'b10; Memwrite <=0; Memread <= 0; Branch <= 0; ALUsrc <= 1; Regwrite <= 1; MemtoReg <= 0; jump <= 0; IF_Flush <= 0;  end // addi
else if (opcode == 7'd35)
begin RegDst <= 0; ALUop <= 2'b10; Memwrite <=0; Memread <= 1; Branch <= 0; ALUsrc <= 1; Regwrite <= 1; MemtoReg <= 0; jump <= 0; IF_Flush <= 0;  end // lw
else if(opcode == 7'd43)
begin RegDst <= 0; ALUop <= 2'b10; Memwrite <=1; Memread <= 0; Branch <= 0; ALUsrc <= 1; Regwrite <= 0; MemtoReg <= 1; jump <= 0; IF_Flush <= 0;  end // sw
else if(opcode == 7'd4)
begin RegDst <= 0; ALUop <= 2'b01; Memwrite <=0; Memread <= 0; Branch <= 1; ALUsrc <= 0; Regwrite <= 0; MemtoReg <= 0; jump <= 0; IF_Flush <= 1;  end // beq
else if(opcode == 7'd2)
begin RegDst <= 0; ALUop <= 2'bxx; Memwrite <=0; Memread <= 0; Branch <= 0; ALUsrc <= 0; Regwrite <= 0; MemtoReg <= 0; jump <= 1; IF_Flush <= 1;  end // jump
else
begin RegDst <= 0; ALUop <= 2'b00; Memwrite <=0; Memread <= 0; Branch <= 0; ALUsrc <= 0; Regwrite <= 0; MemtoReg <= 0; jump <= 0; IF_Flush <= 0;  end // invalid instruction

end

endmodule

module ALU_control(
input [5:0] funct,
input [1:0] ALUop,
output reg [3:0] sel_signal
);

always @(funct or ALUop)
begin
  if(ALUop == 2'b00)  // R type instruction
  begin
    case(funct)
      6'd0: sel_signal = 4'd0;  // addition
      6'd1: sel_signal = 4'd1;  // subtraction
      6'd2: sel_signal = 4'd2;  // multiply
      6'd3: sel_signal = 4'd3;  // shift_right
      6'd4: sel_signal = 4'd4;  // shift_left
      6'd5: sel_signal = 4'd5;  // And
      6'd6: sel_signal = 4'd6;  // Or
      6'h2a: sel_signal = 4'd7; // slt
    endcase
  end
  else if(ALUop == 2'b10)  // I type instruction
    sel_signal = 4'd0; // addition
  else if(ALUop == 2'b01)  // B type instruction
    sel_signal = 4'd1; // subtraction
end

endmodule

module Branch_address_ALU(
input [31:0] PC_next_address,
input [15:0] imm,
output reg [31:0] branch_address
);

always@(*)
branch_address <= PC_next_address + {{16{imm[15]}}, imm};

endmodule

module shift_left_2(
input [31:0] offset,
output [31:0] shift_left_offset
);

assign shift_left_offset = offset << 2;

endmodule

module jump_address_CAL(
input [31:0]PC_next_address,
input [25:0] imm,
output [31:0] jump_address
);

assign jump_address = {PC_next_address[31:28],imm << 1};

endmodule

module PC_next_address(
input [31:0]PC_current_address,
output [31:0]PC_next_address
);

assign PC_next_address = PC_current_address + 1;

endmodule 

module Decode_register(
input clk,
input register_write,
input [15:0] offset,
input [25:0] imm,
input [4:0] shamt,
input [5:0] funct,
input [31:0]PC_next,
input[4:0] rs2,
input [4:0] rs1,
input [4:0] rd,
input [31:0] read_data_1,  // missing imm ,funct, offset
input [31:0] read_data_2,
input RegDst,
input ALUsrc,
input Memwrite,
input Memread,
input Regwrite,
input Branch,
input [1:0] ALUop,
input MemtoReg,
input jump,
output reg [15:0] offset_DE,
output reg [25:0] imm_DE,
output reg [4:0] shamt_DE,
output reg [5:0] funct_DE,
output reg[31:0]PC_next_IF,
output reg[4:0] IF_rs2,
output reg[4:0] IF_rs1,
output reg[4:0] IF_rd,
output reg[31:0] read_data_1_IF,
output reg[31:0] read_data_2_IF,
output reg RegDst_IF,
output reg ALUsrc_IF,
output reg Memwrite_IF,
output reg Memread_IF,
output reg Regwrite_IF,
output reg Branch_IF,
output reg [1:0] ALUop_IF,
output reg MemtoReg_IF,
output reg jump_IF

);

always@(posedge clk)
begin
if(register_write == 0) begin
offset_DE <= offset;
imm_DE <= imm;
shamt_DE <= shamt;
funct_DE <= funct;
PC_next_IF <= PC_next;
IF_rs2 <= rs2;
IF_rs1 <= rs1;
IF_rd <= rd;
read_data_1_IF <= read_data_1;
read_data_2_IF <= read_data_2;
RegDst_IF <= RegDst;
ALUsrc_IF <= ALUsrc;
Memwrite_IF <= Memwrite;
Memread_IF <= Memread;
Regwrite_IF <= Regwrite;
Branch_IF <= Branch;
ALUop_IF <= ALUop;
MemtoReg_IF <= MemtoReg;
jump_IF <= jump;
 end
else begin
offset_DE <= 16'dx;
imm_DE <= 26'dx;
shamt_DE <= 4'dx;
funct_DE <= 5'dx;
PC_next_IF <= 32'dx;
IF_rs2 <= 5'dx;
IF_rs1 <= 5'dx;
IF_rd <= 5'dx;
read_data_1_IF <= 32'dx;
read_data_2_IF <= 32'dx;
RegDst_IF <= 1'dx;
ALUsrc_IF <= 1'dx;
Memwrite_IF <= 1'dx;
Memread_IF <= 1'dx;
Regwrite_IF <= 1'dx;
Branch_IF <= 1'dx;
ALUop_IF <= 2'dx;
MemtoReg_IF <= 1'dx;
jump_IF <= 1'dx;
end
end
endmodule

module Execution_register(
input clk,
input [31:0]PC_next,
input[4:0] rt,
input [4:0] rs,
input [4:0] rd,
input [31:0] ALU_result,
input [31:0] read_data_2_DE,
input Memwrite,
input Memread,
input Regwrite,
input Branch,
input MemtoReg,
input jump,
output reg[31:0]PC_next_Exe,
output reg[4:0] Exe_rt,
output reg[4:0] Exe_rs,
output reg[4:0] Exe_rd,
output reg [31:0] ALU_result_Exe,
output reg [31:0] read_data_2_Exe,
output reg Memwrite_Exe,
output reg Memread_Exe,
output reg Regwrite_Exe,
output reg Branch_Exe,
output reg MemtoReg_Exe,
output reg jump_Exe

);

always@(posedge clk)
begin
//if(register_write == 0) begin
PC_next_Exe <= PC_next;
Exe_rt <= rt;
Exe_rs <= rs;
Exe_rd <= rd;
ALU_result_Exe <= ALU_result;
Memwrite_Exe <= Memwrite;
Memread_Exe <= Memread;
Regwrite_Exe <= Regwrite;
Branch_Exe <= Branch;
MemtoReg_Exe <= MemtoReg;
jump_Exe <= jump;
// end
/*else begin
PC_next_Exe <= 32'dx;
Exe_rs2 <= 5'dx;
Exw_rs1 <= 5'dx;
Exe_rd <= 5'dx;
Memwrite_Exe <= 1'dx;
Memread_Exe <= 1'dx;
Regwrite_Exe <= 1'dx;
Branch_Exe <= 1'dx;
MemtoReg_Exe <= 1'dx;
jump_Exe <= 1'dx;
end*/
end
endmodule

module Data_Memory_register(
input clk,
input Regwrite_Exe,
input [31:0] write_data,
input [4:0] Exe_rd,
output reg Regwrite_Mem,
output reg [31:0] write_data_Mem,
output reg [4:0] Mem_rd
);

always@(posedge clk) begin
Regwrite_Mem <= Regwrite_Exe;
write_data_Mem <= write_data;
Mem_rd <= Exe_rd;
end

endmodule

module forwarding_unit(
input Exe_Memread,
input [4:0] Mem_rd,
input [4:0] Exe_rd,

input [4:0] Exe_rs,
input [4:0] Exe_rt,

input [4:0] ID_rs,
input [4:0] ID_rt,

output reg [1:0] ALU_data_1_flag,
output reg [1:0] ALU_data_2_flag
);

always@(*) begin
if (Exe_Memread) begin
  if(Mem_rd == Exe_rs)
       ALU_data_1_flag = 0;
  if(Mem_rd == Exe_rt)
       ALU_data_2_flag = 0; end
else begin
if(Exe_rd == Mem_rd && Exe_rd == ID_rs)
    ALU_data_1_flag = 1;
else if (Exe_rd == ID_rs)
    ALU_data_1_flag = 1;
else if (Mem_rd == ID_rs)
    ALU_data_1_flag = 2;
else 
    ALU_data_1_flag = 3;

if(Exe_rd == Mem_rd && Exe_rd == ID_rt)
    ALU_data_2_flag = 1;
else if (Exe_rd == ID_rt)
    ALU_data_2_flag = 1;
else if (Mem_rd == ID_rt)
    ALU_data_2_flag = 2;
else 
    ALU_data_2_flag = 3;
end

end
endmodule

module Hazard_control(
input rst,
input DE_Memread,
input IF_jump,
input IF_Branch,
input [4:0]DE_rd,
input [4:0]IF_rt,
input [4:0]IF_rs,
output reg register_write
);

always@(*) begin
if (rst)
   register_write <= 0;

if(DE_Memread && IF_jump == 0 && IF_Branch == 0) 
   if(DE_rd == IF_rt || DE_rd == IF_rs)
        register_write <= 1;
   else
        register_write <= 0; 
else 
   register_write <= 0;

end
endmodule


module Pipelined_Processor(
input clk,
input rst
);
wire [31:0]out_address;
wire [31:0]PC_next;
wire[31:0]instruction;
wire [15:0] offset;
wire [4:0] rt;
wire [4:0] rs;
wire [4:0] rd;
wire [4:0] shamt;
wire [5:0] funct;
wire [6:0] opcode;
wire [25:0] imm;
wire [31:0] PC_next_IF;

// reg_file
  wire [31:0] read_data_1;
  wire [31:0] read_data_2;
// signed_extended_output
  wire [31:0] sign_extended_output;
// control signals
  wire RegDst;
  wire ALUsrc;
  wire Memwrite;
  wire Memread;
  wire Regwrite;
  wire Branch;
  wire [1:0] ALUop;
  wire MemtoReg;
  wire jump;
  wire IF_Flush;
// DECODE REGISTER
wire[31:0]PC_next_DE;
wire [15:0]offset_DE;
wire [25:0]imm_DE;
wire [5:0]funct_DE;
wire [4:0]shamt_DE;
wire[4:0] DE_rt;
wire[4:0] DE_rs;
wire[4:0] DE_rd;
wire[31:0] read_data_1_DE;
wire[31:0] read_data_2_DE;
wire RegDst_DE;
wire ALUsrc_DE;
wire Memwrite_DE;
wire Memread_DE;
wire Regwrite_DE;
wire Branch_DE;
wire [1:0] ALUop_DE;
wire MemtoReg_DE;
wire jump_DE;
// EXECUTION REGISTER
wire [31:0]PC_next_Exe;
wire[4:0] Exe_rt;
wire [4:0] Exe_rs;
wire [4:0] Exe_rd;
wire [31:0] ALU_result_Exe;
wire [31:0] read_data_2_Exe;
wire Memwrite_Exe;
wire Memread_Exe;
wire Regwrite_Exe;
wire Branch_Exe;
wire MemtoReg_Exe;
wire jump_Exe;
// hazard control
wire register_write;
// ALU control unit
wire [3:0] select_signal;
wire [31:0] ALU_result;
wire zero_flag;
reg [31:0] ALU_data_1;
reg [31:0] ALU_data_2;
// Forwarding unit
wire [1:0] ALU_data_1_flag;
wire [1:0] ALU_data_2_flag;
// Data memory
wire [31:0]data_memory_output;
reg [31:0] write_data;
// Data memory register
wire Regwrite_Mem;
wire [31:0]write_data_Mem;
wire [4:0] Mem_rd;
// Decode ALU unit
reg [31:0] DE_ALU_data_1;
reg [31:0] DE_ALU_data_2;
reg [31:0] DE_results;
reg DE_zeroflag;
wire [31:0]DE_branchaddress;
//
reg [4:0]rd_;
reg [31:0] ALU_second_op;
reg [31:0] next_address;
// jump address
wire [31:0] jump_address;
reg jump_sig;
// read_vals
reg [31:0]read_data_1_val;
reg [31:0]read_data_2_val;

/////////////////////////////////////
////////////////////////////////////
//STAGE 1 IF/ID REGISTER FETCH STATE
///////////////////////////////////
//////////////////////////////////

PC uut (next_address, out_address, clk, rst,register_write);
PC_next_address pnau(out_address,PC_next);
inst_rom utt (out_address, instruction);

jump_address_CAL jac(PC_next,instruction[25:0],jump_address);

always@(*) begin
if(DE_zeroflag && Branch)
    next_address <= DE_branchaddress;
else if(jump_sig)
    next_address <= jump_address;
else 
    next_address <= PC_next;
end

always@(*) begin
  if(instruction[31:26] == 6'd2)
     jump_sig <= 1;
  else 
      jump_sig <= 0;
end

Fetch_register fru (clk,register_write,IF_Flush,instruction,PC_next,opcode,offset,rt,rs,rd,shamt,funct,imm,PC_next_IF);

//////////////////////////////////////
/////////////////////////////////////
//STAGE 2 ID/EX REGISTER DECODE STATE
///////////////////////////////////
//////////////////////////////////

Control_unit cut(opcode,RegDst,ALUsrc,Memwrite,Memread,Branch,Regwrite,ALUop,MemtoReg,jump,IF_Flush);
register_file rfu(clk,Regwrite_Mem,rst,rs,rt,Mem_rd,read_data_1,read_data_2,write_data_Mem);
sign_extend seu (offset, sign_extended_output);

always@(*) begin
if(Regwrite_Mem) 
   if(rs == Mem_rd)
      read_data_1_val <= write_data_Mem;
   else
      read_data_1_val <= read_data_1;
else
   read_data_1_val <= read_data_1;
end

always@(*) begin
if(Regwrite_Mem) 
   if(rt == Mem_rd)
      read_data_2_val <= write_data_Mem;
   else
      read_data_2_val <= read_data_2;
else
   read_data_2_val <= read_data_2;
end


always@(*) begin
if(RegDst)
rd_ <= rd;
else
rd_ <= rt;
end

always@(*) begin
   if(DE_rd == rs) 
       DE_ALU_data_1 <= ALU_result;
   else if(Exe_rd == rs)
       DE_ALU_data_1 <= write_data;
   else 
       DE_ALU_data_1 <= read_data_1;

   if(DE_rd == rt)
       DE_ALU_data_2 <= ALU_result;
   else if(Exe_rd == rt)
       DE_ALU_data_2 <= write_data;
   else 
       DE_ALU_data_2 <= read_data_2;
end

always@(*) begin
DE_results <= DE_ALU_data_1 - DE_ALU_data_2;

if(DE_results == 0)
   DE_zeroflag <= 1;
else
   DE_zeroflag <= 0;
end

Branch_address_ALU baau(PC_next_IF,imm,DE_branchaddress);

Decode_register dru(clk,register_write,offset,imm,shamt,funct,PC_next_IF,rt,rs,rd_,read_data_1_val,read_data_2_val,RegDst,ALUsrc,Memwrite,Memread,Branch,Regwrite,ALUop,MemtoReg,jump,offset_DE,imm_DE,shamt_DE,funct_DE,PC_next_DE,DE_rt,DE_rs,DE_rd,read_data_1_DE,read_data_2_DE,RegDst_DE,ALUsrc_DE,Memwrite_DE,Memread_DE,Branch_DE,Regwrite_DE,ALUop_DE,MemtoReg_DE,jump_DE);

Hazard_control hcu(rst,Memread_DE,jump,Branch,DE_rd,rs,rt,register_write);


//////////////////////////////////////////
/////////////////////////////////////////
//STAGE 3 ID/EXE REGISTER EXECUTION STATE
////////////////////////////////////////
///////////////////////////////////////

ALU_control acl (funct_DE,ALUop_DE,select_signal);
ALU auu(select_signal,ALU_data_1,ALU_data_2,shamt_DE,ALU_result,zero_flag);
forwarding_unit fuu(Memread_Exe,Mem_rd,Exe_rd,Exe_rs,Exe_rt,DE_rs,DE_rt,ALU_data_1_flag,ALU_data_2_flag);

always@(*) begin
if(ALUsrc_DE)
   ALU_second_op <= offset_DE;
else 
   ALU_second_op <= read_data_2_DE;
end

always@(*) begin
if(ALU_data_1_flag == 0 || ALU_data_1_flag == 2)
   ALU_data_1 <= write_data_Mem;
else if(ALU_data_1_flag == 1)
   ALU_data_1 <= ALU_result_Exe;
else if(ALU_data_1_flag == 3)
   ALU_data_1 <= read_data_1_DE;
end

always@(*) begin
if(ALU_data_2_flag == 0 || ALU_data_2_flag == 2)
   ALU_data_2 <= write_data_Mem;              // fix when mem data register is made
else if(ALU_data_2_flag == 1)
   ALU_data_2 <= ALU_result_Exe; // Exe_rd 
else if(ALU_data_2_flag == 3)
   ALU_data_2 <= ALU_second_op;  // DE_rt
end

Execution_register eru(clk,PC_next_DE,DE_rt,DE_rs,DE_rd,ALU_result,read_data_2_DE,Memwrite_DE,Memread_DE,Branch_DE,Regwrite_DE,MemtoReg_DE,jump_DE,PC_next_Exe,Exe_rt,Exe_rs,Exe_rd,ALU_result_Exe,read_data_2_Exe,Memwrite_Exe,Memread_Exe,Branch_Exe,Regwrite_Exe,MemtoReg_Exe,jump_Exe);


//////////////////////////////////////////
/////////////////////////////////////////
//STAGE 4 EXE/MEM DATA MEMORY STATE/////
////////////////////////////////////////
///////////////////////////////////////

data_mem dmu(ALU_result_Exe,read_data_2_Exe,data_memory_output,clk,Memwrite_Exe,Memread_Exe);

always@(*) begin
if(MemtoReg_Exe)
write_data <= data_memory_output;
else 
write_data <= ALU_result_Exe;
end

Data_Memory_register dmr(clk,Regwrite_Exe,write_data,Exe_rd,Regwrite_Mem,write_data_Mem,Mem_rd);
 
endmodule







