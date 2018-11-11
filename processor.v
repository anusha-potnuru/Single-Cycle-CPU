`timescale 1ns / 1ps
//////////////////////////////////////////////////////////////////////////////////
// Name: P ANUSHA 
// Name: P V S L Hari Chandana
// GROUP NO: 47
// Create Date:    14:31:04 11/05/2018 
// Design Name: 
// Module Name:    processor 
// Project Name: 
// Target Devices: 
// Tool versions: 
// Description: 
//
// Dependencies: 
//
// Revision: 
// Revision 0.01 - File Created
// Additional Comments: 
//
//////////////////////////////////////////////////////////////////////////////////

module mux32bit_2_to_1(input[31:0] a, input[31:0] b, output reg[31:0] out, input s);
always@(*)
begin
  if(s)
    out = b;
  else
    out = a;
end
endmodule

module mux5bit_2_to_1(input[4:0] a, input[4:0] b, output reg[4:0] out, input s);
always@(*)
begin
  if(s)
    out = b;
  else
    out = a;
end
endmodule

//changed
module DFF(out, in, reset, clock);
	output out;
	input in;
	//input e;
	input reset;
	input clock;
	(*keep = "true"*) reg mem;
	always @(posedge clock) begin 
		if (reset == 1) 
			mem <= 1'b0; 
		else 
			mem <= in; 
	end 
	assign out = mem;
endmodule

module DFF32bit(out, in, reset, clock);
	output[31:0] out;
	input[31:0] in;
	//input e;
	input reset;
	input clock;
	(*keep = "true"*) reg mem;
	always @(posedge clock) begin 
		if (reset == 1) 
			mem <= 1'b0; 
		else 
			mem <= in; 
	end 
	assign out = mem;
endmodule

module alu(input[31:0] a, input[31:0] b, output reg[31:0] out, input[2:0] alu_cntrl,
			output reg zflag, output reg overflowflag, 
			output reg signflag, output reg carryflag
			 );
always@(*)
begin
	overflowflag =1'b0;
	zflag = 1'b0;
	signflag = 1'b0;
	carryflag = 1'b0;
case(alu_cntrl)
	3'b000: 
		begin
		out = a+b;
		overflowflag = a[31] & b[31] & ~out[31] | ~a[31] & ~b[31] & out[31];
		carryflag = a[31]^b[31]^out[31];
		zflag = (out== 0) ? 1'b1:1'b0;
		signflag = out[31];
		end
	3'b001: out= a-b;
	3'b010: 
		begin
		out = -b;
		zflag = (out== 0) ? 1'b1:1'b0;
		signflag = out[31];
		end
	3'b011: 
		begin
		out = a&b;
		zflag = (out==0) ? 1'b1:1'b0;
		signflag = out[31];
		end
	3'b100:
		begin 
		out = a^b;
		zflag = (out==0) ? 1'b1:1'b0;
		signflag = out[31];
		end
	3'b101: out = a<<b;
	3'b110: out = a>>b;
	3'b111: out = a>>>b;
	default: out = a+b;
endcase
	//signflag = out[31];
	$strobe("%t: i1= %b i2=%b alu output %b ", $time,a,b, out);
	$strobe("%t: signflag %b ", $time, signflag);
	//overflowflag = a[31] & b[31] & ~out[31] | ~a[31] & ~b[31] & out[31];
	//carryflag = a[31]^b[31]^out[31];
	
end
endmodule

module mux5bit_4_to_1(input[4:0] in1,input[4:0] in2, input[4:0] in3, output reg[4:0] out , input[1:0] sel);
always@(*)
begin
if(sel == 2'b00)
out = in1;
else if(sel == 2'b01)
out = in2;
else if(sel == 2'b10)
out = in3;
else 
out = in1;
end
endmodule


module alucontrol(input[5:0] opcode, output reg[2:0] alu_cntrl);

always@(opcode)
begin
casex(opcode)
  //6'b100xxx: alu_cntrl = 3'b001;
  //6'b101010: alu_cntrl = 3'b000;
  6'b0x0000: alu_cntrl = 3'b000; //optimise xx0000
  6'b01001x: alu_cntrl = 3'b000;
  6'b0x0001: alu_cntrl = 3'b010;
  6'b000010: alu_cntrl = 3'b011;
  6'b000011: alu_cntrl = 3'b100;
  6'b0001x0: alu_cntrl = 3'b101;
  6'b0001x1: alu_cntrl = 3'b110;
  6'b00100x: alu_cntrl = 3'b111;
  default : alu_cntrl = 3'b000;
endcase
end 
endmodule
/*
module registerBank(
 input    clk,
 // write port
 input    reg_write_en,
 //input  [4:0] reg_write_dest,
 input  [31:0] reg_write_data,
 //read port 1
 input  [4:0] reg_read_addr_1,
 output  [31:0] reg_read_data_1,
 //read port 2
 input  [4:0] reg_read_addr_2,
 output  [31:0] reg_read_data_2
);
 reg [31:0] reg_array [4:0];
 integer i;
 // write port
 //reg [2:0] i;
 initial begin
  for(i=0;i<32;i=i+1)
   reg_array[i] <= 32'd0;
 end
 always @ (posedge clk ) begin
   if(reg_write_en) begin
    reg_array[reg_write_dest] <= reg_write_data;
   end
 end
 
 assign reg_read_data_1 = reg_array[reg_read_addr_1];
 assign reg_read_data_2 = reg_array[reg_read_addr_2];

endmodule
*/
module Control_Unit(
      input[5:0] opcode,
      output reg[2:0] alu_op,
		output reg[2:0] flag,
    output reg[1:0] call,
      output reg jump,branch,mem_read,mem_write,alu_src,mem_to_reg,reg_write,ret , ra_write, add_calc 
    );


always @(*)
begin
  alu_src = 0;mem_to_reg=0;reg_write=0;mem_read=0;mem_write=0;alu_op=3'b0;jump=0;branch=0;ret=0;call=2'b00;
  add_calc=0;ra_write=0;flag=3'b000;
 case(opcode) 
 6'b010010:  // LW
   begin
    alu_src = 1'b1;
   call = 2'b10;
    mem_to_reg = 1'b1;
    reg_write = 1'b1;
    mem_read = 1'b1;
   alu_op=3'b000;
   end
 6'b010011:  // SW
   begin
    alu_src = 1'b1;
    mem_write = 1'b1;
   alu_op=3'b000;
   end
 6'b000000:  // add
   begin
    reg_write = 1'b1;
   alu_op=3'b000;
   end
 6'b000001:  // comp
   begin
    reg_write = 1'b1;
    alu_op = 3'b010;
   end
 6'b000010:  // and
   begin
    reg_write = 1'b1;
    alu_op = 3'b011;
   end
 6'b000011:  // xor
   begin
    reg_write = 1'b1;
    alu_op = 3'b100;
   end
 6'b010000:  // addi
   begin
    alu_src = 1'b1;
    reg_write = 1'b1;
   alu_op = 3'b000;
   end
 6'b010001:  // compi
   begin
    alu_src = 1'b1;
    reg_write = 1'b1;
    alu_op = 3'b010;
   end
 6'b000100:  //shll
   begin
    alu_src = 1'b1;
    reg_write = 1'b1;
    alu_op = 3'b101;
   end
 6'b000101:  // shrl
   begin
    alu_src = 1'b1;
    reg_write = 1'b1;
    alu_op = 3'b110;
   end
 6'b010001:  // shllv
   begin
    reg_write = 1'b1;
    alu_op = 3'b101;
   end
 6'b000111:  // shrlv
   begin
    reg_write = 1'b1;
    alu_op = 3'b110;
   end
 6'b001000:  // shra
   begin
    alu_src = 1'b1;
    reg_write = 1'b1;
    alu_op = 3'b111;
   end  
  6'b001001:  // shrav
   begin
    reg_write = 1'b1;
    alu_op = 3'b111;
   end 
  6'b101000:  // b
   begin
    jump = 1'b1; 
   end 
  6'b101001:  // br
   begin
   jump = 1'b1;
   add_calc = 1'b1;  
   end 
  6'b100000: //bz
  begin
    branch = 1'b1;
    flag = 3'b00;
  end
  6'b100001:   //bnz
  begin
    branch = 1'b1;
    flag = 3'b001;
  end
  6'b100010:   //bcy
  begin
    branch = 1'b1;
    flag = 3'b010;
  end
  6'b100011:   //bncy
  begin
    branch = 1'b1;
    flag = 3'b011;
  end
  6'b100100:   //bs
  begin
    branch = 1'b1;
    flag = 3'b100;
  end
  6'b100101:   //bns
  begin
    branch = 1'b1;
    flag = 3'b101;
  end
  6'b100110:   //bv
  begin
    branch = 1'b1;
    flag = 3'b110;
  end
  6'b100111:   //bnv
  begin
    branch = 1'b1;
    flag = 3'b111;
  end
  6'b101000:   //call
  begin
    jump = 1'b1;
    call = 2'b01;
    reg_write=1'b1;
    ra_write=1'b1;
  end
  6'b101011:   //ret
  begin
    jump = 1'b1;
    ret = 1'b1;
  end
 default: begin
    reg_write = 1'b1;
	 alu_op = 3'b000;
   end
 endcase
 end

endmodule

module sign_extension(input[15:0] in , output reg[31:0] out);
always@(*)
begin
 if(in[15] == 1'b0)
 out = {16'b0 , in};
 else
 out = {16'b1111111111111111,in};
 $strobe("%t: sign-extension output %b ", $time, out);
end
endmodule



module ProgramCounter(clk, reset, jump_addr, pc,sel);
	parameter	size=32;
	input		clk;
	input		reset;
	input[31:0] jump_addr;
	wire    [size-1:0] pc_next;
	output	[size-1:0]	pc;
	input 	sel;

	//	The outputs are defined as registers too
	reg	[size-1:0]	pc;
	
	initial 
	begin
		pc = -1;
	end

	mux32bit_2_to_1 M_pc(pc+1, jump_addr, pc_next, sel );


	always @(posedge clk)
	begin
		if (reset)
			pc = -1;
		else
			pc = pc_next; //pc_next is mux output
	end

	always @(posedge clk)
	begin
		$strobe("%3d: PC: %d ", $time,pc);
	end
endmodule
//

module RegisterFile(clk, reset,
							reg_write, 
							read_reg_1,read_reg_2,
							write_register,
							write_data,
							read_data_1,read_data_2);

	 parameter size=32;
	 input    clk;
	 input    reset;

	 // write port
	 input  reg_write;
	 input  [4:0] write_register;
	 input  [size-1:0] write_data;

	 //read port 1
	 input  [4:0]  read_reg_1;
	 output   [size-1:0] read_data_1;

	 //read port 2
	 input  [4:0]  read_reg_2;
	 output  [size-1:0] read_data_2;

	 reg [size-1:0] RF [size-1:0] ;
	 
	
	 integer i,j;
	 // write port

	 assign read_data_2 = RF[read_reg_2];
	 assign read_data_1 = RF[read_reg_1];
//

	 always @(posedge clk )
	 begin
		if (reset)
		begin
			for(i=0;i<size;i=i+1)
				RF[i] = 32'b00000000000000000000000000000000;
		end
		if(reg_write) 
		begin
		   RF[write_register] = write_data;
		   $display("%t: Write_reg %d Write Data %b", $time, write_register, write_data);
		end
	 end
		//assign RF[30] = 32'b0; 
		//$strobe("%t: Read Values1 RF(%d)  %b ", $time, read_reg_1, read_data_1);
		//$strobe("%t: Read Values2 RF(%d)  %b ", $time, read_reg_2, read_data_2);
	/*
	 always @(clk)
	 begin
		$strobe("%t: Read Values1 RF(%d)  %b ", $time, read_reg_1, read_data_1);
		$strobe("%t: Read Values2 RF(%d)  %b ", $time, read_reg_2, read_data_2);
		$strobe("%t: RF(%d)  %b ", $time,0, RF[0]);
		$strobe("%t: RF(%d)  %b ", $time,1, RF[1]);
		$strobe("%t: RF(%d)  %b ", $time,2, RF[2]);
		//$strobe("%t: RF(%d)  %b \n\n", $time,31, RF[31]);
	 end
	 */
endmodule


module instructionMemory(PC,dataOut,reset);
	input[31:0] PC;
	input reset;
	
	output wire[31:0]  dataOut;
	reg[31:0] memory[0:63];

	assign dataOut = memory[PC];

	always @(*)
	begin
		if(reset == 1'b1) begin
			/*memory[0] = 32'b01001000000000010000000000000000;
			//memory[1] = 32'b01001000000000100000000000000001;
			memory[2] = 32'b01000000001000001111111111111111;
			memory[3] = 32'b01001100000000010000000000000010;*/
			//memory[4] = 32'b00001000010000010000000000000000;
			//memory[5] = 32'b01001100000000100000000000000011;
			//memory[4] = 32'b10100000000000000000000000000110;
			//memory[6] = 32'b01000000010000000000000000000011;
			//memory[7] = 32'b01001100000000100000000000000100;
			
			
			memory[0] = {6'b010010, 5'b11110, 5'b00111, 16'b0000000000000001};
			memory[1] = {6'b010010, 5'b11110, 5'b00000, 16'b0000000000000000};
			memory[2] = {6'b010000, 5'b00000, 5'b00000, 16'b0000000000000001};//this is loop1
			memory[3] = {6'b000001, 5'b01000, 5'b00111, 16'b0000000000000000};
			memory[4] = {6'b010010, 5'b11110, 5'b01001, 16'b0000000000000000};
			
			memory[5] = {6'b000011, 5'b01001, 5'b00000, 16'b0000000000000000};
			memory[6] = {6'b000000, 5'b01001, 5'b01000, 16'b0000000000000000};
			memory[7] = {6'b100100, 10'b0, 16'b1010};  //label1
			memory[8] = {6'b000011, 5'b01001, 5'b11110, 16'b0000000000000000};
			memory[9] = {6'b100001, 10'b0, 16'b100001}; //goto end
			memory[10] = {6'b010010, 5'b11110, 5'b00001, 16'b0000000000000000};//this is label1
			memory[11] = {6'b000000, 5'b00001, 5'b00111, 16'b0000000000000000};
			memory[12] = {6'b000001, 5'b01010, 5'b00001, 16'b0000000000000000};//this is loop2
			memory[13] = {6'b010010, 5'b11110, 5'b01011, 16'b0000000000000000};
			memory[14] = {6'b000011, 5'b01011, 5'b00000, 16'b0000000000000000};
			
			memory[15] = {6'b000000, 5'b01011, 5'b01010, 16'b0000000000000000};
			memory[16] = {6'b100101, 10'b0,16'b10}; //goto loop1
			
			memory[17] = {6'b010000, 5'b00001, 5'b00000, 16'b1111111111111111};
			memory[18] = {6'b010010, 5'b11110, 5'b00100, 16'b0 };
			
			memory[19] = {6'b000011, 5'b00100, 5'b00001, 16'b0000000000000000};
			
			memory[20] = {6'b010010, 5'b11110, 5'b00011, 16'b0000000000000000};
			memory[21] = {6'b000011, 5'b00011, 5'b00100, 16'b0000000000000000};
			
			memory[22] = {6'b010000, 5'b00011, 5'b00000, 16'b1111111111111111};
			
			//memory[22] = {6'b010000, 5'b00100, 5'b00000, 16'b0000000000000010};
			//memory[23] = {6'b010000, 5'b00011, 5'b00000, 16'b0000000000000010};
			
			memory[23] = {6'b010010, 5'b00100, 5'b00101, 16'b0000000000000010};
			memory[24] = {6'b010010, 5'b00011, 5'b00110, 16'b0000000000000010};
			
			memory[25] = {6'b000001, 5'b01000, 5'b00110, 16'b0000000000000000};
			memory[26] = {6'b010010, 5'b11110, 5'b01001, 16'b0000000000000000};
			memory[27] = {6'b000011, 5'b01001, 5'b00101, 16'b0000000000000000};
		
			memory[28] = {6'b000000, 5'b01001, 5'b01000, 16'b0000000000000000};
			memory[29] = {6'b100101, 10'b0, 16'b1100}; //goto loop2
			
			memory[30] = {6'b010011, 5'b00011, 5'b00101, 16'b0000000000000010}; //swap	
			memory[31] = {6'b010011, 5'b00100, 5'b00110, 16'b0000000000000010};
			
			memory[32] = {6'b101000, 10'b0, 16'b1100}; //goto loop2
			memory[33] = {6'b000000, 5'b00000, 5'b00000, 16'b0000000000000000};	//this is end	
				
		end
	end
	always@(*)
	begin
	$strobe("instruction: %b",dataOut);
	end
	
endmodule


module dataMemory(clk, Addr,dataOut,reset,dataIn,memwrite);
	input[31:0] Addr;
	input clk;
	input memwrite;
	input reset;
	input[31:0] dataIn;
	output wire[31:0]  dataOut;
	reg[31:0] memory[0:63];

	assign dataOut = memory[Addr];
	always @(posedge clk) begin
		if(reset == 1'b1) begin
		
			memory[0] = 32'b00000000000000000000000000000000;
			memory[1] = 32'b00000000000000000000000000001000;
			memory[2] = 32'b00000000000000000000000000001000;
			memory[3] = 32'b00000000000000000000000000000010;
			memory[4] = 32'b00000000000000000000000000000001;
			memory[5] = 32'b00000000000000000000000000001001;
			memory[6] = 32'b00000000000000000000000000001100;
			memory[7] = 32'b00000000000000000000000000010010;
			memory[8] = 32'b00000000000000000000000000000011;
			memory[9] = 32'b00000000000000000000000000001110;
			
			//memory[0] = 32'b00000000000000000000000000000100;
			//memory[1] = 32'b00000000000000000000000000000100;
			//memory[2] = 32'b00000000000000000000000000000100;
	
		end
		else if(memwrite==1'b1)
		begin
			memory[Addr] = dataIn;
			$strobe("%t: datamemory %b %b",$time, Addr, dataIn);
		end
	end

endmodule

module Processor(clk,rst,out);
	input clk;
	input rst;
	output[31:0] out;
	
	wire[31:0] instruction;
	wire[31:0] pc;
	wire[4:0] read_reg_1_in;
	wire[4:0] read_reg_2_in;
	//reg[4:0] ra;
	wire[4:0] write_register;
	wire[31:0] jump_addr;
	wire[31:0] branch_addr;
	wire[31:0] imm32;

	wire[31:0] read_data_1;
	wire[31:0] read_data_2;
	wire[31:0] read_data_dm;

	wire zflag;
	wire overflowflag;
	wire carryflag; 
	wire signflag;
	
	wire z_flag;
	wire overflow_flag;
	wire carry_flag; 
	wire sign_flag;
	
	wire[2:0] alu_op;
	wire jump,branch,mem_read,mem_write,alu_src,mem_to_reg,reg_write,ret , ra_write, add_calc;
	wire[2:0] flag;
	wire [1:0] call;
	
	wire and_out;
	wire or_output;
	wire zero;
	
	wire[31:0] data_out;
	wire[31:0] write_data;
	wire[31:0] alu_out;
	wire[31:0] alu_out1;
	wire[31:0] alu_input2;

	assign out = data_out;
	
	assign branch_addr = {pc[31:26], instruction[25:0]}; // pc+4
	mux32bit_2_to_1 M1( branch_addr, read_data_1,  jump_addr,add_calc);
	
	assign zero = (flag == 3'b000 && zflag==1) ? 1'b1 : 1'b0   |  (flag == 3'b001 && zflag==0) ? 1'b1 : 1'b0  |  
	(flag == 3'b010 && carryflag==1) ? 1'b1 : 1'b0 |  (flag == 3'b011 && carryflag==0) ? 1'b1 : 1'b0 |  
	(flag == 3'b100 && signflag==1) ? 1'b1 : 1'b0 |  (flag == 3'b101 && signflag==0) ? 1'b1 : 1'b0 |  
	(flag == 3'b110 && overflowflag==1) ? 1'b1 : 1'b0 |  (flag == 3'b111 && overflowflag==0) ? 1'b1 : 1'b0  ;
	

	ProgramCounter P(clk, rst, jump_addr, pc,or_output);

	mux5bit_2_to_1 M2(instruction[25:21], 5'b11111,  read_reg_1_in,ret);
	assign read_reg_2_in = instruction[20:16];

	mux5bit_4_to_1 m3(instruction[25:21], 5'b11111,instruction[20:16], write_register,call );
	mux32bit_2_to_1 m4(  data_out , pc+32'b100, write_data,ra_write);
   mux32bit_2_to_1 m5(alu_out, read_data_dm, data_out,mem_to_reg);


	RegisterFile rf(clk, rst,
							reg_write, 
							read_reg_1_in,read_reg_2_in,
							write_register,
							write_data,
							read_data_1,read_data_2);

	assign and_out = branch & zero;
	assign or_output = jump | and_out;

	
	instructionMemory Instr_Mem(pc,instruction,rst);
	dataMemory data_memory (clk, alu_out,read_data_dm,rst,read_data_2,mem_write);
	
	
	
    mux32bit_2_to_1 m2(read_data_2,imm32 ,alu_input2, alu_src );
    sign_extension  s1(instruction[15:0],imm32);

	alu a( read_data_1, alu_input2, alu_out, alu_op, z_flag, overflow_flag, sign_flag, carry_flag);
	
	//DFF32bit d5(alu_out,alu_out1,rst,clk);
	DFF d1(zflag, z_flag, rst, clk);
	DFF d2(overflowflag, overflow_flag, rst, clk);
	DFF d3(signflag, sign_flag, rst, clk);
	DFF d4(carryflag, carry_flag, rst, clk);
	//alucontrol A1(instruction[31:26], alu_cntrl);
	
	Control_Unit c1(
     instruction[31:26],
       alu_op,
		 flag,
       call,
      jump,branch,mem_read,mem_write,alu_src,mem_to_reg,reg_write,ret , ra_write, add_calc 
    );
	//If write enable (WE) is high, the data at DIN will be written in the adressed memory.
	//If write enable (WE) is high, the data at DIN will be written in the adressed memory.
	
	

endmodule




