`timescale 1ns / 1ps

////////////////////////////////////////////////////////////////////////////////
// Company: 
// Engineer:
//
// Create Date:   14:32:36 11/05/2018
// Design Name:   Processor
// Module Name:   C:/Users/student/COA_CT_1/SCC_Final/test.v
// Project Name:  SCC_Final
// Target Device:  
// Tool versions:  
// Description: 
//
// Verilog Test Fixture created by ISE for module: Processor
//
// Dependencies:
// 
// Revision:
// Revision 0.01 - File Created
// Additional Comments:
// 
////////////////////////////////////////////////////////////////////////////////

module test;

	// Inputs
	reg clk;
	reg rst;

	// Outputs
	wire [31:0] out;

	// Instantiate the Unit Under Test (UUT)
	Processor uut (
		.clk(clk), 
		.rst(rst), 
		.out(out)
	);
	
	always #40 clk = ~clk;

	initial begin
		// Initialize Inputs
		clk = 0;
		rst = 1;

		// Wait 100 ns for global reset to finish
		#80;
		rst =0;
		#4000;
      $finish;
		// Add stimulus here

	end
      
endmodule

