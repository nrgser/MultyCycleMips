
`timescale 1ns/100ps 

   `define ADD  4'h0
   `define SUB  4'h1
   `define SLT  4'h2
   `define SLTU 4'h3
   `define AND  4'h4
   `define OR   4'h5
   `define NOR  4'h6
   `define XOR  4'h7
   `define LUI  4'h8
   `define SLL  4'h9
module multi_cycle_mips(

   input clk,
   input reset,

   // Memory Ports
   output  [31:0] mem_addr,
   input   [31:0] mem_read_data,
   output  [31:0] mem_write_data,
   output         mem_read,
   output         mem_write
);

   // Data Path Registers
   reg MRE, MWE;
   reg [31:0] A, B, PC, IR, MDR, MAR,mfHI,mfLO,shift,D,R;

   // Data Path Control Lines, donot forget, regs are not always regs !!
   reg setMRE, clrMRE, setMWE, clrMWE;
   reg Awrt, Bwrt, RFwrt, PCwrt, IRwrt, MDRwrt, MARwrt,shiftEn;

   // Memory Ports Binding
   assign mem_addr = MAR;
   assign mem_read = MRE;
   assign mem_write = MWE;
   assign mem_write_data = B;

   // Mux & ALU Control Lines
   reg [3:0] aluOp;
   reg [2:0] shiftCheck;
   reg [1:0] aluSelB, IorD,pcCheck,RegDst,MemtoReg;
   reg SgnExt, aluSelA,mfCheck,multEn,divEn,err,resets;
   reg [4:0] shiftreg;
   // Wiring
   wire aluZero,finEn,finDivEn;
   wire [31:0] aluResult, rfRD1, rfRD2;
    wire [63:0] result;
   // Clocked Registers
   always @( posedge clk ) begin
      if( reset )
         PC <= #0.1 32'h00000000;
      else if( PCwrt )begin
	 case(pcCheck)
         2'b00: PC <= #0.1 aluResult;
	 2'b01: PC <= #0.1 {PC[31:28],IR[25:0],2'b00};
	 2'b11: PC <= #0.1 A;
	 endcase
       end
      if( Awrt ) A <= #0.1 rfRD1;
      if( Bwrt ) B <= #0.1 rfRD2;

      if( MARwrt )begin
	   case(IorD)
            2'b00: MAR <= #0.1  PC;
  	    2'b01: MAR <= #0.1  aluResult;
 	    2'b10: MAR <= #0.1  {PC[31:28],IR[25:0],2'b00};
     	    2'b11: MAR <= #0.1  A;
	   endcase
	end

      if( IRwrt ) IR <= #0.1 mem_read_data;
      if( MDRwrt ) MDR <= #0.1 mem_read_data;
      if( reset | clrMRE ) MRE <= #0.1 1'b0;
          else if( setMRE) MRE <= #0.1 1'b1;

      if( reset | clrMWE ) MWE <= #0.1 1'b0;
          else if( setMWE) MWE <= #0.1 1'b1;
     if( finEn ) begin
	 mfLO <= #0.1 result[31:0];
         mfHI <= #0.1 result[63:32];
      end
    if(finDivEn)begin
	 mfLO <= #0.1 D;
         mfHI <= #0.1 R;
      end
      if(shiftEn)begin
	case(shiftCheck)
           3'b000:   shift<= #0.1 B<<shiftreg; 
	   3'b001:   shift<= #0.1 B<<shiftreg;
	   3'b010:   shift<= #0.1 B>>shiftreg;
	   3'b011:   shift<= #0.1 B>>>shiftreg;
	   3'b100:   shift<= #0.1 B>>>shiftreg;
	   3'b101:   shift<= #0.1 B>>shiftreg;
	endcase
	end
   end

   // Register File
   reg_file rf(
      .clk( clk ),
      .write( RFwrt ),

      .RR1( IR[25:21] ),
      .RR2( IR[20:16] ),
      .RD1( rfRD1 ),
      .RD2( rfRD2 ),

     .WR( RegDst==2'b01 ? IR[15:11] :RegDst==2'b00 ? IR[20:16] :RegDst==2'b10 ?5'b11111:5'bx),
     .WD( MemtoReg==2'b01 ? MDR :MemtoReg==2'b00 ? aluResult:MemtoReg==2'b10 ? PC:MemtoReg==2'b11 ? mfCheck? mfHI:mfLO: 5'bx)
   );

   // Sign/Zero Extension
   wire [31:0] SZout = SgnExt ? {{16{IR[15]}}, IR[15:0]} : {16'h0000, IR[15:0]};

   // ALU-A Mux
   wire [31:0] aluA = aluSelA ? A : PC;

   // ALU-B Mux
   reg [31:0] aluB;
   always @(*)begin
   case (aluSelB)
      2'b00: aluB = B;
      2'b01: aluB = 32'h4;
      2'b10: aluB = SZout;
      2'b11: aluB = SZout << 2;
   endcase
end
   my_alu alu(
      .A( aluA ),
      .B( aluB ),
      .Op( aluOp ),

      .X( aluResult ),
      .Z( aluZero )
   );


   // Controller Starts Here

   // Controller State Registers
   reg [4:0] state, nxt_state;

   // State Names & Numbers
   localparam
      RESET = 0, FETCH1 = 1, FETCH2 = 2, FETCH3 = 3, DECODE = 4,
      EX_jr=5,EX_jalr=6,EX_ALU_R = 7, EX_ALU_I = 8,EX_j=9,EX_jal=10,
      EX_LW_1 = 11, EX_LW_2 = 12, EX_LW_3= 13, EX_LW_4 = 14, EX_LW_5 = 15,
      EX_SW_1 = 21, EX_SW_2 = 22, EX_SW_3 = 23,
      EX_BRA_1 = 25, EX_BRA_2 = 26,EX_mHI=27,EX_mLo=28,
      EX_multu=29,EX_multu_2=30,EX_multu_3=31,EX_sll=32,EX_sllv=33,EX_srl=34,EX_srlv=35,EX_srav=36,EX_sra=37,EX_div=38,EX_div_2=39,EX_div_3=40;
   // State Clocked Register 
   always @(posedge clk)
      if(reset)
         state <= #0.1 RESET;
      else
         state <= #0.1 nxt_state;

   task PrepareFetch;
      begin
         IorD = 0;
         setMRE = 1;
         MARwrt = 1;
         nxt_state = FETCH1;
      end
   endtask

   // State Machine Body Starts Here
   always @( * ) begin

      nxt_state = 'bx;

      SgnExt = 'bx; IorD = 'bx;
      MemtoReg = 'bx; RegDst = 'bx;mfCheck=1'bx;
      aluSelA = 'bx; aluSelB = 'bx; aluOp = 'bx;

      PCwrt = 0;pcCheck=2'bxx;multEn=1'bx;shiftreg='bx;
      Awrt = 0; Bwrt = 0; shiftEn=0;divEn=1'bx;err=1'bx;
      RFwrt = 0; IRwrt = 0;shiftCheck=3'bxxx;
      MDRwrt = 0; MARwrt = 0;
      setMRE = 0; clrMRE = 0;
      setMWE = 0; clrMWE = 0;

      case(state)

         RESET:
            PrepareFetch;

         FETCH1:
            nxt_state = FETCH2;

         FETCH2:
            nxt_state = FETCH3;

         FETCH3: begin
            IRwrt = 1;
            PCwrt = 1;
            clrMRE = 1;
            aluSelA = 0;
            aluSelB = 2'b01;
            aluOp = `ADD;
	    pcCheck=2'b00;
            nxt_state = DECODE;
         end

         DECODE: begin
            Awrt = 1;
            Bwrt = 1;
            case( IR[31:26] )
               6'b000_000:             // R-format
                  case( IR[5:3] )
                     3'b000: begin
			if(IR[2:0]==3'b000) 
				nxt_state = EX_sll;
			else if(IR[2:0]==3'b100)
			        nxt_state = EX_sllv;
			else if(IR[2:0]==3'b010)
			        nxt_state = EX_srl;
			else if(IR[2:0]==3'b110)
			        nxt_state = EX_srlv;
			else if(IR[2:0]==3'b011)
			        nxt_state = EX_sra;
			else if(IR[2:0]==3'b111)
			        nxt_state = EX_srav;
		       end  
                     3'b001: begin
			if(IR[2:0]==3'b000) 
				nxt_state = EX_jr;
			else if(IR[2:0]==3'b001)
			        nxt_state = EX_jalr;
		       end 
                     3'b010:begin
			if(IR[2:0]==3'b000)
				nxt_state =EX_mHI; 
			else if(IR[2:0]==3'b010)
				nxt_state = EX_mLo; 
			end 
                     3'b011: begin
			 if(IR[2:0]==3'b001)
				nxt_state = EX_multu;
			else if(IR[2:0]==3'b010)
				nxt_state = EX_div;
			end
                     3'b100: nxt_state = EX_ALU_R;
                     3'b101: nxt_state = EX_ALU_R;
                     3'b110: ;
                     3'b111: ;
                  endcase

               6'b001_000,             // addi
               6'b001_001,             // addiu
               6'b001_010,             // slti
               6'b001_011,             // sltiu
               6'b001_100,             // andi
               6'b001_101,             // ori
               6'b001_111,             //lui
	       6'b001_110:             // xori
                  nxt_state = EX_ALU_I;

               6'b100_011:
                  nxt_state = EX_LW_1;

               6'b101_011:
                  nxt_state = EX_SW_1;

               6'b000_100,
               6'b000_101:
                  nxt_state = EX_BRA_1;
               6'b000_010:
		  nxt_state = EX_j;
   	       6'b000_011:
		  nxt_state = EX_jal;

               // rest of instructiones should be decoded here

            endcase
         end

         EX_ALU_R: begin
            aluSelA = 1'b1;  
            aluSelB = 2'b00; 
            RegDst = 2'b01;   
            RFwrt = 1'b1; 
	    MemtoReg = 2'b00; 
		case(IR[5:0])
	       6'b100_000: aluOp = `ADD;
	       6'b100_001: aluOp = `ADD;
               6'b100_010: aluOp = `SUB;
               6'b100_011: aluOp = `SUB;
               6'b100_100: aluOp = `AND;
               6'b100_101: aluOp = `OR;
               6'b100_110: aluOp = `XOR;
               6'b100_111: aluOp = `NOR;
               6'b101_010: aluOp = `SLT;
               6'b101_011: aluOp = `SLTU;
               6'b101_111: aluOp = `SLTU;
               endcase
            PrepareFetch;
         end 
         

         EX_ALU_I: begin
            aluSelA = 1'b1;  
            aluSelB = 2'b10; 
            RegDst = 2'b00; 
	    RFwrt = 1'b1;   
            MemtoReg = 2'b00; 
		case(IR[31:26])
	       6'b001_000,
               6'b001_001: begin 
                  SgnExt = 1'b1;
                  aluOp = `ADD;
               end
               6'b001_010: begin 
		  SgnExt = 1'b1;
                  aluOp = `SLT;
               end
               6'b001_011: begin 
                   SgnExt = 1'b0;
		   aluOp = `SLTU;
               end
               6'b001_100: begin  
                   SgnExt = 1'b0;  
		   aluOp = `AND;
               end
               6'b001_101: begin 
		  SgnExt = 1'b0; 
                  aluOp = `OR;
               end
               6'b001_110: begin  
                 SgnExt = 1'b0;
		 aluOp = `XOR;
               end
               6'b001_111: begin  
                  SgnExt = 1'bx;
		  aluOp = `LUI;
               end
            endcase
            PrepareFetch; 
         end
         

         EX_LW_1: begin
           aluSelA=1;
	   aluSelB=2'b10;
	   IorD = 2'b01;
	   aluOp = `ADD;
	   setMRE = 1;
	   SgnExt = 1;
           MARwrt = 1;
           nxt_state = EX_LW_2;
         end

	EX_LW_2:begin
	  nxt_state = EX_LW_3;
	end

	EX_LW_3:begin
	  nxt_state = EX_LW_4;
	end

	EX_LW_4:begin
             MDRwrt = 1;
	     clrMRE = 1;
            nxt_state = EX_LW_5;
	end 

	EX_LW_5: begin 
            RegDst = 2'b00;
	    RFwrt = 1;  
	    MDRwrt = 0;   
            MemtoReg = 2'b01;         
            PrepareFetch; 
         end

         EX_SW_1: begin
            aluSelA = 1'b1;  
            aluSelB = 2'b10;
	    IorD = 2'b01;
	    aluOp = `ADD;
            SgnExt = 1'b1;   
            setMWE = 1'b1;
	    MARwrt = 1'b1;  
	    nxt_state = EX_SW_2;
         end
	 EX_SW_2: begin
            clrMWE = 1'b1;
            nxt_state = EX_SW_3;
         end
        EX_SW_3: begin
            PrepareFetch; 
         end
         EX_BRA_1: begin
            aluSelA = 1'b1;
            aluSelB = 2'b00;
            aluOp = `SUB;
	    if(IR[31:26]==6'b000100 && aluZero)
		nxt_state = EX_BRA_2;
           else if(IR[31:26]==6'b000101 && !aluZero)
		nxt_state = EX_BRA_2;
            else
	        PrepareFetch; 
         end
	EX_BRA_2: begin
            aluSelA = 1'b0;
            aluSelB = 2'b11;
	    IorD = 2'b01;
	    pcCheck=2'b00;
            aluOp = `ADD;
	    SgnExt = 1'b1;
            MARwrt = 1'b1;
	    PCwrt = 1'b1;
	    setMRE = 1'b1;
            nxt_state = FETCH1;
         end

         EX_multu: begin
		multEn=1;
		nxt_state = EX_multu_2;
	end
	EX_multu_2:begin
		if(finEn)begin
		    nxt_state = EX_multu_3;
		end
		else
		   nxt_state = EX_multu_2;
	end
	EX_multu_3:begin
	        PrepareFetch;
	end
        EX_div: begin
		divEn=1;
		nxt_state = EX_div_2;
	end
	EX_div_2:begin
		if(finDivEn)begin
		    nxt_state = EX_div_3;
		end
		else
		   nxt_state = EX_div_2;
	end
	EX_div_3:begin
	        PrepareFetch;
	end
	EX_jr:begin
            PCwrt = 1'b1;
            pcCheck = 2'b11;
	    IorD = 2'b11;   
            setMRE = 1'b1;
	    MARwrt = 1'b1; 
            nxt_state = FETCH1;
	 end
	EX_jalr:begin
            PCwrt = 1'b1; 
            IorD = 2'b11; 
            pcCheck = 2'b11; 
            RegDst = 2'b10;
            MemtoReg = 2'b10;
            RFwrt = 1'b1;
            setMRE = 1'b1;
	    MARwrt = 1'b1; 
            nxt_state = FETCH1;
	end
	EX_mHI:begin 
            mfCheck = 1'b1;
            RegDst = 2'b01;
            MemtoReg = 2'b11;
            RFwrt = 1'b1; 
	    PrepareFetch;
        end
	EX_mLo:begin 
            mfCheck = 1'b0; 
            RegDst = 2'b01;
            MemtoReg = 2'b11;
            RFwrt = 1'b1;
	    PrepareFetch;
         end
        EX_j:begin 
            pcCheck = 2'b01;  
            IorD = 2'b10; 
            PCwrt = 1'b1; 
	    setMRE = 1'b1;
            MARwrt = 1'b1;
            nxt_state = FETCH1;
         end	
	EX_jal:begin 
            MARwrt = 1'b1; 
            pcCheck = 2'b01; 
            IorD = 2'b10; 
            PCwrt = 1'b1; 
 	    setMRE = 1'b1;
            RegDst = 2'b10;
            MemtoReg = 2'b10;
	    RFwrt = 1'b1;
            nxt_state = FETCH1;
          end	
	EX_sll:begin 
	    shiftCheck=3'b000;
	    shiftEn=1;
            shiftreg=IR[10:6]; 
            RegDst = 2'b10;
            MemtoReg = 2'b10;
	    RFwrt = 1'b1;
	   // aluOp = `SLL;
            PrepareFetch;
          end	
	EX_sllv:begin
	    shiftCheck=3'b001; 
	    shiftEn=1;
	   // aluOp = `SLL;
            shiftreg=IR[25:21]; 
            RegDst = 2'b10;
            MemtoReg = 2'b10;
	    RFwrt = 1'b1;
            PrepareFetch;
          end
	EX_srl:begin 
	    shiftCheck=3'b010;
	    shiftEn=1;
	   // aluOp = `SLL;
            shiftreg=IR[10:6]; 
            RegDst = 2'b10;
            MemtoReg = 2'b10;
	    RFwrt = 1'b1;
            PrepareFetch;
          end		
	EX_sra:begin 
	    shiftCheck=3'b011;
	    shiftEn=1;
	   // aluOp = `SLL;
            shiftreg=IR[10:6]; 
            RegDst = 2'b10;
            MemtoReg = 2'b10;
	    RFwrt = 1'b1;
            PrepareFetch;
          end		
	EX_srav:begin 
	    shiftCheck=3'b100;
	    shiftEn=1;
	   // aluOp = `SLL;
            shiftreg=IR[25:21]; 
            RegDst = 2'b10;
            MemtoReg = 2'b10;
	    RFwrt = 1'b1;
            PrepareFetch;
          end		
	EX_srlv:begin 
	    shiftCheck=3'b101;
	    shiftEn=1;
	   // aluOp = `SLL;
            shiftreg=IR[25:21]; 
            RegDst = 2'b10;
            MemtoReg = 2'b10;
	    RFwrt = 1'b1;
            PrepareFetch;
          end	
      endcase

   end
multiplier1 mult(
      .clk( clk ),  
      .start( multEn ),
      .A( A ), 
      .B( B ), 
      .Product( result ),
      .ready( finEn )
   );
 Divide div(  
      .clk( clk ), 
      .start( divEn ),
      .A( A ), 
      .B( B ),  
      .D( D ), 
      .R( R ),  
      .ready( finDivEn )  
       
   ); 
endmodule

//==============================================================================
module multiplier1(
//-----------------------Port directions and deceleration
   input clk,  
   input start,
   input [31:0] A, 
   input [31:0] B, 
   output reg [63:0] Product,
   output ready
    );



//------------------------------------------------------

//----------------------------------- register deceleration
reg [31:0] Multiplicand ;
reg [5:0]  counter;
//-------------------------------------------------------

//------------------------------------- wire deceleration
wire product_write_enable;
wire [32:0] adder_output;
//---------------------------------------------------------

//-------------------------------------- combinational logic
assign adder_output = Multiplicand + Product[63:32];
assign product_write_enable = Product[0];
assign ready = counter[5];
//---------------------------------------------------------

//--------------------------------------- sequential Logic
always @ (posedge clk)

   if(start) begin
       counter <= 6'b000000 ;
      Product <= {32'h00000000, B};
      Multiplicand <= A ;
   end

   else if(! ready) begin
         counter <= counter + 1;
	 Product <= Product >> 1;

      if(product_write_enable)
          Product[63:31] <= adder_output;
   end   

endmodule
//==============================================================================
module Divide(  
   input      clk,    
   input      start,  
   input [31:0]  A,  
   input [31:0]  B,  
   output [31:0]  D,  
   output [31:0]  R,  
   output     ready     
     
   );  
   reg       active;     
   reg [4:0]    cycle;     
   reg [31:0]   result;     
   reg [31:0]   denom;     
   reg [31:0]   work;    
   wire [32:0]   sub = { work[30:0], result[31] } - denom;  
   

   assign D = result;  
   assign R = work;  
   assign ready = ~active;
  
   always @(posedge clk) begin  
      if(start) begin    
       if (active) begin  
           
         if (sub[32] == 0) begin  
           work <= sub[31:0];  
           result <= {result[30:0], 1'b1};  
         end  
         else begin  
           work <= {work[30:0], result[31]};  
           result <= {result[30:0], 1'b0};  
         end  
         if (cycle == 0) begin  
           active <= 0;  
         end  
         cycle <= cycle - 5'd1;  
       end  
       else begin 
         cycle <= 5'd31;  
         result <= A;  
         denom <= B;  
         work <= 32'b0;  
         active <= 1;  
       end  
     end  
   end  
 endmodule  
//==============================================================================
module my_alu(
   input [3:0] Op,
   input [31:0] A,
   input [31:0] B,

   output [31:0] X,
   output        Z
);

   wire sub = Op != `ADD;
   wire shamt=A[4:0];
   wire [31:0] bb = sub ? ~B : B;

   wire [32:0] sum = A + bb + sub;

   wire sltu = ! sum[32];

   wire v = sub ? 
        ( A[31] != B[31] && A[31] != sum[31] )
      : ( A[31] == B[31] && A[31] != sum[31] );

   wire slt = v ^ sum[31];

   reg [31:0] x;

   always @( * )
      case( Op )
         `ADD : x = sum;
         `SUB : x = sum;
         `SLT : x = slt;
         `SLTU: x = sltu;
         `AND : x =   A & B;
         `OR  : x =   A | B;
         `NOR : x = ~(A | B);
         `XOR : x =   A ^ B;
	 `LUI : x = { B[15:0], { 16{1'b0} } };
	 `SLL : x = B>>shamt;
         default : x = 32'hxxxxxxxx;
      endcase

   assign #2 X = x;
   assign #2 Z = x == 32'h00000000;

endmodule

//==============================================================================

module reg_file(
   input clk,
   input write,
   input [4:0] WR,
   input [31:0] WD,
   input [4:0] RR1,
   input [4:0] RR2,
   output [31:0] RD1,
   output [31:0] RD2
);

   reg [31:0] rf_data [0:31];

   assign #2 RD1 = rf_data[ RR1 ];
   assign #2 RD2 = rf_data[ RR2 ];   

   always @( posedge clk ) begin
      if ( write )
         rf_data[ WR ] <= WD;

      rf_data[0] <= 32'h00000000;
   end

endmodule

//==============================================================================
