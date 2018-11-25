
`timescale 1ns/1ps
`define DEL    #1

module RSA_interface(
	input clk,
	input rst_n,
	input [511:0] lcl_dout,
	input lcl_dv,
	input lcl_idone,
	output reg lcl_den,
	output [511:0] lcl_din
);

 wire finish;
 reg [511:0] dataout;
 wire [31:0] data_out;

 assign finish = (cnt==6'd31) ? 1'b1 : 1'b0;

 reg [2:0] cnt_i;
 always@(posedge clk or negedge rst_n)begin
   if(~rst_n)begin
     cnt_i <= 3'd0;
   end
   else begin
     if(cnt_i==3'b110)
          cnt_i <= cnt_i;
     else if(lcl_dv)
       cnt_i <= cnt_i+1'b1; 
     end
 end

 

 reg [511:0] slv_reg0;
 reg [511:0] slv_reg1;
 reg [511:0] slv_reg2;
 reg [511:0] slv_reg3;
 reg [511:0] slv_reg4;
 reg [511:0] slv_reg5; 
 reg dout_en;

 always@(posedge clk or negedge rst_n)begin
   if(~rst_n)begin
     slv_reg0 <= 512'd0;
     slv_reg1 <= 512'd0;
     slv_reg2 <= 512'd0;
     slv_reg3 <= 512'd0;
     slv_reg4 <= 512'd0;
     slv_reg5 <= 512'd0;
   end
   else if(lcl_dv == 1'b1)begin
     case(cnt_i)
       3'd0 : slv_reg0 <= lcl_dout;
       3'd1 : slv_reg1 <= lcl_dout; 
       3'd2 : slv_reg2 <= lcl_dout; 
       3'd3 : slv_reg3 <= lcl_dout; 
       3'd4 : slv_reg4 <= lcl_dout;
       3'd5 : slv_reg5 <= lcl_dout; 
       endcase
   end
   else if(dout_en==1'b1)begin   //data out
     case(cnt)
        6'd0 : slv_reg0[31:0]     <= `DEL data_out;
        6'd1 : slv_reg0[63:32]    <= `DEL data_out;
        6'd2 : slv_reg0[95:64]    <= `DEL data_out;
        6'd3 : slv_reg0[127:96]   <= `DEL data_out;
        6'd4 : slv_reg0[159:128]  <= `DEL data_out;
        6'd5 : slv_reg0[191:160]  <= `DEL data_out;
        6'd6 : slv_reg0[223:192]  <= `DEL data_out;
        6'd7 : slv_reg0[255:224]  <= `DEL data_out;
        6'd8 : slv_reg0[287:256]  <= `DEL data_out;
        6'd9 : slv_reg0[319:288]  <= `DEL data_out;
        6'd10: slv_reg0[351:320]  <= `DEL data_out;
        6'd11: slv_reg0[383:352]  <= `DEL data_out;
        6'd12: slv_reg0[415:384]  <= `DEL data_out;
        6'd13: slv_reg0[447:416]  <= `DEL data_out;
        6'd14: slv_reg0[479:448]  <= `DEL data_out;
        6'd15: slv_reg0[511:480]  <= `DEL data_out;
        6'd16: slv_reg1[31:0]     <= `DEL data_out;
        6'd17: slv_reg1[63:32]    <= `DEL data_out;
        6'd18: slv_reg1[95:64]    <= `DEL data_out;
        6'd19: slv_reg1[127:96]   <= `DEL data_out;
        6'd20: slv_reg1[159:128]  <= `DEL data_out;
        6'd21: slv_reg1[191:160]  <= `DEL data_out;
        6'd22: slv_reg1[223:192]  <= `DEL data_out;
        6'd23: slv_reg1[255:224]  <= `DEL data_out;
        6'd24: slv_reg1[287:256]  <= `DEL data_out;
        6'd25: slv_reg1[319:288]  <= `DEL data_out;
        6'd26: slv_reg1[351:320]  <= `DEL data_out;
        6'd27: slv_reg1[383:352]  <= `DEL data_out;
        6'd28: slv_reg1[415:384]  <= `DEL data_out;
        6'd29: slv_reg1[447:416]  <= `DEL data_out;
        6'd30: slv_reg1[479:448]  <= `DEL data_out;
        6'd31: slv_reg1[511:480]  <= `DEL data_out;
      endcase
    end
 end



  //posedge detect
 reg [1:0] key_rdy_reg;
 reg [1:0] mod_rdy_reg;
 reg [1:0] dat_rdy_reg;
 reg key_rdy;
 reg mod_rdy;
 reg dat_rdy;
 wire [2:0] state; 
 reg [31:0] key_in;
 reg [31:0] mod_in;
 reg [31:0] data_in;
 wire data_out_ready;
 reg [5:0] cnt;

 always@(posedge clk or negedge rst_n)begin
   if(~rst_n)begin
     key_rdy_reg <= 2'b00;
     mod_rdy_reg <= 2'b00;
     dat_rdy_reg <= 2'b00;
   end
   else begin
     key_rdy_reg <= { key_rdy_reg[0], key_rdy };
     mod_rdy_reg <= { mod_rdy_reg[0], mod_rdy };
     dat_rdy_reg <= { dat_rdy_reg[0], dat_rdy };
   end
 end

 wire key_rdy_en;
 wire mod_rdy_en;
 wire dat_rdy_en;
 assign key_rdy_en = (key_rdy_reg == 2'b01); 
 assign mod_rdy_en = (mod_rdy_reg == 2'b01); 
 assign dat_rdy_en = (dat_rdy_reg == 2'b01); 

 wire key_end;
 wire mod_end;
 always@(posedge clk or negedge rst_n)begin
    if(~rst_n)begin
      key_rdy <= 1'b0;
      mod_rdy <= 1'b0;
      dat_rdy <= 1'b0;
    end
    else begin
      if(cnt_i == 3'd1)
         key_rdy <= 1'd1;
      else if(key_end == 1'b1)
        mod_rdy <= 1'd1;
      else if(mod_end == 1'b1)
        dat_rdy <= 1'd1;
    end
  end

   //counter

  always@(posedge clk or negedge rst_n)begin
    if(~rst_n)
      cnt <= `DEL 6'd33;
    else if(key_rdy_en | mod_rdy_en | dat_rdy_en | data_out_ready)
      cnt <= `DEL 6'd0;
    else if(cnt==6'd33)
      cnt <= `DEL cnt;
    else 
      cnt <= `DEL cnt + 1'b1;
  end

  always@(posedge clk or negedge rst_n)begin
    if(~rst_n)
      dout_en <= `DEL 1'b0;
    else if(data_out_ready)
      dout_en <= `DEL 1'b1;
    else if(finish)
      dout_en <= `DEL 1'b0;
  end

  //load key to RSA
 always@(*)begin
   key_in = 32'b0;
   if(state==3'd3)
     case (cnt)
        6'd0 :  key_in = slv_reg0[31:0]   ;
        6'd1 :  key_in = slv_reg0[63:32]  ;
        6'd2 :  key_in = slv_reg0[95:64]  ;
        6'd3 :  key_in = slv_reg0[127:96] ;
        6'd4 :  key_in = slv_reg0[159:128];
        6'd5 :  key_in = slv_reg0[191:160];
        6'd6 :  key_in = slv_reg0[223:192];
        6'd7 :  key_in = slv_reg0[255:224];
        6'd8 :  key_in = slv_reg0[287:256];
        6'd9 :  key_in = slv_reg0[319:288];
        6'd10:  key_in = slv_reg0[351:320];
        6'd11:  key_in = slv_reg0[383:352];
        6'd12:  key_in = slv_reg0[415:384];
        6'd13:  key_in = slv_reg0[447:416];
        6'd14:  key_in = slv_reg0[479:448];
        6'd15:  key_in = slv_reg0[511:480];
        6'd16:  key_in = slv_reg1[31:0]   ;
        6'd17:  key_in = slv_reg1[63:32]  ;
        6'd18:  key_in = slv_reg1[95:64]  ;
        6'd19:  key_in = slv_reg1[127:96] ;
        6'd20:  key_in = slv_reg1[159:128];
        6'd21:  key_in = slv_reg1[191:160];
        6'd22:  key_in = slv_reg1[223:192];
        6'd23:  key_in = slv_reg1[255:224];
        6'd24:  key_in = slv_reg1[287:256];
        6'd25:  key_in = slv_reg1[319:288];
        6'd26:  key_in = slv_reg1[351:320];
        6'd27:  key_in = slv_reg1[383:352];
        6'd28:  key_in = slv_reg1[415:384];
        6'd29:  key_in = slv_reg1[447:416];
        6'd30:  key_in = slv_reg1[479:448];
        6'd31:  key_in = slv_reg1[511:480];
        default:key_in = 32'b0; 
      endcase
  end

  //load mod 
  always@(*)begin
    mod_in = 32'b0;
    if(state==3'd4)
      case (cnt)
        6'd0 :  mod_in = slv_reg2[31:0]   ;
        6'd1 :  mod_in = slv_reg2[63:32]  ;
        6'd2 :  mod_in = slv_reg2[95:64]  ;
        6'd3 :  mod_in = slv_reg2[127:96] ;
        6'd4 :  mod_in = slv_reg2[159:128];
        6'd5 :  mod_in = slv_reg2[191:160];
        6'd6 :  mod_in = slv_reg2[223:192];
        6'd7 :  mod_in = slv_reg2[255:224];
        6'd8 :  mod_in = slv_reg2[287:256];
        6'd9 :  mod_in = slv_reg2[319:288];
        6'd10:  mod_in = slv_reg2[351:320];
        6'd11:  mod_in = slv_reg2[383:352];
        6'd12:  mod_in = slv_reg2[415:384];
        6'd13:  mod_in = slv_reg2[447:416];
        6'd14:  mod_in = slv_reg2[479:448];
        6'd15:  mod_in = slv_reg2[511:480];
        6'd16:  mod_in = slv_reg3[31:0]   ;
        6'd17:  mod_in = slv_reg3[63:32]  ;
        6'd18:  mod_in = slv_reg3[95:64]  ;
        6'd19:  mod_in = slv_reg3[127:96] ;
        6'd20:  mod_in = slv_reg3[159:128];
        6'd21:  mod_in = slv_reg3[191:160];
        6'd22:  mod_in = slv_reg3[223:192];
        6'd23:  mod_in = slv_reg3[255:224];
        6'd24:  mod_in = slv_reg3[287:256];
        6'd25:  mod_in = slv_reg3[319:288];
        6'd26:  mod_in = slv_reg3[351:320];
        6'd27:  mod_in = slv_reg3[383:352];
        6'd28:  mod_in = slv_reg3[415:384];
        6'd29:  mod_in = slv_reg3[447:416];
        6'd30:  mod_in = slv_reg3[479:448];
        6'd31:  mod_in = slv_reg3[511:480];
        default:mod_in = 32'b0; 
      endcase
 end

  //load data
  always@(*)begin
    data_in=32'b0;
    if(state==3'd5)
      case (cnt)
        6'd0 :  data_in = slv_reg4[31:0]   ;
        6'd1 :  data_in = slv_reg4[63:32]  ;
        6'd2 :  data_in = slv_reg4[95:64]  ;
        6'd3 :  data_in = slv_reg4[127:96] ;
        6'd4 :  data_in = slv_reg4[159:128];
        6'd5 :  data_in = slv_reg4[191:160];
        6'd6 :  data_in = slv_reg4[223:192];
        6'd7 :  data_in = slv_reg4[255:224];
        6'd8 :  data_in = slv_reg4[287:256];
        6'd9 :  data_in = slv_reg4[319:288];
        6'd10:  data_in = slv_reg4[351:320];
        6'd11:  data_in = slv_reg4[383:352];
        6'd12:  data_in = slv_reg4[415:384];
        6'd13:  data_in = slv_reg4[447:416];
        6'd14:  data_in = slv_reg4[479:448];
        6'd15:  data_in = slv_reg4[511:480];
        6'd16:  data_in = slv_reg5[31:0]   ;
        6'd17:  data_in = slv_reg5[63:32]  ;
        6'd18:  data_in = slv_reg5[95:64]  ;
        6'd19:  data_in = slv_reg5[127:96] ;
        6'd20:  data_in = slv_reg5[159:128];
        6'd21:  data_in = slv_reg5[191:160];
        6'd22:  data_in = slv_reg5[223:192];
        6'd23:  data_in = slv_reg5[255:224];
        6'd24:  data_in = slv_reg5[287:256];
        6'd25:  data_in = slv_reg5[319:288];
        6'd26:  data_in = slv_reg5[351:320];
        6'd27:  data_in = slv_reg5[383:352];
        6'd28:  data_in = slv_reg5[415:384];
        6'd29:  data_in = slv_reg5[447:416];
        6'd30:  data_in = slv_reg5[479:448];
        6'd31:  data_in = slv_reg5[511:480];
        default:data_in = 32'b0; 
      endcase
 end



 
 reg en;
 always@(posedge clk or negedge rst_n)begin
    if(~rst_n)
      en <= 1'b0;
    else if(dout_en == 1'b1 && cnt == 6'd31)
        en <= 1'b1;
    else if(lcl_idone)
        en<= 1'd0;
 end

 reg [1:0] cnt_o;
 always@(posedge clk or negedge rst_n)begin
    if(~rst_n)
      cnt_o <= 2'b00;
    else if(cnt_o == 2'b10)
      cnt_o <= cnt_o;
    else if(en == 1'b1)
      cnt_o <= cnt_o + 1'b1;
  end
		
  always@(posedge clk or negedge rst_n)begin
    if(~rst_n)begin
      dataout <= 512'b0;
      lcl_den <= 1'b0;
    end
    else if(lcl_idone)begin
        lcl_den<= 1'd0;
        dataout <= 512'd0;
    end
    else if(en == 1'b1)begin
      case(cnt_o)
        2'd0 : begin dataout <= slv_reg0; lcl_den<=1'b1; end
        2'd1 : dataout <= slv_reg1; 
        default :dataout <= 512'd0;
      endcase
    end
  end

  assign lcl_din = dataout;

     RSA my_RSA (
    // Outputs
    .data_out       (data_out),
    .finish         ( ),
    .data_out_ready (data_out_ready),
    .mod_end        (mod_end),
    .key_end        (key_end),
    .state          (state),
    // Inputs
    .CLK            (clk),
    .enable         (1'b1),
    .resetn         (rst_n),
    .data_ready     (dat_rdy_en),
    .mod_ready      (mod_rdy_en),
    .key_ready      (key_rdy_en),
    .key_in         (key_in),
    .mod_in         (mod_in),
    .data_in        (data_in));
 

 endmodule

