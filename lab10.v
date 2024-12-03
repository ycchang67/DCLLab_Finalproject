`timescale 1ns / 1ps
//////////////////////////////////////////////////////////////////////////////////
// Company: Dept. of Computer Science, National Chiao Tung University
// Engineer: Chun-Jen Tsai 
// 
// Create Date: 2018/12/11 16:04:41
// Design Name: 
// Module Name: lab9
// Project Name: 
// Target Devices: 
// Tool Versions: 
// Description: A circuit that show the animation of a fish swimming in a seabed
//              scene on a screen through the VGA interface of the Arty I/O card.
// 
// Dependencies: vga_sync, clk_divider, sram 
// 
// Revision:
// Revision 0.01 - File Created
// Additional Comments:
// 
//////////////////////////////////////////////////////////////////////////////////

module lab10(
    input  clk,
    input  reset_n,
    input  [3:0] usr_btn,
    output [3:0] usr_led,
    
    // VGA specific I/O ports
    output VGA_HSYNC,
    output VGA_VSYNC,
    output [3:0] VGA_RED,
    output [3:0] VGA_GREEN,
    output [3:0] VGA_BLUE
    );

// Declare system variables
//reg  [31:0] fish_clock;
//wire [9:0]  pos;
wire 	pokemon1_region;
wire    pokemon1a_region;
wire 	ball_region;

wire frame_sync;
// declare SRAM control signals
wire [17:0] sram_addr;
wire [11:0] data_in;
wire [11:0] data_out;
wire        sram_we, sram_en;

// General VGA control signals
wire vga_clk;         // 50MHz clock for VGA control
wire video_on;        // when video_on is 0, the VGA controller is sending
                      // synchronization signals to the display device.
  
wire pixel_tick;      // when pixel tick is 1, we must update the RGB value
                      // based for the new coordinate (pixel_x, pixel_y)
  
wire [9:0] pixel_x;   // x coordinate of the next pixel (between 0 ~ 639) 
wire [9:0] pixel_y;   // y coordinate of the next pixel (between 0 ~ 479)
  
reg  [11:0] rgb_reg;  // RGB value for the current pixel
reg  [11:0] rgb_next; // RGB value for the next pixel
  
// Application-specific VGA signals
reg  [17:0] pixel_addr;

// Declare the video buffer size
localparam VBUF_W = 320; // video buffer width
localparam VBUF_H = 240; // video buffer height

assign frame_sync = (pixel_y == 524) &&(pixel_x ==799) && pixel_tick;

localparam pokemon1_W   = 64; //width of pokemon 1
localparam pokemon1_H   = 58; //height of pokemon 1
localparam ball_W   = 40; // width of ball
localparam ball_H   = 40; // height of ball

reg [17:0] pokemon_addr[0:9];   // Address array for up to 8 fish images.

// Instiantiate the VGA sync signal generator
vga_sync vs0(
  .clk(vga_clk), .reset_n(reset_n), .oHS(VGA_HSYNC), .oVS(VGA_VSYNC),
  .visible(video_on), .p_tick(pixel_tick),
  .pixel_x(pixel_x), .pixel_y(pixel_y)
);

clk_divider#(2) clk_divider0(
  .clk(clk),
  .reset(~reset_n),
  .clk_out(vga_clk)
);
/////////////////////////////////////////////////////////////////////////////
reg [2:0] STATE;
localparam [2:0] S_MAIN_INIT = 3'b000, S_MAIN_IDLE = 3'b001,
                 S_MAIN_POKE1= 3'b010, S_MAIN_RUN  = 3'b011;
reg  [15:0] faddr; // 64x32x2(page)x2(r/w)

wire [15:0] pokemon1_sram_addr;	
wire [15:0] ball_sram_addr;
reg  [15:0] pokemon1_addr;  
reg  [15:0] pokemon1a_addr; 
reg  [15:0] ball_addr; 

reg  [4:0] poke_load; // 
wire [4:0] poke_we; //
assign poke_we[1] = poke_load[1]& faddr[1];

wire [11:0] pokemon1_out, pokemon2_out, ball_out;
/////////////////////////////////////////////////////////////////////////////
always @(posedge clk  or negedge reset_n) begin
  if (~reset_n) begin
      STATE <= S_MAIN_INIT;
	  poke_load[4:0] <= 5'b00000;
	  faddr <= 0;
  end   
  else begin
	  case (STATE)
		S_MAIN_INIT  : STATE <=S_MAIN_IDLE;
		S_MAIN_IDLE  :	begin
							STATE <=S_MAIN_POKE1;
							poke_load <= 5'b00001;
							faddr <= 0;
						end
		S_MAIN_POKE1 : 	begin // write to sram if necessary, but it seems that we dont need it now...
							if (faddr >= 64*58*6) begin
								STATE <=S_MAIN_RUN;
								poke_load <= 5'b00010;
								faddr <= 0;
							end
							else begin
								STATE <=S_MAIN_POKE1;
								faddr <= faddr +1;
							end
						end
		S_MAIN_RUN   : STATE <=S_MAIN_RUN;
		default: STATE <=S_MAIN_INIT;
	  endcase
	end
end

// ------------------------------------------------------------------------
// The following code describes an initialized SRAM memory block that
// stores a 320x240 12-bit seabed image, plus two 64x32 fish images.
//sram #(.DATA_WIDTH(12), .ADDR_WIDTH(18), .RAM_SIZE(VBUF_W*VBUF_H+FISH_W*FISH_H*2))
//  ram0 (.clk(clk), .we(sram_we), .en(sram_en),
//          .addr(), .data_i(data_in), .data_o(data_out));
reg [6:0] x;
reg [7:0] y;
wire [11:0] data1 = (x==0) ? 12'hFFF : ((y==0 )|| (y==32 )) ? 12'hFFF : 12'h0F0;
always @(posedge clk  or negedge reset_n) begin
  if (~reset_n) begin
	x<=0;
	y<=0;
  end
  else begin
	if (faddr[0] == 1'b1) begin
		x<=x+1;
		if (x==63) begin
			x <=0;
			y <=y+1;
		end
	end
  end
end
//this can copy fish
//sram64x32x2 u_fish1a (.clk(clk), .we(fish_we[0]), .en(sram_en), .addr(fish1a_sram_addr), .data_i(fish1_out), .data_o(fish1a_out));

/////////////////background////////////////
ROM_76800 rom0( // background out
  .clka (clk),
  .ena  (sram_en),
  .wea  (sram_we),
  .addra(sram_addr),
  .dina (data_in),
  .douta(data_out));
ROM_22272 poke1_rom( // don don mouse out
  .clka (clk),
  .ena  (sram_en),
  .wea  (sram_we),
  .addra(pokemon1_sram_addr),
  .dina (data_in),
  .douta(pokemon1_out));   
ROM_1600 ball_rom( // ball out
  .clka (clk),
  .ena  (sram_en),
  .wea  (sram_we),
  .addra(ball_sram_addr),
  .dina (data_in),
  .douta(ball_out)); 


assign sram_we = 0; // In this demo, we do not write the SRAM. However, if
                             // you set 'sram_we' to 0, Vivado fails to synthesize
                             // ram0 as a BRAM -- this is a bug in Vivado.
assign sram_en = 1;          // Here, we always enable the SRAM block.
assign sram_addr = (poke_load[0]) ? VBUF_W*VBUF_H + 18'd0 +faddr[14:1] :
				    pixel_addr;
assign data_in = 12'h000; // SRAM is read-only so we tie inputs to zeros.

assign pokemon1_sram_addr = (STATE ==S_MAIN_RUN) ? (poke1a_region) ? pokemon1a_addr : pokemon1_addr : faddr[15:1]; // copy pokemon1									  
assign ball_sram_addr  = (STATE ==S_MAIN_RUN) ? ball_addry* ball_W + ball_addrx : faddr[15:1];
// End of the SRAM memory block.
// ------------------------------------------------------------------------

// VGA color pixel generator
assign {VGA_RED, VGA_GREEN, VGA_BLUE} = rgb_reg;

// ------------------------------------------------------------------------
// An animation clock for the motion of the fish, upper bits of the
// fish clock is the x position of the fish on the VGA screen.
// Note that the fish will move one screen pixel every 2^20 clock cycles,
// or 10.49 msec

reg  [3:0] pokemon_p;
reg [1:0] one_of_three; // let the don don mouse move to the next photo 1 / 3 frequency

always@(posedge vga_clk or negedge reset_n)begin
	if(~reset_n) begin
		one_of_three <= 0;
	end
	else if (frame_sync) begin // to ensure that no more than six
	   if(one_of_three == 2)begin
			one_of_three <= 0;
	   end
	   else begin
			one_of_three <= one_of_three + 1;
	   end
    end
end

always @(posedge vga_clk  or negedge reset_n) begin
  if (~reset_n) begin
	  pokemon_p<= 0;
  end
  else if (frame_sync && (one_of_three == 2)) begin // to ensure that no more than six
	  pokemon_p <=(pokemon_p >= 5)? 0 : pokemon_p + 1;
  end
end

// ------------------------------------------------------------------------
// ball
reg [9:0] ball_x;  //0~640
reg [9:0] ball_y;	//0~480
wire [9:0] ball_xe;
wire [9:0] ball_ye; 
reg [1:0] ball_dir; //[1] y: 0: To the down, 1: To the up; [0] 0: To the right, 1: To the left
assign ball_xe = ball_x + ball_W - 1;
assign ball_ye = ball_y + ball_H - 1;
wire [5:0] ball_addrx ;   //0~63
wire [5:0] ball_addry ;   //0~63

assign ball_region = (pixel_y >= ball_y) && (pixel_y <= ball_ye) && (pixel_x >= ball_x) && (pixel_x <= ball_xe);

always @(posedge vga_clk  or negedge reset_n) begin
  if (~reset_n) begin
	ball_x <= 320;
	ball_y <= 320;
  end
  else if (frame_sync) begin
	case (ball_dir)
	2'b00:	begin
			if ((ball_xe >= 639) && (ball_ye >= 479)) begin
				ball_dir[1:0] <= 2'b11;
			end
			else if (ball_xe >= 639) begin
				ball_dir[1:0] <= 2'b01;	// y up when reach the region
			end
			else ball_x <= ball_x + 1;
		end
	2'b01:	begin
			if (ball_x <= 310) begin
				ball_dir[1:0] <= 2'b00;	
			end
			else ball_x <= ball_x - 1; 
		end
	2'b10:	begin
			if (ball_xe >= 639) begin
				ball_dir[1:0] <= 2'b11;	
			end
			else ball_x <= ball_x + 1;
		end
	2'b11:	begin
			if ((ball_x == 310) || (ball_y == 0)) begin
				ball_dir[1:0] <= 2'b00;
			end
			else if (ball_x <= 310) begin
				ball_dir[1:0] <= 2'b10;	
			end
			else ball_x <= ball_x - 1;
		end
	endcase
  end		 	
end

assign ball_addrx = (pixel_x - ball_x);
assign ball_addry = (pixel_y - ball_y);

// ------------------------------------------------------------------------
// poke 1
reg [9:0] poke1_x;  //0~640
reg [9:0] poke1_y;	//0~480
wire [9:0] poke1_xe;
wire [9:0] poke1_ye; 
reg [1:0] poke1_dir; //[1] y: 0: To the down, 1: To the up; [0] 0: To the right, 1: To the left
assign poke1_xe = poke1_x + pokemon1_W * 2 - 1;
assign poke1_ye = poke1_y + pokemon1_H * 2 - 1;
wire [5:0] poke1_addrx ;   //0~63
wire [5:0] poke1_addry ;   //0~63

assign poke1_region = (pixel_y >= poke1_y) && (pixel_y <= poke1_ye) && (pixel_x >= poke1_x ) && (pixel_x <= poke1_xe);

always @(posedge vga_clk  or negedge reset_n) begin
  if (~reset_n) begin
	poke1_x <= 320;
	poke1_y <= 320;
	poke1_dir<= 2'b00;
  end
  else if (frame_sync) begin
	case (poke1_dir)
	2'b00:	begin
			if ((poke1_xe >= 639) && (poke1_ye >= 479)) begin
				poke1_dir[1:0] <= 2'b11;
			end
			else if (poke1_xe >= 639) begin
				poke1_dir[1:0] <= 2'b01;	// y up when reach the region
				poke1_y <= poke1_y;
			end
			else poke1_x <= poke1_x + 1;
		end
	2'b01:	begin
			if (poke1_x <= 310) begin
				poke1_dir[1:0] <= 2'b00;	
				poke1_y <= poke1_y;
			end
			else poke1_x <= poke1_x - 1; 
		end
	2'b10:	begin
			if (poke1_xe >= 639) begin
				poke1_dir[1:0] <= 2'b11;	
				poke1_y <= poke1_y;
			end
			else poke1_x <= poke1_x + 1;
		end
	2'b11:	begin
			if ((poke1_x == 310) || (poke1_y == 0)) begin
				poke1_dir[1:0] <= 2'b00;
			end
			else if (poke1_x <= 310) begin
				poke1_dir[1:0] <= 2'b10;	
				poke1_y <= poke1_y;
			end
			else poke1_x <= poke1_x - 1; 
		end
	endcase
  end		 	
end
assign poke1_addrx = (pixel_x - poke1_x) >> 1;
assign poke1_addry = (pixel_y - poke1_y) >> 1;
//---------------------------------------------------------------------------
//change frame
always @(*) begin
	case(pokemon_p[3:1])
	0:	pokemon1_addr <= poke1_addry* pokemon1_W + poke1_addrx;
	1:	pokemon1_addr <= poke1_addry* pokemon1_W + poke1_addrx + pokemon1_W*pokemon1_H;
	2:	pokemon1_addr <= poke1_addry* pokemon1_W + poke1_addrx + pokemon1_W*pokemon1_H*2;
	3:	pokemon1_addr <= poke1_addry* pokemon1_W + poke1_addrx + pokemon1_W*pokemon1_H*3;
	4:	pokemon1_addr <= poke1_addry* pokemon1_W + poke1_addrx + pokemon1_W*pokemon1_H*4;	
	5:	pokemon1_addr <= poke1_addry* pokemon1_W + poke1_addrx + pokemon1_W*pokemon1_H*5;
	endcase

end

// ------------------------------------------------------------------------
// poke 1a
reg [9:0] poke1a_x;  //0~640
reg [9:0] poke1a_y;	//0~480
wire [9:0] poke1a_xe;
wire [9:0] poke1a_ye; 
reg [1:0] poke1a_dir; //[1] y: 0: To the down, 1: To the up; [0] 0: To the right, 1: To the left
assign poke1a_xe = poke1a_x + pokemon1_W*2 - 1;
assign poke1a_ye = poke1a_y + pokemon1_H*2 - 1;
wire [5:0] poke1a_addrx ;   //0~63
wire [5:0] poke1a_addry ;   //0~63

assign poke1a_region = (pixel_y >= poke1a_y) && (pixel_y <= poke1a_ye) && (pixel_x >= poke1a_x ) && (pixel_x <= poke1a_xe); // second don don mouth

// use 2 1 0 button to control the left don don mouse
// 2 : left , 1 : up, 0 : right
// y have to be reduce so don don mouse can jump
reg button_reduce; // use to control reduce
reg button_add; // use to control add
reg button_jump; // use to control jump
reg stop_jump;
reg initial_jump; // to initialize the start speed 12
reg reach_the_ground;
reg [30:0] add_counter;
reg [30:0] red_counter;
reg signed [5:0] jump_speed;

// for jump speed
always @(posedge clk or negedge reset_n) begin
    if(~reset_n)begin
        stop_jump <= 1;
    end
    else begin
        if(button_jump && !reach_the_ground)begin
            stop_jump <= 0;
        end
        else begin
            stop_jump <= 1;
        end
    end
end 
reg start_second; // check if speed is initialize
always @(posedge clk)begin // frame_sync
    if(~reset_n)begin
        initial_jump <= 0;
    end
    else if(button_jump && !initial_jump && !start_second)begin
        initial_jump <= 1;
    end
    else if(initial_jump && start_second)begin
        initial_jump <= 0;
    end
end

always @(posedge clk or negedge reset_n)begin // frame_sync
    if(~reset_n)begin
        start_second <= 0;
    end
    else if(initial_jump)begin
        start_second <= 1;
    end
end

always @(posedge clk or negedge reset_n)begin // check with frame_sync
    if(~reset_n)begin
        jump_speed <= 0;
    end
    else if(initial_jump) begin
        jump_speed <= -12;
    end
    else if(!stop_jump)begin
        jump_speed <= jump_speed + 2;
    end
    else if(reach_the_ground)begin
        jump_speed <= 0;
    end
    
end

// for moving
always @(posedge clk or negedge reset_n) begin
    if(~reset_n)begin
        button_reduce <= 0;
        button_add <= 0;
        button_jump <= 0;
        add_counter <= 0;
        red_counter <= 0;
    end
    else begin
        if(usr_btn[0])begin
            button_add <= 1;
        end
        else begin
            button_add <= 0;
        end
        if(usr_btn[2])begin
            button_reduce <= 1;
        end
        else begin 
            button_reduce <= 0;
        end
        if(usr_btn[1] && jump_speed == 0 && stop_jump)begin
            button_jump <= 1;
        end
        else if(!stop_jump && usr_btn[1])begin
            button_jump <= 1;
        end
        else if(!stop_jump && !usr_btn[1])begin
            button_jump <= button_jump;
        end
        else if(stop_jump) begin
            button_jump <= 0;
        end
    end
end

always @(posedge vga_clk  or negedge reset_n) begin
  if (~reset_n) begin
	poke1a_x <= 0;
	poke1a_y <= 320;
	poke1a_dir<= 2'b00;
	reach_the_ground <= 1;
  end
  else if (frame_sync) begin
	 if (poke1a_xe >= 330) begin
	    poke1a_x <= poke1a_x - button_reduce * 2; 	
		if(poke1a_y >= 320)begin
		   reach_the_ground <= 1;
		   poke1a_y <= 320;
		end
		else begin
		  poke1a_y <= poke1a_y + jump_speed;
		  reach_the_ground <= 0;
		end
	 end
	 else if (poke1a_x <= 0) begin
		if(poke1a_y >= 320)begin
		   reach_the_ground <= 1;
		   poke1a_y <= 320;
		end
		else begin
		  poke1a_y <= poke1a_y + jump_speed;
		  reach_the_ground <= 0;
		end
		poke1a_x <= poke1a_x + button_add * 2;
	 end
	 else begin
	   poke1a_x <= poke1a_x + button_add * 2 - button_reduce * 2;
	    if(poke1a_y >= 320)begin
		   reach_the_ground <= 1;
		   poke1a_y <= 320;
		end
		else begin
		  poke1a_y <= poke1a_y + jump_speed;
		  reach_the_ground <= 0;
		end
	 end
  end		 	
end


assign poke1a_addrx = (pokemon1_W * 2 - 1 - (pixel_x - poke1a_x) >> 1);
assign poke1a_addry = (pixel_y - poke1a_y) >> 1;


always @(*) begin
	case(pokemon_p[3:1])
	0:	pokemon1a_addr <= poke1a_addry* pokemon1_W + poke1a_addrx;
	1:	pokemon1a_addr <= poke1a_addry* pokemon1_W + poke1a_addrx + pokemon1_W*pokemon1_H;
	2:	pokemon1a_addr <= poke1a_addry* pokemon1_W + poke1a_addrx + pokemon1_W*pokemon1_H*2;
	3:	pokemon1a_addr <= poke1a_addry* pokemon1_W + poke1a_addrx + pokemon1_W*pokemon1_H*3;
	4:	pokemon1a_addr <= poke1a_addry* pokemon1_W + poke1a_addrx + pokemon1_W*pokemon1_H*4;	
	5:	pokemon1a_addr <= poke1a_addry* pokemon1_W + poke1a_addrx + pokemon1_W*pokemon1_H*5;
	endcase

end

// ------------------------------------------------------------------------
// Video frame buffer address generation unit (AGU) with scaling control
// Note that the width x height of the fish image is 64x32, when scaled-up
// on the screen, it becomes 128x64. 'pos' specifies the right edge of the
// fish image.
//assign fish1_region =
//           pixel_y >= (FISH_VPOS1<<1) && pixel_y < (FISH_VPOS1+FISH_H)<<1 &&
//           (pixel_x + 127) >= pos && pixel_x < pos + 1;


//wire poke1_region_green = (pokemon1_out==12'h0F0);
wire poke1_region_green = (pokemon1_out[11:8] <= 8 && pokemon1_out[7:4] >= 6 && pokemon1_out[3:0] <= 9); // the first one
//wire poke1a_region_green = (pokemon1_out[11:8] <= 8 && pokemon1_out[7:4] >= 6 && pokemon1_out[3:0] <= 9); // the second one
wire poke1a_region_green = (pokemon1_out[11:8] <= 8 && pokemon1_out[7:4] >= 6 && pokemon1_out[3:0] <= 9);
wire ball_region_green = (ball_out == 12'h0F0);

always @ (posedge clk or negedge reset_n) begin
  if (~reset_n)
    pixel_addr <= 0;

  else 
    // Scale up a 320x240 image for the 640x480 display.
    // (pixel_x, pixel_y) ranges from (0,0) to (639, 479)
    pixel_addr <= (pixel_y >> 1) * VBUF_W + (pixel_x >> 1);

end
// End of the AGU code.
// ------------------------------------------------------------------------
// ------------------------------------------------------------------------
// Send the video data in the sram to the VGA controller

always @(posedge clk) begin
  if (pixel_tick) rgb_reg <= rgb_next;
end

always @(*) begin
  if (~video_on)
    rgb_next = 12'h000; // Synchronization period, must set RGB values to zero.
  else
	if (poke1_region && ~poke1_region_green )
		rgb_next = pokemon1_out;  //poke1
	else if (poke1a_region && ~poke1a_region_green )
		rgb_next = pokemon1_out;
	else if (ball_region && ~ball_region_green )
		rgb_next = ball_out;
	else 
		rgb_next = data_out; // RGB value at (pixel_x, pixel_y)

end
// End of the video data display code.
// ------------------------------------------------------------------------
// ------------------------------------------------------------------------
//btn
wire [3:0] btn_level;
reg [3:0] btn_pressed;
reg  [3:0] prev_btn_level;


debounce btn_db3(
  .clk(clk),
  .btn_input(usr_btn[3]),
  .btn_output(btn_level[3])
);

always @(posedge clk or negedge reset_n) begin
  if (~reset_n)
    prev_btn_level <= 0;
  else
    prev_btn_level <= btn_level;
end

//
//----------------------------------------------------

endmodule
