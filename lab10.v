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
wire 	fish1a_region;
wire 	fish2a_region;
wire 	fish3a_region;
wire    fish1_region;
wire    fish2_region;
wire    fish3_region;

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
// Set parameters for the fish images
localparam FISH_VPOS1   = 64; // Vertical location of the fish in the sea image.
localparam FISH_VPOS2   = 128; // Vertical location of the fish in the sea image.
localparam FISH_VPOS5   = 2; // Vertical location of the fish in the sea image.
localparam FISH_W      = 64; // Width of the fish.
localparam FISH_H      = 32; // Height of the fish.
localparam FISH2_W      = 64; // Width of the fish.
localparam FISH2_H      = 44; // Height of the fish.
localparam FISH3_W      = 40; // Width of the fish.
localparam FISH3_H      = 45; // Height of the fish.
localparam BOAT_W      = 75; // Width of the fish.
localparam BOAT_H      = 27; // Height of the fish.
//localparam FISH4_W      = 32; // Width of the fish.
//localparam FISH4_H      = 16; // Height of the fish.
reg [17:0] fish_addr[0:9];   // Address array for up to 8 fish images.

// Initializes the fish images starting addresses.
// Note: System Verilog has an easier way to initialize an array,
//       but we are using Verilog 2001 :(
initial begin
  fish_addr[0] = VBUF_W*VBUF_H + 18'd0;         /* Addr for fish1 image #1 */
  fish_addr[1] = VBUF_W*VBUF_H + FISH_W*FISH_H  ; /* Addr for fish1 image #2 */
  fish_addr[2] = VBUF_W*VBUF_H + FISH_W*FISH_H*2;         /* Addr for fish2 image #1 */
  fish_addr[3] = VBUF_W*VBUF_H + FISH_W*FISH_H*3; /* Addr for fish2 image #2 */
  fish_addr[4] = VBUF_W*VBUF_H + FISH_W*FISH_H*4;         /* Addr for fish3 image #1 */
  fish_addr[5] = VBUF_W*VBUF_H + FISH_W*FISH_H*5; /* Addr for fish3 image #2 */
  fish_addr[6] = VBUF_W*VBUF_H + FISH_W*FISH_H*6;         /* Addr for fish4 image #1 */
  fish_addr[7] = VBUF_W*VBUF_H + FISH_W*FISH_H*7; /* Addr for fish4 image #2 */
end

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
                 S_MAIN_FISH1= 3'b010, S_MAIN_FISH2= 3'b011,
                 S_MAIN_FISH3= 3'b100, S_MAIN_FISH4= 3'b101,
                 S_MAIN_FISH5= 3'b110, S_MAIN_RUN  = 3'b111;
reg  [15:0] faddr; // 64x32x2(page)x2(r/w)

wire [15:0] fish_sram_addr;	//64x100x8
wire [15:0] fish1a_sram_addr;	//64x100x8
wire [15:0] fish2a_sram_addr;	//64x100x8
wire [15:0] fish3a_sram_addr;	//64x100x8
wire [15:0] fish1_sram_addr;	//64x100x8
wire [15:0] fish2_sram_addr;	//64x100x8
wire [15:0] fish3_sram_addr;	//64x100x8
wire [15:0] boat_sram_addr;
reg  [15:0] fish1a_addr;   	//64x100x8
reg  [15:0] fish2a_addr;   	//64x100x8
reg  [15:0] fish3a_addr;   	//64x100x8
reg  [15:0] fish1_addr;   	//64x100x8
reg  [15:0] fish2_addr;   	//64x100x8
reg  [15:0] fish3_addr;   	//64x100x8
reg  [15:0] fish4_addr;   	//64x100x8
reg  [15:0] boat_addr;
reg  [4:0] fish_load; // 
wire [4:0] fish_we; //
assign fish_we[0] = fish_load[0]& faddr[0];
assign fish_we[1] = fish_load[1]& faddr[0];
assign fish_we[2] = fish_load[2]& faddr[0];
assign fish_we[3] = fish_load[3]& faddr[0];
assign fish_we[4] = fish_load[4]& faddr[0];
wire [11:0] fish1a_out, fish2a_out, fish3a_out,fish1_out, fish2_out, fish3_out, boat_out;
/////////////////////////////////////////////////////////////////////////////
always @(posedge clk  or negedge reset_n) begin
  if (~reset_n) begin
      STATE <= S_MAIN_INIT;
	  fish_load[4:0] <= 5'b00000;
	  faddr <= 0;
	  faddr <= 0;
  end   
  else begin
	  case (STATE)
		S_MAIN_INIT  : STATE <=S_MAIN_IDLE;
		S_MAIN_IDLE  :	begin
							STATE <=S_MAIN_FISH1;
							fish_load <= 5'b00001;
							faddr <= 0;
						end
		S_MAIN_FISH1 : 	begin // write to sram if necessary
							if (faddr >= 64*2*32*2) begin
								STATE <=S_MAIN_FISH2;
								fish_load <= 5'b00010;
								faddr <= 0;
							end
							else begin
								STATE <=S_MAIN_FISH1;
								faddr <= faddr +1;
							end
						end
		S_MAIN_FISH2 : 	begin
							if (faddr>= 64*2*44*2 ) begin
								STATE <=S_MAIN_FISH3;
								fish_load <= 5'b00100;
								faddr <= 0;
								
							end
							else begin
								STATE <=S_MAIN_FISH2;
								faddr <= faddr +1;
							end
						end
		S_MAIN_FISH3 : 	begin
							if (faddr>= 40*2*45*2) begin
								STATE <=S_MAIN_RUN;
								fish_load <= 5'b01000;
								faddr <= 0;
							end
							else begin
								STATE <=S_MAIN_FISH3;
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
ROM_76800 rom0(
  .clka (clk),
  .ena  (sram_en),
  .wea  (sram_we),
  .addra(sram_addr),
  .dina (data_in),
  .douta(data_out));
ROM_16384 fish1_rom(
  .clka (clk),
  .ena  (sram_en),
  .wea  (sram_we),
  .addra(fish1_sram_addr),
  .dina (data_in),
  .douta(fish1_out));   


assign sram_we = 0; // In this demo, we do not write the SRAM. However, if
                             // you set 'sram_we' to 0, Vivado fails to synthesize
                             // ram0 as a BRAM -- this is a bug in Vivado.
assign sram_en = 1;          // Here, we always enable the SRAM block.
assign sram_addr = (fish_load[0]) ? VBUF_W*VBUF_H + 18'd0 +faddr[14:1] :
				    pixel_addr;
assign data_in = 12'h000; // SRAM is read-only so we tie inputs to zeros.

assign fish1a_sram_addr  = (STATE ==S_MAIN_RUN) ? fish1a_addr : faddr[15:1];
assign fish2a_sram_addr  = (STATE ==S_MAIN_RUN) ? fish2a_addr : faddr[15:1];
assign fish3a_sram_addr  = (STATE ==S_MAIN_RUN) ? fish3a_addr : faddr[15:1];
assign fish1_sram_addr   = (STATE ==S_MAIN_RUN) ? fish1_addr : faddr[15:1];
//assign fish2_sram_addr   = (STATE ==S_MAIN_RUN) ? fish2_addr : faddr[15:1];
assign fish2_sram_addr   = (STATE ==S_MAIN_RUN) ? (fish2a_region) ? fish2a_addr : fish2_addr : faddr[15:1]; //copy fish2
//assign fish3_sram_addr   = (STATE ==S_MAIN_RUN) ? fish3_addr : faddr[15:1];	
assign fish3_sram_addr   = (STATE ==S_MAIN_RUN) ? fish3_addr : faddr[15:1];		
assign boat_sram_addr         = (STATE ==S_MAIN_RUN) ? boat_addry* BOAT_W + boat_addrx : faddr[15:1];								  
// End of the SRAM memory block.
// ------------------------------------------------------------------------

// VGA color pixel generator
assign {VGA_RED, VGA_GREEN, VGA_BLUE} = rgb_reg;

// ------------------------------------------------------------------------
// An animation clock for the motion of the fish, upper bits of the
// fish clock is the x position of the fish on the VGA screen.
// Note that the fish will move one screen pixel every 2^20 clock cycles,
// or 10.49 msec

reg  [3:0] fish_p;
always @(posedge vga_clk  or negedge reset_n) begin
  if (~reset_n) begin

	  fish_p<= 0;
  end
  else if (frame_sync) begin
	  fish_p <= fish_p+1;
  end
end

// ------------------------------------------------------------------------
// fish 1
reg [9:0] fish1_x;  //0~640
reg [9:0] fish1_y;	//0~480
wire [9:0] fish1_xe;
wire [9:0] fish1_ye; 
reg [1:0] fish1_dir; //[1] y: 0: To the down, 1: To the up; [0] 0: To the right, 1: To the left
assign fish1_xe = fish1_x + FISH_W;
assign fish1_ye = fish1_y + FISH_H -1;
wire [5:0] fish1_addrx ;   //0~63
wire [6:0] fish1_addry ;   //0~99

// fish1
assign fish1_region = (pixel_y >= fish1_y) && (pixel_y <= fish1_ye) && (pixel_x >= fish1_x) && (pixel_x <= fish1_xe);

always @(posedge vga_clk  or negedge reset_n) begin
  if (~reset_n) begin
	fish1_x <= 0;
	fish1_y <= 200;
	fish1_dir<= 2'b00;
  end
  else if (frame_sync && get_fish[0]) fish1_y <= (fish1_y >= 32)  ? fish1_y -32 : 0;
  else if (frame_sync) begin
	case (fish1_dir)
	2'b00:	begin
			if ((fish1_xe >= 639) && (fish1_ye >= 479)) begin
				fish1_dir[1:0] <= 2'b11;
			end
			else if (fish1_xe >= 639) begin
				fish1_dir[1:0] <= 2'b01;	
				fish1_y <= fish1_y+1;
			end
			else fish1_x <= fish1_x+fish1_speed;
		end
	2'b01:	begin
			if (fish1_x <= fish1_speed) begin
				fish1_dir[1:0] <= 2'b00;	
				fish1_y <= fish1_y+1;
			end
			else fish1_x <= fish1_x - fish1_speed; 
		end
	2'b10:	begin
			if (fish1_xe >= 639) begin
				fish1_dir[1:0] <= 2'b11;	
				fish1_y <= fish1_y-1;
			end
			else fish1_x <= fish1_x+fish1_speed;
		end
	2'b11:	begin
			if ((fish1_x == 0) || (fish1_y == 0)) begin
				fish1_dir[1:0] <= 2'b00;
			end
			else if (fish1_x <= fish1_speed) begin
				fish1_dir[1:0] <= 2'b10;	
				fish1_y <= fish1_y-1;
			end
			else fish1_x <= fish1_x - fish1_speed; 
		end
	endcase
  end		 	
end
assign fish1_addrx = fish1_dir[0] ? FISH_W - 1 - (pixel_x - fish1_x) : (pixel_x - fish1_x);
assign fish1_addry = (pixel_y - fish1_y);

always @(*) begin
	case(fish_p[3:1])
	0:	fish1_addr <= fish1_addry* FISH_W + fish1_addrx;
	1:	fish1_addr <= fish1_addry* FISH_W + fish1_addrx + FISH_W*FISH_H;
	2:	fish1_addr <= fish1_addry* FISH_W + fish1_addrx + FISH_W*FISH_H*2;
	3:	fish1_addr <= fish1_addry* FISH_W + fish1_addrx + FISH_W*FISH_H*3;
	4:	fish1_addr <= fish1_addry* FISH_W + fish1_addrx + FISH_W*FISH_H*4;	
	5:	fish1_addr <= fish1_addry* FISH_W + fish1_addrx + FISH_W*FISH_H*5;
	6:	fish1_addr <= fish1_addry* FISH_W + fish1_addrx + FISH_W*FISH_H*6;
	7:	fish1_addr <= fish1_addry* FISH_W + fish1_addrx + FISH_W*FISH_H*7;
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


wire fish1_region_green = (fish1_out==12'h0F0);

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
	if (fish1_region && ~fish1_region_green )
		rgb_next = fish1_out;  //fish1

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

debounce btn_db0(
  .clk(clk),
  .btn_input(usr_btn[0]),
  .btn_output(btn_level[0])
);
debounce btn_db1(
  .clk(clk),
  .btn_input(usr_btn[1]),
  .btn_output(btn_level[1])
);
debounce btn_db2(
  .clk(clk),
  .btn_input(usr_btn[2]),
  .btn_output(btn_level[2])
);
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


always @(posedge clk or negedge reset_n) begin
    if(!reset_n) fish2_speed_level <= 0;
	else if (btn_pressed[0]) fish1_speed_level <= (fish1_speed_level == 4 ) ? 0 : fish1_speed_level +1;
    else if (btn_pressed[1]) fish2_speed_level <= (fish2_speed_level == 4 ) ? 0 : fish2_speed_level +1;
	else if (btn_pressed[2]) fish3_speed_level <= (fish3_speed_level == 4 ) ? 0 : fish3_speed_level +1;
end

//
//----------------------------------------------------

endmodule
