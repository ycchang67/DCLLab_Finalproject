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
    output [3:0] VGA_BLUE,

	input  uart_rx,
    output uart_tx
    );

// Declare system variables

wire 	poke1_region;
wire  poke1a_region;
wire meet1; // for meet with ball_region and poke1_region
wire meet1a; // for meet with ball_region and poke1a_region
wire 	ball_region;
wire 	number1_region;
wire 	number2_region;
wire prompt_region;

// e means right or down edge
assign meet1a_up = (poke1a_region && ball_region ) && (ball_ye <= poke1a_y + 1); // small means up, big means down. // has problem
assign meet1a_down = (poke1a_region && ball_region ) && (ball_y >= poke1a_ye - 1); // ball's up larger than pokemon's down
assign meet1a_right = (poke1a_region && ball_region ) && (ball_ye > poke1a_y) && (ball_y <= poke1a_ye) && (ball_x <= poke1a_xe) && (ball_xe > poke1a_xe);
assign meet1a_left = (poke1a_region && ball_region )  && (ball_ye > poke1a_y) && (ball_y <= poke1a_ye) && (ball_xe >= poke1a_x) && (ball_x < poke1a_x);



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
localparam number_W   = 36;  // width of number
localparam number_H   = 50;  // height of number
localparam prompt_W   = 100;  // width of number
localparam prompt_H   = 14;  // height of number

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
				 S_MAIN_START = 3'b010, S_MAIN_RUN  = 3'b011,
				 S_MAIN_END = 3'b100;
reg  [15:0] faddr; // 64x32x2(page)x2(r/w)

wire [15:0] pokemon1_sram_addr;	
wire [15:0] ball_sram_addr;
wire [15:0] number_sram_addr;
wire [15:0] prompt_sram_addr;
reg  [15:0] pokemon1_addr;  
reg  [15:0] pokemon1a_addr; 
reg  [15:0] ball_addr; 
reg  [15:0] number1_addr; 
reg  [15:0] number2_addr;
reg  [15:0] prompt_addr;

reg  [4:0] poke_load; // 
wire [4:0] poke_we; //
assign poke_we[1] = poke_load[1]& faddr[1];

wire [11:0] pokemon1_out, pokemon2_out, ball_out, number_out, prompt_out;
//------------------------------------------------------------------------------
//UART control
localparam [1:0] S_MAIN_INITUART = 0, S_MAIN_PROMPT = 1,
                 S_MAIN_READ_INPUT = 2;
localparam [1:0] S_UART_IDLE = 0, S_UART_WAIT = 1,
                 S_UART_SEND = 2, S_UART_INCR = 3;
localparam INIT_DELAY = 100_000; // 1 msec @ 100 MHz
localparam PROMPT_STR = 0;  // starting index of the prompt message
localparam PROMPT_LEN = 29; // length of the prompt message

localparam MEM_SIZE   = PROMPT_LEN;

// declare system variables
wire print_enable, print_done;
reg [$clog2(MEM_SIZE):0] send_counter;
reg [1:0] P, P_next;
reg [1:0] Q, Q_next;
reg [$clog2(INIT_DELAY):0] init_counter;
reg [7:0] data[0:MEM_SIZE-1];
reg  [0:PROMPT_LEN*8-1] msg1 = { "\015\012USE WAD to control poke1: ", 8'h00 };
reg  [31:0] data_reg;  // The key-in number register

// declare UART signals
wire transmit;
wire received;
wire [7:0] rx_byte;
reg  [7:0] rx_temp;  // if recevied is true, rx_temp latches rx_byte for ONLY ONE CLOCK CYCLE!
wire [7:0] tx_byte;
wire [7:0] echo_key; // keystrokes to be echoed to the terminal
wire valid_input;
wire is_receiving;
wire is_transmitting;
wire recv_error;

/* The UART device takes a 100MHz clock to handle I/O at 9600 baudrate */
uart uart(
  .clk(clk),
  .rst(~reset_n),
  .rx(uart_rx),
  .tx(uart_tx),
  .transmit(transmit),
  .tx_byte(tx_byte),
  .received(received),
  .rx_byte(rx_byte),
  .is_receiving(is_receiving),
  .is_transmitting(is_transmitting),
  .recv_error(recv_error)
);

// Initializes some strings.
// System Verilog has an easier way to initialize an array,
// but we are using Verilog 2001 :(
//
integer idx;

always @(posedge clk) begin
  if (~reset_n) begin
    for (idx = 0; idx < PROMPT_LEN; idx = idx + 1) data[idx] = msg1[idx*8 +: 8];
  end
end

// ------------------------------------------------------------------------
// Main FSM that reads the UART input and triggers
// the output of the string "Hello, World!".
always @(posedge clk) begin
  if (~reset_n) P <= S_MAIN_INITUART;
  else P <= P_next;
end

always @(*) begin // FSM next-state logic
  case (P)
    S_MAIN_INITUART: // Wait for initial delay of the circuit.
	   if (init_counter < INIT_DELAY) P_next = S_MAIN_INITUART;
		else P_next = S_MAIN_PROMPT;
    S_MAIN_PROMPT: // Print the prompt message.
      if (print_done) P_next = S_MAIN_READ_INPUT;
      else P_next = S_MAIN_PROMPT;
    S_MAIN_READ_INPUT: //read input
		P_next = S_MAIN_READ_INPUT;
  endcase
end

// FSM output logics: print string control signals.
assign print_enable = (P != S_MAIN_PROMPT && P_next == S_MAIN_PROMPT) ||
                  (P != S_MAIN_READ_INPUT && P_next == S_MAIN_READ_INPUT);
assign print_done = (tx_byte == 8'h0);

// Initialization counter.
always @(posedge clk) begin
  if (P == S_MAIN_INITUART) init_counter <= init_counter + 1;
  else init_counter <= 0;
end
// End of the FSM of the print string controller
// ------------------------------------------------------------------------

// ------------------------------------------------------------------------
// FSM of the controller that sends a string to the UART.
always @(posedge clk) begin
  if (~reset_n) Q <= S_UART_IDLE;
  else Q <= Q_next;
end

always @(*) begin // FSM next-state logic
  case (Q)
    S_UART_IDLE: // wait for the print_string flag
      if (print_enable) Q_next = S_UART_WAIT;
      else Q_next = S_UART_IDLE;
    S_UART_WAIT: // wait for the transmission of current data byte begins
      if (is_transmitting == 1) Q_next = S_UART_SEND;
      else Q_next = S_UART_WAIT;
    S_UART_SEND: // wait for the transmission of current data byte finishes
      if (is_transmitting == 0) Q_next = S_UART_INCR; // transmit next character
      else Q_next = S_UART_SEND;
    S_UART_INCR:
      if (tx_byte == 8'h0) Q_next = S_UART_IDLE; // string transmission ends
      else Q_next = S_UART_WAIT;
  endcase
end

// FSM output logics: UART transmission control signals
assign transmit = (Q_next == S_UART_WAIT ||
                  (P == S_MAIN_READ_INPUT && received) ||
                   print_enable);
assign valid_input = (rx_byte == 8'h61) || (rx_byte == 8'h64) || (rx_byte == 8'h77);
assign echo_key = (valid_input || rx_byte == 8'h0D)? rx_byte : 0;
assign tx_byte  = ((P == S_MAIN_READ_INPUT) && received)? echo_key : data[send_counter];

// UART send_counter control circuit
always @(posedge clk) begin
  case (P_next)
    S_MAIN_INITUART: send_counter <= PROMPT_STR;
    default: send_counter <= send_counter + (Q_next == S_UART_INCR);
  endcase
end
// End of the FSM of the print string controller
// ------------------------------------------------------------------------

// ------------------------------------------------------------------------
// UART input logic
reg input_a;
reg input_d;
reg input_w;

reg checking; // for checking
reg checking2;
assign usr_led[3] = poke1a_region && ball_region ;
assign usr_led[2] =  checking;
assign usr_led[1] =  meet1a_left;
assign usr_led[0] =  checking2; // this is correct
always @(posedge clk or negedge reset_n)begin
  if (~reset_n) begin 
	  checking <= 0;
    checking2 <= 0;
  end
  else if(meet1a_up)begin
    checking <= 1;
  end
  else if(meet1a_down) checking2 <= 1;
  else begin
    checking <= checking;
    checking2 <= checking2;
  end
end



always @(posedge clk or negedge reset_n)begin
  if (~reset_n) begin 
	input_a <= 0;
	input_d <= 0;
	input_w <= 0;
  end
  else if (input_a && button1_reduce)begin
		input_a <= 0;
  end
  else if (input_d && button1_add)begin
		input_d <= 0;
  end
  else if (input_w && start1_jump)begin
		input_w <= 0;
  end
  else if (P == S_MAIN_INITUART || P == S_MAIN_PROMPT) begin
	input_a <= 0;
	input_d <= 0;
	input_w <= 0;
  end

  else if (is_receiving && valid_input) begin
	if(rx_byte == 8'h61)begin
		input_a <= 1;
	end
	else if(rx_byte == 8'h64)begin
		input_d <= 1;
	end
	else if(rx_byte == 8'h77)begin
		input_w <= 1;
	end
  end


end


// The following logic stores the UART input in a temporary buffer.
// The input character will stay in the buffer for one clock cycle.
always @(posedge clk) begin
  rx_temp <= (received)? rx_byte : 8'h0;
end
// End of the UART input logic
// ------------------------------------------------------------------------

/////////////////////////////////////////////////////////////////////////////
always @(posedge clk  or negedge reset_n) begin
  if (~reset_n) begin
      STATE <= S_MAIN_INIT;
	  poke_load[4:0] <= 5'b00000;
	  faddr <= 0;
  end   
  else begin
	  case (STATE)
		S_MAIN_INIT  : STATE <= S_MAIN_IDLE;
		S_MAIN_IDLE  :	begin
							STATE <= S_MAIN_START;
							poke_load <= 5'b00001;
							faddr <= 0;
						end
		S_MAIN_START : begin
			if(score1 > 0 || score2 > 0) STATE <= S_MAIN_RUN;
			else if(btn_pressed[3])begin
				STATE <= S_MAIN_RUN;
			end
			else STATE <= S_MAIN_START;
		end
		S_MAIN_RUN : begin
			if(ball_in1 || ball_in2) begin
				STATE <= S_MAIN_START;
			end
			else if ((score1 == 7) || (score2 == 7))begin
				STATE <= S_MAIN_END;
			end
			else STATE <= S_MAIN_RUN;
		end
		S_MAIN_END : begin	
			STATE <= S_MAIN_END;
		end
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

//-------------------------------------------------------------
//ROM
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
ROM_14400 num_rom( // num out
  .clka (clk),
  .ena  (sram_en),
  .wea  (sram_we),
  .addra(number_sram_addr),
  .dina (data_in),
  .douta(number_out)); 
ROM_2800 prompt_rom( // prompt out
  .clka (clk),
  .ena  (sram_en),
  .wea  (sram_we),
  .addra(prompt_sram_addr),
  .dina (data_in),
  .douta(prompt_out)); 

assign sram_we = 0; // In this demo, we do not write the SRAM. However, if
                             // you set 'sram_we' to 0, Vivado fails to synthesize
                             // ram0 as a BRAM -- this is a bug in Vivado.
assign sram_en = 1;          // Here, we always enable the SRAM block.
assign sram_addr = (STATE == S_MAIN_START || STATE == S_MAIN_RUN || STATE == S_MAIN_END) ? pixel_addr : faddr[15:1];
assign data_in = 12'h000; // SRAM is read-only so we tie inputs to zeros.

assign pokemon1_sram_addr = (STATE == S_MAIN_START || STATE == S_MAIN_RUN || STATE == S_MAIN_END)  ? (poke1a_region) ? pokemon1a_addr : pokemon1_addr : faddr[15:1]; // copy pokemon1									  
assign ball_sram_addr  = (STATE == S_MAIN_START || STATE == S_MAIN_RUN || STATE == S_MAIN_END)  ? ball_addry* ball_W + ball_addrx : faddr[15:1];
assign number_sram_addr  = (STATE ==S_MAIN_RUN || STATE == S_MAIN_END) ? (number1_region) ? number1_addr : number2_addr : faddr[15:1];
assign prompt_sram_addr = (STATE == S_MAIN_START || STATE == S_MAIN_END) ? prompt_addr : faddr[15:1];
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
// prompt
reg [9:0] prompt_x;  //0~640
reg [9:0] prompt_y;	//0~480
wire [9:0] prompt_xe; // left of ball x
wire [9:0] prompt_ye;  // buttom of ball y 
assign prompt_xe = prompt_x + prompt_W * 2 - 1;
assign prompt_ye = prompt_y + prompt_H * 2 - 1; 
wire [9:0] prompt_addrx ;   //0~63
wire [9:0] prompt_addry ;   //0~63

assign prompt_region = (pixel_y >= prompt_y) && (pixel_y <= prompt_ye) && (pixel_x >= prompt_x) && (pixel_x <= prompt_xe);

assign prompt_addrx = (pixel_x - prompt_x) >> 1;
assign propmt_addry = (pixel_y - prompt_y) >> 1;

always @(posedge vga_clk or negedge reset_n) begin
    if(~reset_n)begin
        prompt_x <= 120;
        prompt_y <= 226;
    end
    else if (frame_sync) begin
		if(STATE == S_MAIN_START)begin
			prompt_x <= 120;
        	prompt_y <= 226;
		end
		else if(STATE == S_MAIN_END)begin
			prompt_x <= 120;
        	prompt_y <= 226;
		end
    end
end

always @(*) begin
	if(STATE == S_MAIN_START)begin
		prompt_addr <= prompt_addry* prompt_W + prompt_addrx;
		end
	else if(STATE == S_MAIN_END)begin
		prompt_addr <= prompt_addry* prompt_W + prompt_addrx + prompt_W*prompt_H;
	end
end



// ------------------------------------------------------------------------
// ball
reg [9:0] ball_x;  //0~640
reg [9:0] ball_y;	//0~480
wire [9:0] ball_xe; // left of ball x
wire [9:0] ball_ye;  // buttom of ball y 
reg [2:0] ball_dir; //[1] y: 0: To the down, 1: To the up; [0] 0: To the right, 1: To the left
assign ball_xe = ball_x + ball_W - 1;
assign ball_ye = ball_y + ball_H - 1; 
wire [5:0] ball_addrx ;   //0~63
wire [5:0] ball_addry ;   //0~63

reg ball_in1;
reg ball_in2;

reg [9:0] ball_Sx;  //delta x of ball // speedx
reg [9:0] ball_Sy;	//delta y of ball // speedy

assign ball_region = (pixel_y >= ball_y) && (pixel_y <= ball_ye) && (pixel_x >= ball_x) && (pixel_x <= ball_xe);

always @(posedge vga_clk or negedge reset_n) begin
    if(~reset_n)begin
        ball_Sx <= 0;
        ball_Sy <= 0;
    end
    else begin
        ball_Sx <= 2;
        ball_Sy <= 2;
    end
end



// if reach the head , just send the ball to the opponent
/*
assign meet1a_up = (poke1a_region && ball_region ) && (ball_ye < poke1a_y); // small means up, big means down.
assign meet1a_down = (poke1a_region && ball_region ) && (ball_y > poke1a_ye); // ball's up larger than pokemon's down
assign meet1a_right = (poke1a_region && ball_region ) && (ball_ye >= poke1a_y ) && (ball_y <= poke1a_ye) && (ball_x <= poke1a_xe) && (ball_xe > poke1a_xe);
assign meet1a_left = (poke1a_region && ball_region )  && (ball_ye >= poke1a_y ) && (ball_y <= poke1a_ye) && (ball_xe >= poke1a_x) && (ball_x < poke1a_x);
*/
always @(posedge vga_clk  or negedge reset_n) begin
  if (~reset_n) begin
	ball_x <= 60;
	ball_y <= 158;
	ball_dir <= 3'b000;
  end
  else if (frame_sync) begin // ball_ye have to <= 378, or bounce
	case (ball_dir)
	3'b000:	begin // ball in left region , going left,and going on , note that if ball_ye >= 190, just turn back, if < 190, x can keep going
	        if(ball_x > 2) begin // haven't reach the left limit
            if(meet1a_up) begin // if meet up
              ball_x <= ball_x + ball_Sx;
              ball_y <= ball_y + ball_Sy;
              ball_dir <= 3'b001;
            end
            else if(meet1a_down)begin
              ball_x <= ball_x - ball_Sx;
              ball_y <= ball_y + ball_Sy;
              ball_dir <= 3'b010;
            end
            else if(meet1a_right) begin
              ball_x <= ball_x + ball_Sx;
              ball_y <= ball_y + ball_Sy;
              ball_dir <= 3'b001;
            end
            else if(meet1a_left)begin
              if(ball_x - 2* ball_Sx > 0)begin
                ball_x <= ball_x - 2 * ball_Sx; // be careful of this , may cause some problem, like the bound of ball_x
              end
              else begin
                ball_x <= ball_x - ball_Sx;
              end
              ball_y <= ball_y - 2 * ball_Sy;
            end
            else
	            ball_x <= ball_x - ball_Sx;
	            if(ball_y - ball_Sy > 0)begin
	               ball_y <= ball_y - ball_Sy;
	            end
	            else begin // start to going down, go to going left and going down state
	               ball_y <= ball_y;
	               ball_dir <= 3'b010;
	            end
	          end
	        else begin // reach left limit
	           ball_x <= ball_x + ball_Sx;
	           ball_y <= ball_y; // start to reduce
	           ball_dir <= 3'b001; 
	        end
		end
	3'b001:	begin // ball in left region , going right,and going on , note that if ball_ye >= 240, just turn back, if < 190, x can keep going
	        if(ball_x > 280 && ball_ye < 215)begin // if over net
	           ball_x <= ball_x + ball_Sx;
	           ball_y <= ball_y - ball_Sy; // going on
	           ball_dir <= 3'b110;
	        end
	        else if(ball_x > 280 && ball_ye >= 215)begin // if under net
	           ball_x <= ball_x - ball_Sx;
	           ball_y <= ball_y - ball_Sy; // going on
	           ball_dir <= 3'b000;
	        end
	        else if(ball_x <= 280) begin
            if(meet1a_up)begin
              ball_x <= ball_x + 2*ball_Sx;
              ball_y <= ball_y - 2*ball_Sy;
            end
            else if(meet1a_down)begin
              ball_x <= ball_x + ball_Sx;
              ball_y <= ball_y + ball_Sy;
              ball_dir <= 3'b011;
            end
            else if(meet1a_right)begin
              ball_x <= ball_x + 2*ball_Sx;
              ball_y <= ball_y - 2*ball_Sy;
            end
            else if(meet1a_left) begin
              ball_x <= ball_x - ball_Sx;
              ball_y <= ball_y + ball_Sy;
              ball_dir <= 3'b000;
            end
            
	           ball_x <= ball_x + ball_Sx;
	           if(ball_y - ball_Sy > 0)begin
	               ball_y <= ball_y - ball_Sy;
	           end
	           else begin // start to going down, go to going right and going down state
	               ball_y <= ball_y;
	               ball_dir <= 3'b011;
	           end
	        end
	        else begin
	           ball_x <= ball_x + ball_Sx; // keep going
	           ball_y <= ball_y - ball_Sy; // keep going
	        end
		end
	3'b010:	begin // ball in left region , going left,and going down , note that if ball_ye >= 190, just turn back, if < 190, x can keep going
			if(ball_x > 2) begin // haven't reach the left limit
	           ball_x <= ball_x - ball_Sx;
	           if(ball_ye > 436)begin // start to going up
	               ball_y <= ball_y - ball_Sy;
	               ball_dir <= 3'b000;
	           end
	           else begin // keep going down
	               ball_y <= ball_y + ball_Sy;
	           end
	        end
	        else begin // reach left limit
	           ball_x <= ball_x; // start to going right
	           ball_y <= ball_y; 
	           ball_dir <= 3'b011; 
	        end
		end
	3'b011:	begin // ball in left region , going right,and going down , note that if ball_ye >= 190, just turn back, if < 190, x can keep going
	        if((ball_x + ball_Sx) > 280 && ball_ye < 215)begin // if over net
	           ball_x <= ball_x + ball_Sx;
	           ball_y <= ball_y; // going on
	           ball_dir <= 3'b111;
	        end
	        else if((ball_x + ball_Sx) > 280 && ball_ye >= 215)begin // if under net
	           ball_x <= ball_x - ball_Sx;
	           ball_y <= ball_y; // going on
	           ball_dir <= 3'b010;
	        end
	        else if(ball_x <= 280) begin // in the normal condition
	           ball_x <= ball_x + ball_Sx;
	           if(ball_ye > 436)begin  // if larger than the ground
	               ball_y <= ball_y - ball_Sy;
	               ball_dir <= 3'b001;
	           end
	           else begin // keep going down
	               ball_y <= ball_y + ball_Sy;
	           end
	        end
	        else begin
	           ball_x <= ball_x + ball_Sx; // keep going right
	           ball_y <= ball_y + ball_Sy; // keep going down
	        end
		end
	3'b100:	begin // ball in right region, going left and going on
	        if(ball_x <= 330 && ball_ye < 215)begin // if over net
	           ball_x <= ball_x - ball_Sx; // keep going left
	           ball_y <= ball_y - ball_Sy; // going on
	           ball_dir <= 3'b000; // to left region, going left and going down
	        end
	        else if(ball_x <= 330 && ball_ye >= 215)begin // if under net // start to going right
	           ball_x <= ball_x + ball_Sx; // turn to go right
	           ball_y <= ball_y - ball_Sy; // going on
	           ball_dir <= 3'b110;
	        end
	        else if(ball_x > 330) begin // in the normal condition
	           ball_x <= ball_x - ball_Sx;
	           if(ball_y - ball_Sy > 0)begin
	               ball_y <= ball_y - ball_Sy;
	           end
	           else begin // start to going down, 
	               ball_y <= ball_y; // keep going down
	               ball_dir <= 3'b101; // start to going left and going down
	           end
	        end
	        else begin
	           ball_x <= ball_x - ball_Sx; // start to going left
	           ball_y <= ball_y - ball_Sy; // keep going on
	        end
		end
	3'b101:	begin // ball in right region, going left and going down 
	        if(ball_x <= 330 && ball_ye < 215)begin // if over net
	           ball_x <= ball_x - ball_Sx; // keep going left
	           ball_y <= ball_y + ball_Sy; // going on
	           ball_dir <= 3'b010; // to left region, going left and going down
	        end

	        else if(ball_x <= 330 && ball_ye >= 215)begin // if under net
	           ball_x <= ball_x + ball_Sx; // turn to go right
	           ball_y <= ball_y + ball_Sy; // going down
	           ball_dir <= 3'b111;
	        end
	        else if(ball_x > 330) begin // in the normal condition
	           ball_x <= ball_x - ball_Sx;
	           if(ball_ye > 436)begin
	               ball_y <= ball_y - ball_Sy;
	               ball_dir <= 3'b100;
	           end
	           else begin // start to going down, 
	               ball_y <= ball_y + ball_Sy; // keep going down
	           end
	        end
	        else begin
	           ball_x <= ball_x - ball_Sx; // start to going left
	           ball_y <= ball_y + ball_Sy; // keep going down
	        end
		end
	3'b110:	begin // ball in right region, going right and going on 
			if(ball_xe <= 640) begin // in the normal condition
	           ball_x <= ball_x + ball_Sx;
	           if(ball_y - ball_Sy > 0)begin
	               ball_y <= ball_y - ball_Sy;
	           end
	           else begin // start to going down, go to going right and going down state
	               ball_y <= ball_y;
	               ball_dir <= 3'b111;
	           end
	        end
	        else if(ball_xe > 640)begin
	           ball_x <= ball_x - ball_Sx; // start to going left
	           ball_y <= ball_y + ball_Sy; // keep going down
	           ball_dir <= 3'b100;
	        end
		end
	3'b111:	begin // ball in right region, going right and going down
			if(ball_xe <= 640) begin // in the normal condition
	           ball_x <= ball_x + ball_Sx;
	           if(ball_ye > 436)begin  // if larger than the ground
	               ball_y <= ball_y - ball_Sy;
	               ball_dir <= 3'b110;
	           end
	           else begin // keep going down
	               ball_y <= ball_y + ball_Sy;
	           end
	        end
	        else if(ball_xe > 640)begin
	           ball_x <= ball_x - ball_Sx; // start to going left
	           ball_y <= ball_y + ball_Sy; // keep going down
	           ball_dir <= 3'b101;
	        end
		end
		endcase
  end		 	
end

assign ball_addrx = (pixel_x - ball_x);
assign ball_addry = (pixel_y - ball_y);

always @(posedge vga_clk  or negedge reset_n) begin
  if (~reset_n) begin
	ball_in1 <= 0;
	ball_in2 <= 0;
  end
  else if (frame_sync) begin
	if((ball_x >= 321 && ball_xe <= 639) && (ball_ye >= 436))begin // right region
		ball_in1 <= 1;
		ball_in2 <= 0;
	end
	else if ((ball_x >= 0 && ball_xe <= 319) && (ball_ye >= 436))begin // left region
		ball_in2 <= 1;
		ball_in1 <= 0;
	end
	else begin
		ball_in1 <= 0;
		ball_in2 <= 0;
	end
  end
end

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

// use 2 1 0 button to control the left don don mouse
// 2 : left , 1 : up, 0 : right
// y have to be reduce so don don mouse can jump
reg button1_reduce; // use to control reduce
reg button1_add; // use to control add
reg button1_jump; // use to control jump
reg reach1_the_ground;
reg reach1_the_top;
reg [30:0] add1_counter;
reg [30:0] red1_counter;
reg [6:0] jump1_speed_up; // use to control mouse jump , start is 26 , end is 0
reg [6:0] jump1_speed_down; // use to control mouse down, start is 0, end is 26

reg start1_jump;
always @(posedge vga_clk or negedge reset_n)begin // frame_sync
    if(~reset_n)begin
        jump1_speed_up <= 0; // start is 0
        jump1_speed_down <= 0;
        reach1_the_ground <= 1; // don don mouse is one the ground
        reach1_the_top <= 0;
        start1_jump <= 0;
    end
    else if(input_w && jump1_speed_up == 0 && jump1_speed_down == 0 && frame_sync && !reach1_the_top && !start1_jump) begin // after pressed btn1, start jump
        jump1_speed_up <= 26;
        jump1_speed_down <= 0;
        reach1_the_ground <= 0;
        start1_jump <= 1; // after usr_btn1 pressed , start jump until jump speed down == 26
    end
    else if(start1_jump && jump1_speed_down == 26 && frame_sync && reach1_the_top)begin // when speed down = 26, stop jump logic
        jump1_speed_up <= 0;
        jump1_speed_down <= 0;
        reach1_the_ground <= 1; // when jump_speed_down == 26
        reach1_the_top <= 0; // reset reach the top logic
        start1_jump <= 0;
    end
    else if(jump1_speed_up == 0 && frame_sync && start1_jump && !reach1_the_top)begin // if speed up = 0 and start jump , means reach the top of jump limit, start jump down
        reach1_the_top <= 1;
        jump1_speed_up <= 0;
        jump1_speed_down <= 0;
    end
    else if(frame_sync && !reach1_the_top && start1_jump)begin // if not reach the top, keep going up
        jump1_speed_up <= jump1_speed_up - 2;
        jump1_speed_down <= 0;
    end
    else if(frame_sync && !reach1_the_ground && reach1_the_top && start1_jump) begin // if racht the top,but not reach the ground, keep going down
        jump1_speed_up <= 0;
        jump1_speed_down <= jump1_speed_down + 2;
    end
    else if(reach1_the_ground && frame_sync)begin // keep the original condition 
        jump1_speed_up <= 0;
        jump1_speed_down <= 0;
    end
end

always @(posedge clk or negedge reset_n) begin
    if(~reset_n)begin
        button1_reduce <= 0;
        button1_add <= 0;
        button1_jump <= 0;
        add1_counter <= 0;
        red1_counter <= 0;
    end
    else if(frame_sync)begin // one gap
        if(input_d)begin
            button1_add <= 1;
        end
        else begin
            button1_add <= 0;
        end
        if(input_a)begin
            button1_reduce <= 1;
        end
        else begin 
            button1_reduce <= 0;
        end
    end
end

always @(posedge vga_clk  or negedge reset_n) begin
	if (~reset_n) begin
		poke1_x <= 320;
		poke1_y <= 320;
		poke1_dir<= 2'b00;
  	end
  	else if (frame_sync) begin
		if(STATE == S_MAIN_START)begin
			poke1_x <= 320;
			poke1_y <= 320;
			poke1_dir<= 2'b00;
		end
		else if(STATE == S_MAIN_RUN) begin
	 		if (poke1_xe >= 639) begin
	    		poke1_x <= poke1_x - button1_reduce * 4; 	
				if(poke1_y - jump1_speed_up + jump1_speed_down > 320)begin
		   			poke1_y <= 320;
				end
				else begin
		  			poke1_y <= poke1_y - jump1_speed_up + jump1_speed_down;
				end
	 		end
	 		else if (poke1_x <= 310) begin
				if(poke1_y - jump1_speed_up + jump1_speed_down > 320)begin
	   				poke1_y <= 320;
				end
				else begin
	  				poke1_y <= poke1_y - jump1_speed_up + jump1_speed_down;			
				end
				poke1_x <= poke1_x + button1_add * 4;
 			end
			else begin
			   	poke1_x <= poke1_x + button1_add * 4 - button1_reduce * 4;
	    		if(poke1_y - jump1_speed_up + jump1_speed_down > 320)begin
		   			poke1_y <= 320;
				end
				else begin
		  			poke1_y <= poke1_y - jump1_speed_up + jump1_speed_down;
				end
	 		end
  		end	
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
reg reach_the_ground;
reg reach_the_top;
reg [30:0] add_counter;
reg [30:0] red_counter;
reg [6:0] jump_speed_up; // use to control mouse jump , start is 26 , end is 0
reg [6:0] jump_speed_down; // use to control mouse down, start is 0, end is 26

reg start_jump;
always @(posedge vga_clk or negedge reset_n)begin // frame_sync
    if(~reset_n)begin
        jump_speed_up <= 0; // start is 0
        jump_speed_down <= 0;
        reach_the_ground <= 1; // don don mouse is one the ground
        reach_the_top <= 0;
        start_jump <= 0;
    end
    else if(usr_btn[1] && jump_speed_up == 0 && jump_speed_down == 0 && frame_sync && !reach_the_top && !start_jump) begin // after pressed btn1, start jump
        jump_speed_up <= 26;
        jump_speed_down <= 0;
        reach_the_ground <= 0;
        start_jump <= 1; // after usr_btn1 pressed , start jump until jump speed down == 26
    end
    else if(start_jump && jump_speed_down == 26 && frame_sync && reach_the_top)begin // when speed down = 26, stop jump logic
        jump_speed_up <= 0;
        jump_speed_down <= 0;
        reach_the_ground <= 1; // when jump_speed_down == 26
        reach_the_top <= 0; // reset reach the top logic
        start_jump <= 0;
    end
    else if(jump_speed_up == 0 && frame_sync && start_jump && !reach_the_top)begin // if speed up = 0 and start jump , means reach the top of jump limit, start jump down
        reach_the_top <= 1;
        jump_speed_up <= 0;
        jump_speed_down <= 0;
    end
    else if(frame_sync && !reach_the_top && start_jump)begin // if not reach the top, keep going up
        jump_speed_up <= jump_speed_up - 2;
        jump_speed_down <= 0;
    end
    else if(frame_sync && !reach_the_ground && reach_the_top && start_jump) begin // if racht the top,but not reach the ground, keep going down
        jump_speed_up <= 0;
        jump_speed_down <= jump_speed_down + 2;
    end
    else if(reach_the_ground && frame_sync)begin // keep the original condition 
        jump_speed_up <= 0;
        jump_speed_down <= 0;
    end
end

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
    end
end

always @(posedge vga_clk  or negedge reset_n) begin
	if (~reset_n) begin
		poke1a_x <= 0;
		poke1a_y <= 320;
		poke1a_dir<= 2'b00;
  	end
  	else if (frame_sync) begin
		if(STATE == S_MAIN_START)begin
			poke1a_x <= 0;
			poke1a_y <= 320;
			poke1a_dir<= 2'b00;
		end
		else if (STATE == S_MAIN_RUN) begin
			if (poke1a_xe >= 330) begin
	    		poke1a_x <= poke1a_x - button_reduce * 2; 	
				if(poke1a_y - jump_speed_up + jump_speed_down > 320)begin
		   		poke1a_y <= 320;
				end
				else begin
		  			poke1a_y <= poke1a_y - jump_speed_up + jump_speed_down;
				end
	 		end
	 		else if (poke1a_x <= 0) begin
				if(poke1a_y - jump_speed_up + jump_speed_down > 320)begin
		   			poke1a_y <= 320;
				end
				else begin
		  			poke1a_y <= poke1a_y - jump_speed_up + jump_speed_down;
				end
				poke1a_x <= poke1a_x + button_add * 2; 
	 		end
	 		else begin
	   			poke1a_x <= poke1a_x + button_add * 2 - button_reduce * 2;
	    		if(poke1a_y - jump_speed_up + jump_speed_down > 320)begin
		   			poke1a_y <= 320;
				end
				else begin
		  			poke1a_y <= poke1a_y - jump_speed_up + jump_speed_down;
				end
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
// score 1 and score 2
reg [3:0] score1;
reg [3:0] score2;

always @(posedge vga_clk or negedge reset_n) begin
	if(~reset_n) begin
		score1 <= 0;
		score2 <= 0;
	end 
	else if (frame_sync) begin
		if(STATE == S_MAIN_RUN)begin
			score1 <= (ball_in1 && score1 < 7) ? score1 + 1 : score1;
			score2 <= (ball_in2 && score2 < 7) ? score2 + 1 : score2;
		end
	end
end

// ------------------------------------------------------------------------
// number 1
reg [9:0] num1_x;  //0~640
reg [9:0] num1_y;	//0~480
wire [9:0] num1_xe;
wire [9:0] num1_ye; 
assign num1_xe = num1_x + number_W - 1;
assign num1_ye = num1_y + number_H - 1;
wire [5:0] number1_addrx ;   //0~63
wire [5:0] number1_addry ;   //0~63

assign number1_region = (pixel_y >= num1_y) && (pixel_y <= num1_ye) && (pixel_x >= num1_x ) && (pixel_x <= num1_xe);

assign number1_addrx = (pixel_x - num1_x) ;
assign number1_addry = (pixel_y - num1_y) ;
//---------------------------------------------------------------------------
//change frame
always @(*) begin
	num1_x <= 40;
	num1_y <= 40;
	case(score1)
	0:	number1_addr <= number1_addry* number_W + number1_addrx;
	1:	number1_addr <= number1_addry* number_W + number1_addrx + number_W*number_H;
	2:	number1_addr <= number1_addry* number_W + number1_addrx + number_W*number_H*2;
	3:	number1_addr <= number1_addry* number_W + number1_addrx + number_W*number_H*3;
	4:	number1_addr <= number1_addry* number_W + number1_addrx + number_W*number_H*4;	
	5:	number1_addr <= number1_addry* number_W + number1_addrx + number_W*number_H*5;
	6:	number1_addr <= number1_addry* number_W + number1_addrx + number_W*number_H*6;
	7:	number1_addr <= number1_addry* number_W + number1_addrx + number_W*number_H*7;
	endcase
end
// ------------------------------------------------------------------------
// number 2
reg [9:0] num2_x;  //0~640
reg [9:0] num2_y;	//0~480
wire [9:0] num2_xe;
wire [9:0] num2_ye; 
assign num2_xe = num2_x + number_W - 1;
assign num2_ye = num2_y + number_H - 1;
wire [5:0] number2_addrx ;   //0~63
wire [5:0] number2_addry ;   //0~63

assign number2_region = (pixel_y >= num2_y) && (pixel_y <= num2_ye) && (pixel_x >= num2_x ) && (pixel_x <= num2_xe);

assign number2_addrx = (pixel_x - num2_x) ;
assign number2_addry = (pixel_y - num2_y) ;
//---------------------------------------------------------------------------
//change frame
always @(*) begin
	num2_x <= 564;
	num2_y <= 40;
	case(score2)
	0:	number2_addr <= number2_addry* number_W + number2_addrx;
	1:	number2_addr <= number2_addry* number_W + number2_addrx + number_W*number_H;
	2:	number2_addr <= number2_addry* number_W + number2_addrx + number_W*number_H*2;
	3:	number2_addr <= number2_addry* number_W + number2_addrx + number_W*number_H*3;
	4:	number2_addr <= number2_addry* number_W + number2_addrx + number_W*number_H*4;	
	5:	number2_addr <= number2_addry* number_W + number2_addrx + number_W*number_H*5;
	6:	number2_addr <= number2_addry* number_W + number2_addrx + number_W*number_H*6;	
	7:	number2_addr <= number2_addry* number_W + number2_addrx + number_W*number_H*7;
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
wire ball_region_green = (ball_out == 12'h0F0);
wire number_region_green = (number_out == 12'h0F0);
wire prompt_region_green = (prompt_out == 12'h0F0);

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
  	else begin
  		if(STATE == S_MAIN_START || STATE == S_MAIN_END)begin
			if (prompt_region && ~prompt_region_green)
				rgb_next = prompt_out;	
			else if (poke1_region && ~poke1_region_green )
				rgb_next = pokemon1_out;  //poke1
			else if (poke1a_region && ~poke1_region_green )
				rgb_next = pokemon1_out;
			else if ((number1_region || number2_region) && ~number_region_green )
				rgb_next = number_out;
			else 
				rgb_next = data_out;
  		end
		else if (STATE == S_MAIN_RUN) begin
  			if (poke1_region && ~poke1_region_green )
				rgb_next = pokemon1_out;  //poke1
			else if (poke1a_region && ~poke1_region_green )
				rgb_next = pokemon1_out;	
			else if (ball_region && ~ball_region_green )
				rgb_next = ball_out;
			else if ((number1_region || number2_region) && ~number_region_green )
				rgb_next = number_out;	
			else 
				rgb_next = data_out; // RGB value at (pixel_x, pixel_y)
	 	end
	end
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
always @(*) begin
	btn_pressed[3] = (btn_level[3] == 1 && prev_btn_level[3] == 0)? 1 : 0;
end
//
//----------------------------------------------------

endmodule
