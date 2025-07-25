autoidx 7
attribute \cells_not_processed 1
attribute \src "asicworld/verilog/code_hdl_models_serial_crc.v:7.1-54.10"
module \serial_crc_ccitt
  attribute \src "asicworld/verilog/code_hdl_models_serial_crc.v:28.1-52.4"
  wire width 16 $0\lfsr[15:0]
  attribute \src "asicworld/verilog/code_hdl_models_serial_crc.v:35.17-35.35"
  wire $xor$asicworld/verilog/code_hdl_models_serial_crc.v:35$2_Y
  attribute \src "asicworld/verilog/code_hdl_models_serial_crc.v:40.17-40.34"
  wire $xor$asicworld/verilog/code_hdl_models_serial_crc.v:40$3_Y
  attribute \src "asicworld/verilog/code_hdl_models_serial_crc.v:40.17-40.45"
  wire $xor$asicworld/verilog/code_hdl_models_serial_crc.v:40$4_Y
  attribute \src "asicworld/verilog/code_hdl_models_serial_crc.v:47.17-47.35"
  wire $xor$asicworld/verilog/code_hdl_models_serial_crc.v:47$5_Y
  attribute \src "asicworld/verilog/code_hdl_models_serial_crc.v:47.17-47.46"
  wire $xor$asicworld/verilog/code_hdl_models_serial_crc.v:47$6_Y
  attribute \src "asicworld/verilog/code_hdl_models_serial_crc.v:16.7-16.10"
  wire input 1 \clk
  attribute \src "asicworld/verilog/code_hdl_models_serial_crc.v:22.15-22.22"
  wire width 16 output 6 \crc_out
  attribute \src "asicworld/verilog/code_hdl_models_serial_crc.v:20.7-20.14"
  wire input 5 \data_in
  attribute \src "asicworld/verilog/code_hdl_models_serial_crc.v:18.7-18.13"
  wire input 3 \enable
  attribute \src "asicworld/verilog/code_hdl_models_serial_crc.v:19.7-19.11"
  wire input 4 \init
  attribute \src "asicworld/verilog/code_hdl_models_serial_crc.v:24.14-24.18"
  wire width 16 \lfsr
  attribute \src "asicworld/verilog/code_hdl_models_serial_crc.v:17.7-17.12"
  wire input 2 \reset
  attribute \src "asicworld/verilog/code_hdl_models_serial_crc.v:35.17-35.35"
  cell $xor $xor$asicworld/verilog/code_hdl_models_serial_crc.v:35$2
    parameter \A_SIGNED 0
    parameter \A_WIDTH 1
    parameter \B_SIGNED 0
    parameter \B_WIDTH 1
    parameter \Y_WIDTH 1
    connect \A \data_in
    connect \B \lfsr [15]
    connect \Y $xor$asicworld/verilog/code_hdl_models_serial_crc.v:35$2_Y
  end
  attribute \src "asicworld/verilog/code_hdl_models_serial_crc.v:40.17-40.34"
  cell $xor $xor$asicworld/verilog/code_hdl_models_serial_crc.v:40$3
    parameter \A_SIGNED 0
    parameter \A_WIDTH 1
    parameter \B_SIGNED 0
    parameter \B_WIDTH 1
    parameter \Y_WIDTH 1
    connect \A \lfsr [4]
    connect \B \data_in
    connect \Y $xor$asicworld/verilog/code_hdl_models_serial_crc.v:40$3_Y
  end
  attribute \src "asicworld/verilog/code_hdl_models_serial_crc.v:40.17-40.45"
  cell $xor $xor$asicworld/verilog/code_hdl_models_serial_crc.v:40$4
    parameter \A_SIGNED 0
    parameter \A_WIDTH 1
    parameter \B_SIGNED 0
    parameter \B_WIDTH 1
    parameter \Y_WIDTH 1
    connect \A $xor$asicworld/verilog/code_hdl_models_serial_crc.v:40$3_Y
    connect \B \lfsr [15]
    connect \Y $xor$asicworld/verilog/code_hdl_models_serial_crc.v:40$4_Y
  end
  attribute \src "asicworld/verilog/code_hdl_models_serial_crc.v:47.17-47.35"
  cell $xor $xor$asicworld/verilog/code_hdl_models_serial_crc.v:47$5
    parameter \A_SIGNED 0
    parameter \A_WIDTH 1
    parameter \B_SIGNED 0
    parameter \B_WIDTH 1
    parameter \Y_WIDTH 1
    connect \A \lfsr [11]
    connect \B \data_in
    connect \Y $xor$asicworld/verilog/code_hdl_models_serial_crc.v:47$5_Y
  end
  attribute \src "asicworld/verilog/code_hdl_models_serial_crc.v:47.17-47.46"
  cell $xor $xor$asicworld/verilog/code_hdl_models_serial_crc.v:47$6
    parameter \A_SIGNED 0
    parameter \A_WIDTH 1
    parameter \B_SIGNED 0
    parameter \B_WIDTH 1
    parameter \Y_WIDTH 1
    connect \A $xor$asicworld/verilog/code_hdl_models_serial_crc.v:47$5_Y
    connect \B \lfsr [15]
    connect \Y $xor$asicworld/verilog/code_hdl_models_serial_crc.v:47$6_Y
  end
  attribute \src "asicworld/verilog/code_hdl_models_serial_crc.v:28.1-52.4"
  process $proc$asicworld/verilog/code_hdl_models_serial_crc.v:28$1
    assign $0\lfsr[15:0] \lfsr
    attribute \src "asicworld/verilog/code_hdl_models_serial_crc.v:29.1-52.4"
    switch \reset
      attribute \src "asicworld/verilog/code_hdl_models_serial_crc.v:29.5-29.10"
      case 1'1
        assign $0\lfsr[15:0] 16'1111111111111111
      attribute \src "asicworld/verilog/code_hdl_models_serial_crc.v:31.5-31.9"
      case 
        attribute \src "asicworld/verilog/code_hdl_models_serial_crc.v:31.10-52.4"
        switch \enable
          attribute \src "asicworld/verilog/code_hdl_models_serial_crc.v:31.14-31.20"
          case 1'1
            attribute \src "asicworld/verilog/code_hdl_models_serial_crc.v:32.3-51.6"
            switch \init
              attribute \src "asicworld/verilog/code_hdl_models_serial_crc.v:32.7-32.11"
              case 1'1
                assign $0\lfsr[15:0] 16'1111111111111111
              attribute \src "asicworld/verilog/code_hdl_models_serial_crc.v:34.7-34.11"
              case 
                assign $0\lfsr[15:0] [0] $xor$asicworld/verilog/code_hdl_models_serial_crc.v:35$2_Y
                assign $0\lfsr[15:0] [1] \lfsr [0]
                assign $0\lfsr[15:0] [2] \lfsr [1]
                assign $0\lfsr[15:0] [3] \lfsr [2]
                assign $0\lfsr[15:0] [4] \lfsr [3]
                assign $0\lfsr[15:0] [5] $xor$asicworld/verilog/code_hdl_models_serial_crc.v:40$4_Y
                assign $0\lfsr[15:0] [6] \lfsr [5]
                assign $0\lfsr[15:0] [7] \lfsr [6]
                assign $0\lfsr[15:0] [8] \lfsr [7]
                assign $0\lfsr[15:0] [9] \lfsr [8]
                assign $0\lfsr[15:0] [10] \lfsr [9]
                assign $0\lfsr[15:0] [11] \lfsr [10]
                assign $0\lfsr[15:0] [12] $xor$asicworld/verilog/code_hdl_models_serial_crc.v:47$6_Y
                assign $0\lfsr[15:0] [13] \lfsr [12]
                assign $0\lfsr[15:0] [14] \lfsr [13]
                assign $0\lfsr[15:0] [15] \lfsr [14]
            end
          case 
        end
    end
    sync posedge \clk
      update \lfsr $0\lfsr[15:0]
  end
  connect \crc_out \lfsr
end
