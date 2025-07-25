autoidx 10
attribute \cells_not_processed 1
attribute \src "asicworld/verilog/code_hdl_models_gray_counter.v:7.1-33.10"
module \gray_counter
  attribute \src "asicworld/verilog/code_hdl_models_gray_counter.v:22.3-26.24"
  wire width 8 $0\count[7:0]
  attribute \src "asicworld/verilog/code_hdl_models_gray_counter.v:26.14-26.23"
  wire width 32 $add$asicworld/verilog/code_hdl_models_gray_counter.v:26$2_Y
  attribute \src "asicworld/verilog/code_hdl_models_gray_counter.v:28.51-29.24"
  wire $xor$asicworld/verilog/code_hdl_models_gray_counter.v:28$8_Y
  attribute \src "asicworld/verilog/code_hdl_models_gray_counter.v:28.29-28.48"
  wire $xor$asicworld/verilog/code_hdl_models_gray_counter.v:28$9_Y
  attribute \src "asicworld/verilog/code_hdl_models_gray_counter.v:29.50-30.24"
  wire $xor$asicworld/verilog/code_hdl_models_gray_counter.v:29$6_Y
  attribute \src "asicworld/verilog/code_hdl_models_gray_counter.v:29.27-29.46"
  wire $xor$asicworld/verilog/code_hdl_models_gray_counter.v:29$7_Y
  attribute \src "asicworld/verilog/code_hdl_models_gray_counter.v:30.50-31.24"
  wire $xor$asicworld/verilog/code_hdl_models_gray_counter.v:30$4_Y
  attribute \src "asicworld/verilog/code_hdl_models_gray_counter.v:30.27-30.46"
  wire $xor$asicworld/verilog/code_hdl_models_gray_counter.v:30$5_Y
  attribute \src "asicworld/verilog/code_hdl_models_gray_counter.v:31.27-31.46"
  wire $xor$asicworld/verilog/code_hdl_models_gray_counter.v:31$3_Y
  attribute \src "asicworld/verilog/code_hdl_models_gray_counter.v:15.9-15.12"
  wire input 3 \clk
  attribute \src "asicworld/verilog/code_hdl_models_gray_counter.v:20.13-20.18"
  wire width 8 \count
  attribute \src "asicworld/verilog/code_hdl_models_gray_counter.v:15.19-15.25"
  wire input 2 \enable
  attribute \src "asicworld/verilog/code_hdl_models_gray_counter.v:17.17-17.20"
  wire width 8 output 1 \out
  attribute \src "asicworld/verilog/code_hdl_models_gray_counter.v:15.14-15.17"
  wire input 4 \rst
  attribute \src "asicworld/verilog/code_hdl_models_gray_counter.v:26.14-26.23"
  cell $add $add$asicworld/verilog/code_hdl_models_gray_counter.v:26$2
    parameter \A_SIGNED 0
    parameter \A_WIDTH 8
    parameter \B_SIGNED 0
    parameter \B_WIDTH 32
    parameter \Y_WIDTH 32
    connect \A \count
    connect \B 1
    connect \Y $add$asicworld/verilog/code_hdl_models_gray_counter.v:26$2_Y
  end
  attribute \src "asicworld/verilog/code_hdl_models_gray_counter.v:28.51-29.24"
  cell $xor $xor$asicworld/verilog/code_hdl_models_gray_counter.v:28$8
    parameter \A_SIGNED 0
    parameter \A_WIDTH 1
    parameter \B_SIGNED 0
    parameter \B_WIDTH 1
    parameter \Y_WIDTH 1
    connect \A \count [6]
    connect \B \count [5]
    connect \Y $xor$asicworld/verilog/code_hdl_models_gray_counter.v:28$8_Y
  end
  attribute \src "asicworld/verilog/code_hdl_models_gray_counter.v:28.29-28.48"
  cell $xor $xor$asicworld/verilog/code_hdl_models_gray_counter.v:28$9
    parameter \A_SIGNED 0
    parameter \A_WIDTH 1
    parameter \B_SIGNED 0
    parameter \B_WIDTH 1
    parameter \Y_WIDTH 1
    connect \A \count [7]
    connect \B \count [6]
    connect \Y $xor$asicworld/verilog/code_hdl_models_gray_counter.v:28$9_Y
  end
  attribute \src "asicworld/verilog/code_hdl_models_gray_counter.v:29.50-30.24"
  cell $xor $xor$asicworld/verilog/code_hdl_models_gray_counter.v:29$6
    parameter \A_SIGNED 0
    parameter \A_WIDTH 1
    parameter \B_SIGNED 0
    parameter \B_WIDTH 1
    parameter \Y_WIDTH 1
    connect \A \count [4]
    connect \B \count [3]
    connect \Y $xor$asicworld/verilog/code_hdl_models_gray_counter.v:29$6_Y
  end
  attribute \src "asicworld/verilog/code_hdl_models_gray_counter.v:29.27-29.46"
  cell $xor $xor$asicworld/verilog/code_hdl_models_gray_counter.v:29$7
    parameter \A_SIGNED 0
    parameter \A_WIDTH 1
    parameter \B_SIGNED 0
    parameter \B_WIDTH 1
    parameter \Y_WIDTH 1
    connect \A \count [5]
    connect \B \count [4]
    connect \Y $xor$asicworld/verilog/code_hdl_models_gray_counter.v:29$7_Y
  end
  attribute \src "asicworld/verilog/code_hdl_models_gray_counter.v:30.50-31.24"
  cell $xor $xor$asicworld/verilog/code_hdl_models_gray_counter.v:30$4
    parameter \A_SIGNED 0
    parameter \A_WIDTH 1
    parameter \B_SIGNED 0
    parameter \B_WIDTH 1
    parameter \Y_WIDTH 1
    connect \A \count [2]
    connect \B \count [1]
    connect \Y $xor$asicworld/verilog/code_hdl_models_gray_counter.v:30$4_Y
  end
  attribute \src "asicworld/verilog/code_hdl_models_gray_counter.v:30.27-30.46"
  cell $xor $xor$asicworld/verilog/code_hdl_models_gray_counter.v:30$5
    parameter \A_SIGNED 0
    parameter \A_WIDTH 1
    parameter \B_SIGNED 0
    parameter \B_WIDTH 1
    parameter \Y_WIDTH 1
    connect \A \count [3]
    connect \B \count [2]
    connect \Y $xor$asicworld/verilog/code_hdl_models_gray_counter.v:30$5_Y
  end
  attribute \src "asicworld/verilog/code_hdl_models_gray_counter.v:31.27-31.46"
  cell $xor $xor$asicworld/verilog/code_hdl_models_gray_counter.v:31$3
    parameter \A_SIGNED 0
    parameter \A_WIDTH 1
    parameter \B_SIGNED 0
    parameter \B_WIDTH 1
    parameter \Y_WIDTH 1
    connect \A \count [1]
    connect \B \count [0]
    connect \Y $xor$asicworld/verilog/code_hdl_models_gray_counter.v:31$3_Y
  end
  attribute \src "asicworld/verilog/code_hdl_models_gray_counter.v:22.3-26.24"
  process $proc$asicworld/verilog/code_hdl_models_gray_counter.v:22$1
    assign $0\count[7:0] \count
    attribute \src "asicworld/verilog/code_hdl_models_gray_counter.v:23.3-26.24"
    switch \rst
      attribute \src "asicworld/verilog/code_hdl_models_gray_counter.v:23.7-23.10"
      case 1'1
        assign $0\count[7:0] 8'00000000
      attribute \src "asicworld/verilog/code_hdl_models_gray_counter.v:25.3-25.7"
      case 
        attribute \src "asicworld/verilog/code_hdl_models_gray_counter.v:25.8-26.24"
        switch \enable
          attribute \src "asicworld/verilog/code_hdl_models_gray_counter.v:25.12-25.18"
          case 1'1
            assign $0\count[7:0] $add$asicworld/verilog/code_hdl_models_gray_counter.v:26$2_Y [7:0]
          case 
        end
    end
    sync posedge \clk
      update \count $0\count[7:0]
  end
  connect \out { \count [7] $xor$asicworld/verilog/code_hdl_models_gray_counter.v:28$9_Y $xor$asicworld/verilog/code_hdl_models_gray_counter.v:28$8_Y $xor$asicworld/verilog/code_hdl_models_gray_counter.v:29$7_Y $xor$asicworld/verilog/code_hdl_models_gray_counter.v:29$6_Y $xor$asicworld/verilog/code_hdl_models_gray_counter.v:30$5_Y $xor$asicworld/verilog/code_hdl_models_gray_counter.v:30$4_Y $xor$asicworld/verilog/code_hdl_models_gray_counter.v:31$3_Y }
end
