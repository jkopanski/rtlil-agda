autoidx 4
attribute \dynports 1
attribute \cells_not_processed 1
attribute \src "asicworld/verilog/code_hdl_models_GrayCounter.v:7.1-33.10"
module \GrayCounter
  parameter \COUNTER_WIDTH 4
  attribute \src "asicworld/verilog/code_hdl_models_GrayCounter.v:22.5-31.12"
  wire width 4 $0\BinaryCount[3:0]
  attribute \src "asicworld/verilog/code_hdl_models_GrayCounter.v:22.5-31.12"
  wire width 4 $0\GrayCount_out[3:0]
  attribute \src "asicworld/verilog/code_hdl_models_GrayCounter.v:28.30-28.45"
  wire width 32 $add$asicworld/verilog/code_hdl_models_GrayCounter.v:28$2_Y
  attribute \src "asicworld/verilog/code_hdl_models_GrayCounter.v:30.31-30.94"
  wire width 3 $xor$asicworld/verilog/code_hdl_models_GrayCounter.v:30$3_Y
  attribute \src "asicworld/verilog/code_hdl_models_GrayCounter.v:18.40-18.51"
  wire width 4 \BinaryCount
  attribute \src "asicworld/verilog/code_hdl_models_GrayCounter.v:13.41-13.49"
  wire input 3 \Clear_in
  attribute \src "asicworld/verilog/code_hdl_models_GrayCounter.v:15.41-15.44"
  wire input 4 \Clk
  attribute \src "asicworld/verilog/code_hdl_models_GrayCounter.v:12.41-12.50"
  wire input 2 \Enable_in
  attribute \src "asicworld/verilog/code_hdl_models_GrayCounter.v:10.41-10.54"
  wire width 4 output 1 \GrayCount_out
  attribute \src "asicworld/verilog/code_hdl_models_GrayCounter.v:28.30-28.45"
  cell $add $add$asicworld/verilog/code_hdl_models_GrayCounter.v:28$2
    parameter \A_SIGNED 0
    parameter \A_WIDTH 4
    parameter \B_SIGNED 0
    parameter \B_WIDTH 32
    parameter \Y_WIDTH 32
    connect \A \BinaryCount
    connect \B 1
    connect \Y $add$asicworld/verilog/code_hdl_models_GrayCounter.v:28$2_Y
  end
  attribute \src "asicworld/verilog/code_hdl_models_GrayCounter.v:30.31-30.94"
  cell $xor $xor$asicworld/verilog/code_hdl_models_GrayCounter.v:30$3
    parameter \A_SIGNED 0
    parameter \A_WIDTH 3
    parameter \B_SIGNED 0
    parameter \B_WIDTH 3
    parameter \Y_WIDTH 3
    connect \A \BinaryCount [2:0]
    connect \B \BinaryCount [3:1]
    connect \Y $xor$asicworld/verilog/code_hdl_models_GrayCounter.v:30$3_Y
  end
  attribute \src "asicworld/verilog/code_hdl_models_GrayCounter.v:22.5-31.12"
  process $proc$asicworld/verilog/code_hdl_models_GrayCounter.v:22$1
    assign $0\GrayCount_out[3:0] \GrayCount_out
    assign $0\BinaryCount[3:0] \BinaryCount
    attribute \src "asicworld/verilog/code_hdl_models_GrayCounter.v:23.9-31.12"
    switch \Clear_in
      attribute \src "asicworld/verilog/code_hdl_models_GrayCounter.v:23.13-23.21"
      case 1'1
        assign $0\BinaryCount[3:0] 4'0001
        assign $0\GrayCount_out[3:0] 4'0000
      attribute \src "asicworld/verilog/code_hdl_models_GrayCounter.v:27.9-27.13"
      case 
        attribute \src "asicworld/verilog/code_hdl_models_GrayCounter.v:27.14-31.12"
        switch \Enable_in
          attribute \src "asicworld/verilog/code_hdl_models_GrayCounter.v:27.18-27.27"
          case 1'1
            assign $0\BinaryCount[3:0] $add$asicworld/verilog/code_hdl_models_GrayCounter.v:28$2_Y [3:0]
            assign $0\GrayCount_out[3:0] { \BinaryCount [3] $xor$asicworld/verilog/code_hdl_models_GrayCounter.v:30$3_Y }
          case 
        end
    end
    sync posedge \Clk
      update \GrayCount_out $0\GrayCount_out[3:0]
      update \BinaryCount $0\BinaryCount[3:0]
  end
end
