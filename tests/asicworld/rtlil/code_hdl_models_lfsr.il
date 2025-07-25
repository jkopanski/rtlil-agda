autoidx 4
attribute \cells_not_processed 1
attribute \src "asicworld/verilog/code_hdl_models_lfsr.v:7.1-35.10"
module \lfsr
  attribute \src "asicworld/verilog/code_hdl_models_lfsr.v:25.1-33.4"
  wire width 8 $0\out[7:0]
  attribute \src "asicworld/verilog/code_hdl_models_lfsr.v:23.26-23.44"
  wire $logic_not$asicworld/verilog/code_hdl_models_lfsr.v:23$2_Y
  attribute \src "asicworld/verilog/code_hdl_models_lfsr.v:23.28-23.43"
  wire $xor$asicworld/verilog/code_hdl_models_lfsr.v:23$1_Y
  attribute \src "asicworld/verilog/code_hdl_models_lfsr.v:17.15-17.18"
  wire input 3 \clk
  attribute \src "asicworld/verilog/code_hdl_models_lfsr.v:17.7-17.13"
  wire input 2 \enable
  attribute \src "asicworld/verilog/code_hdl_models_lfsr.v:20.13-20.28"
  wire \linear_feedback
  attribute \src "asicworld/verilog/code_hdl_models_lfsr.v:15.14-15.17"
  wire width 8 output 1 \out
  attribute \src "asicworld/verilog/code_hdl_models_lfsr.v:17.20-17.25"
  wire input 4 \reset
  attribute \src "asicworld/verilog/code_hdl_models_lfsr.v:23.26-23.44"
  cell $logic_not $logic_not$asicworld/verilog/code_hdl_models_lfsr.v:23$2
    parameter \A_SIGNED 0
    parameter \A_WIDTH 1
    parameter \Y_WIDTH 1
    connect \A $xor$asicworld/verilog/code_hdl_models_lfsr.v:23$1_Y
    connect \Y $logic_not$asicworld/verilog/code_hdl_models_lfsr.v:23$2_Y
  end
  attribute \src "asicworld/verilog/code_hdl_models_lfsr.v:23.28-23.43"
  cell $xor $xor$asicworld/verilog/code_hdl_models_lfsr.v:23$1
    parameter \A_SIGNED 0
    parameter \A_WIDTH 1
    parameter \B_SIGNED 0
    parameter \B_WIDTH 1
    parameter \Y_WIDTH 1
    connect \A \out [7]
    connect \B \out [3]
    connect \Y $xor$asicworld/verilog/code_hdl_models_lfsr.v:23$1_Y
  end
  attribute \src "asicworld/verilog/code_hdl_models_lfsr.v:25.1-33.4"
  process $proc$asicworld/verilog/code_hdl_models_lfsr.v:25$3
    assign $0\out[7:0] \out
    attribute \src "asicworld/verilog/code_hdl_models_lfsr.v:26.1-33.4"
    switch \reset
      attribute \src "asicworld/verilog/code_hdl_models_lfsr.v:26.5-26.10"
      case 1'1
        assign $0\out[7:0] 8'00000000
      attribute \src "asicworld/verilog/code_hdl_models_lfsr.v:28.5-28.9"
      case 
        attribute \src "asicworld/verilog/code_hdl_models_lfsr.v:28.10-33.4"
        switch \enable
          attribute \src "asicworld/verilog/code_hdl_models_lfsr.v:28.14-28.20"
          case 1'1
            assign $0\out[7:0] { \out [6:0] \linear_feedback }
          case 
        end
    end
    sync posedge \clk
      update \out $0\out[7:0]
  end
  connect \linear_feedback $logic_not$asicworld/verilog/code_hdl_models_lfsr.v:23$2_Y
end
