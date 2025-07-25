autoidx 4
attribute \cells_not_processed 1
attribute \src "asicworld/verilog/code_hdl_models_decoder_using_assign.v:7.1-20.10"
module \decoder_using_assign
  attribute \src "asicworld/verilog/code_hdl_models_decoder_using_assign.v:18.22-18.57"
  wire width 32 $extend$asicworld/verilog/code_hdl_models_decoder_using_assign.v:18$2_Y
  attribute \src "asicworld/verilog/code_hdl_models_decoder_using_assign.v:18.34-18.48"
  wire width 32 $shl$asicworld/verilog/code_hdl_models_decoder_using_assign.v:18$1_Y
  attribute \src "asicworld/verilog/code_hdl_models_decoder_using_assign.v:18.22-18.57"
  wire width 32 $ternary$asicworld/verilog/code_hdl_models_decoder_using_assign.v:18$3_Y
  attribute \src "asicworld/verilog/code_hdl_models_decoder_using_assign.v:12.13-12.22"
  wire width 4 input 1 \binary_in
  attribute \src "asicworld/verilog/code_hdl_models_decoder_using_assign.v:14.15-14.26"
  wire width 16 output 2 \decoder_out
  attribute \src "asicworld/verilog/code_hdl_models_decoder_using_assign.v:13.8-13.14"
  wire input 3 \enable
  attribute \src "asicworld/verilog/code_hdl_models_decoder_using_assign.v:18.22-18.57"
  cell $pos $extend$asicworld/verilog/code_hdl_models_decoder_using_assign.v:18$2
    parameter \A_SIGNED 0
    parameter \A_WIDTH 16
    parameter \Y_WIDTH 32
    connect \A 16'0000000000000000
    connect \Y $extend$asicworld/verilog/code_hdl_models_decoder_using_assign.v:18$2_Y
  end
  attribute \src "asicworld/verilog/code_hdl_models_decoder_using_assign.v:18.34-18.48"
  cell $shl $shl$asicworld/verilog/code_hdl_models_decoder_using_assign.v:18$1
    parameter \A_SIGNED 0
    parameter \A_WIDTH 32
    parameter \B_SIGNED 0
    parameter \B_WIDTH 4
    parameter \Y_WIDTH 32
    connect \A 1
    connect \B \binary_in
    connect \Y $shl$asicworld/verilog/code_hdl_models_decoder_using_assign.v:18$1_Y
  end
  attribute \src "asicworld/verilog/code_hdl_models_decoder_using_assign.v:18.22-18.57"
  cell $mux $ternary$asicworld/verilog/code_hdl_models_decoder_using_assign.v:18$3
    parameter \WIDTH 32
    connect \A $extend$asicworld/verilog/code_hdl_models_decoder_using_assign.v:18$2_Y
    connect \B $shl$asicworld/verilog/code_hdl_models_decoder_using_assign.v:18$1_Y
    connect \S \enable
    connect \Y $ternary$asicworld/verilog/code_hdl_models_decoder_using_assign.v:18$3_Y
  end
  connect \decoder_out $ternary$asicworld/verilog/code_hdl_models_decoder_using_assign.v:18$3_Y [15:0]
end
