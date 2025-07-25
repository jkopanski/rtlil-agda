autoidx 3
attribute \cells_not_processed 1
attribute \src "asicworld/verilog/code_hdl_models_encoder_4to2_gates.v:1.1-8.10"
module \encoder_4to2_gates
  attribute \src "asicworld/verilog/code_hdl_models_encoder_4to2_gates.v:5.4-5.19"
  wire $or$asicworld/verilog/code_hdl_models_encoder_4to2_gates.v:5$1_Y
  attribute \src "asicworld/verilog/code_hdl_models_encoder_4to2_gates.v:6.4-6.19"
  wire $or$asicworld/verilog/code_hdl_models_encoder_4to2_gates.v:6$2_Y
  attribute \src "asicworld/verilog/code_hdl_models_encoder_4to2_gates.v:2.7-2.9"
  wire input 1 \i0
  attribute \src "asicworld/verilog/code_hdl_models_encoder_4to2_gates.v:2.10-2.12"
  wire input 2 \i1
  attribute \src "asicworld/verilog/code_hdl_models_encoder_4to2_gates.v:2.13-2.15"
  wire input 3 \i2
  attribute \src "asicworld/verilog/code_hdl_models_encoder_4to2_gates.v:2.16-2.18"
  wire input 4 \i3
  attribute \src "asicworld/verilog/code_hdl_models_encoder_4to2_gates.v:3.14-3.15"
  wire width 2 output 5 \y
  attribute \src "asicworld/verilog/code_hdl_models_encoder_4to2_gates.v:5.4-5.19"
  cell $or $or$asicworld/verilog/code_hdl_models_encoder_4to2_gates.v:5$1
    parameter \A_SIGNED 0
    parameter \A_WIDTH 1
    parameter \B_SIGNED 0
    parameter \B_WIDTH 1
    parameter \Y_WIDTH 1
    connect \A \i1
    connect \B \i3
    connect \Y $or$asicworld/verilog/code_hdl_models_encoder_4to2_gates.v:5$1_Y
  end
  attribute \src "asicworld/verilog/code_hdl_models_encoder_4to2_gates.v:6.4-6.19"
  cell $or $or$asicworld/verilog/code_hdl_models_encoder_4to2_gates.v:6$2
    parameter \A_SIGNED 0
    parameter \A_WIDTH 1
    parameter \B_SIGNED 0
    parameter \B_WIDTH 1
    parameter \Y_WIDTH 1
    connect \A \i2
    connect \B \i3
    connect \Y $or$asicworld/verilog/code_hdl_models_encoder_4to2_gates.v:6$2_Y
  end
  connect \y [0] $or$asicworld/verilog/code_hdl_models_encoder_4to2_gates.v:5$1_Y
  connect \y [1] $or$asicworld/verilog/code_hdl_models_encoder_4to2_gates.v:6$2_Y
end
