autoidx 3
attribute \cells_not_processed 1
attribute \src "asicworld/verilog/code_hdl_models_half_adder_gates.v:7.1-14.10"
module \half_adder_gates
  attribute \src "asicworld/verilog/code_hdl_models_half_adder_gates.v:11.5-11.24"
  wire $and$asicworld/verilog/code_hdl_models_half_adder_gates.v:11$1_Y
  attribute \src "asicworld/verilog/code_hdl_models_half_adder_gates.v:12.5-12.20"
  wire $xor$asicworld/verilog/code_hdl_models_half_adder_gates.v:12$2_Y
  attribute \src "asicworld/verilog/code_hdl_models_half_adder_gates.v:9.12-9.17"
  wire output 4 \carry
  attribute \src "asicworld/verilog/code_hdl_models_half_adder_gates.v:9.8-9.11"
  wire output 3 \sum
  attribute \src "asicworld/verilog/code_hdl_models_half_adder_gates.v:8.7-8.8"
  wire input 1 \x
  attribute \src "asicworld/verilog/code_hdl_models_half_adder_gates.v:8.9-8.10"
  wire input 2 \y
  attribute \src "asicworld/verilog/code_hdl_models_half_adder_gates.v:11.5-11.24"
  cell $and $and$asicworld/verilog/code_hdl_models_half_adder_gates.v:11$1
    parameter \A_SIGNED 0
    parameter \A_WIDTH 1
    parameter \B_SIGNED 0
    parameter \B_WIDTH 1
    parameter \Y_WIDTH 1
    connect \A \x
    connect \B \y
    connect \Y $and$asicworld/verilog/code_hdl_models_half_adder_gates.v:11$1_Y
  end
  attribute \src "asicworld/verilog/code_hdl_models_half_adder_gates.v:12.5-12.20"
  cell $xor $xor$asicworld/verilog/code_hdl_models_half_adder_gates.v:12$2
    parameter \A_SIGNED 0
    parameter \A_WIDTH 1
    parameter \B_SIGNED 0
    parameter \B_WIDTH 1
    parameter \Y_WIDTH 1
    connect \A \x
    connect \B \y
    connect \Y $xor$asicworld/verilog/code_hdl_models_half_adder_gates.v:12$2_Y
  end
  connect \carry $and$asicworld/verilog/code_hdl_models_half_adder_gates.v:11$1_Y
  connect \sum $xor$asicworld/verilog/code_hdl_models_half_adder_gates.v:12$2_Y
end
