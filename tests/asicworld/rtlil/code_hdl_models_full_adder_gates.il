autoidx 8
attribute \cells_not_processed 1
attribute \src "asicworld/verilog/code_hdl_models_full_adder_gates.v:7.1-18.10"
module \full_adder_gates
  attribute \src "asicworld/verilog/code_hdl_models_full_adder_gates.v:12.5-12.22"
  wire $and$asicworld/verilog/code_hdl_models_full_adder_gates.v:12$1_Y
  attribute \src "asicworld/verilog/code_hdl_models_full_adder_gates.v:13.5-13.22"
  wire $and$asicworld/verilog/code_hdl_models_full_adder_gates.v:13$2_Y
  attribute \src "asicworld/verilog/code_hdl_models_full_adder_gates.v:14.5-14.22"
  wire $and$asicworld/verilog/code_hdl_models_full_adder_gates.v:14$3_Y
  attribute \src "asicworld/verilog/code_hdl_models_full_adder_gates.v:15.5-15.34"
  wire $or$asicworld/verilog/code_hdl_models_full_adder_gates.v:15$4_Y
  attribute \src "asicworld/verilog/code_hdl_models_full_adder_gates.v:15.5-15.34"
  wire $or$asicworld/verilog/code_hdl_models_full_adder_gates.v:15$5_Y
  attribute \src "asicworld/verilog/code_hdl_models_full_adder_gates.v:16.5-16.22"
  wire $xor$asicworld/verilog/code_hdl_models_full_adder_gates.v:16$6_Y
  attribute \src "asicworld/verilog/code_hdl_models_full_adder_gates.v:16.5-16.22"
  wire $xor$asicworld/verilog/code_hdl_models_full_adder_gates.v:16$7_Y
  attribute \src "asicworld/verilog/code_hdl_models_full_adder_gates.v:10.6-10.10"
  wire \and1
  attribute \src "asicworld/verilog/code_hdl_models_full_adder_gates.v:10.11-10.15"
  wire \and2
  attribute \src "asicworld/verilog/code_hdl_models_full_adder_gates.v:10.16-10.20"
  wire \and3
  attribute \src "asicworld/verilog/code_hdl_models_full_adder_gates.v:9.12-9.17"
  wire output 5 \carry
  attribute \src "asicworld/verilog/code_hdl_models_full_adder_gates.v:9.8-9.11"
  wire output 4 \sum
  attribute \src "asicworld/verilog/code_hdl_models_full_adder_gates.v:10.21-10.25"
  wire \sum1
  attribute \src "asicworld/verilog/code_hdl_models_full_adder_gates.v:8.7-8.8"
  wire input 1 \x
  attribute \src "asicworld/verilog/code_hdl_models_full_adder_gates.v:8.9-8.10"
  wire input 2 \y
  attribute \src "asicworld/verilog/code_hdl_models_full_adder_gates.v:8.11-8.12"
  wire input 3 \z
  attribute \src "asicworld/verilog/code_hdl_models_full_adder_gates.v:12.5-12.22"
  cell $and $and$asicworld/verilog/code_hdl_models_full_adder_gates.v:12$1
    parameter \A_SIGNED 0
    parameter \A_WIDTH 1
    parameter \B_SIGNED 0
    parameter \B_WIDTH 1
    parameter \Y_WIDTH 1
    connect \A \x
    connect \B \y
    connect \Y $and$asicworld/verilog/code_hdl_models_full_adder_gates.v:12$1_Y
  end
  attribute \src "asicworld/verilog/code_hdl_models_full_adder_gates.v:13.5-13.22"
  cell $and $and$asicworld/verilog/code_hdl_models_full_adder_gates.v:13$2
    parameter \A_SIGNED 0
    parameter \A_WIDTH 1
    parameter \B_SIGNED 0
    parameter \B_WIDTH 1
    parameter \Y_WIDTH 1
    connect \A \x
    connect \B \z
    connect \Y $and$asicworld/verilog/code_hdl_models_full_adder_gates.v:13$2_Y
  end
  attribute \src "asicworld/verilog/code_hdl_models_full_adder_gates.v:14.5-14.22"
  cell $and $and$asicworld/verilog/code_hdl_models_full_adder_gates.v:14$3
    parameter \A_SIGNED 0
    parameter \A_WIDTH 1
    parameter \B_SIGNED 0
    parameter \B_WIDTH 1
    parameter \Y_WIDTH 1
    connect \A \y
    connect \B \z
    connect \Y $and$asicworld/verilog/code_hdl_models_full_adder_gates.v:14$3_Y
  end
  attribute \src "asicworld/verilog/code_hdl_models_full_adder_gates.v:15.5-15.34"
  cell $or $or$asicworld/verilog/code_hdl_models_full_adder_gates.v:15$4
    parameter \A_SIGNED 0
    parameter \A_WIDTH 1
    parameter \B_SIGNED 0
    parameter \B_WIDTH 1
    parameter \Y_WIDTH 1
    connect \A \and1
    connect \B \and2
    connect \Y $or$asicworld/verilog/code_hdl_models_full_adder_gates.v:15$4_Y
  end
  attribute \src "asicworld/verilog/code_hdl_models_full_adder_gates.v:15.5-15.34"
  cell $or $or$asicworld/verilog/code_hdl_models_full_adder_gates.v:15$5
    parameter \A_SIGNED 0
    parameter \A_WIDTH 1
    parameter \B_SIGNED 0
    parameter \B_WIDTH 1
    parameter \Y_WIDTH 1
    connect \A $or$asicworld/verilog/code_hdl_models_full_adder_gates.v:15$4_Y
    connect \B \and3
    connect \Y $or$asicworld/verilog/code_hdl_models_full_adder_gates.v:15$5_Y
  end
  attribute \src "asicworld/verilog/code_hdl_models_full_adder_gates.v:16.5-16.22"
  cell $xor $xor$asicworld/verilog/code_hdl_models_full_adder_gates.v:16$6
    parameter \A_SIGNED 0
    parameter \A_WIDTH 1
    parameter \B_SIGNED 0
    parameter \B_WIDTH 1
    parameter \Y_WIDTH 1
    connect \A \x
    connect \B \y
    connect \Y $xor$asicworld/verilog/code_hdl_models_full_adder_gates.v:16$6_Y
  end
  attribute \src "asicworld/verilog/code_hdl_models_full_adder_gates.v:16.5-16.22"
  cell $xor $xor$asicworld/verilog/code_hdl_models_full_adder_gates.v:16$7
    parameter \A_SIGNED 0
    parameter \A_WIDTH 1
    parameter \B_SIGNED 0
    parameter \B_WIDTH 1
    parameter \Y_WIDTH 1
    connect \A $xor$asicworld/verilog/code_hdl_models_full_adder_gates.v:16$6_Y
    connect \B \z
    connect \Y $xor$asicworld/verilog/code_hdl_models_full_adder_gates.v:16$7_Y
  end
  connect \and1 $and$asicworld/verilog/code_hdl_models_full_adder_gates.v:12$1_Y
  connect \and2 $and$asicworld/verilog/code_hdl_models_full_adder_gates.v:13$2_Y
  connect \and3 $and$asicworld/verilog/code_hdl_models_full_adder_gates.v:14$3_Y
  connect \carry $or$asicworld/verilog/code_hdl_models_full_adder_gates.v:15$5_Y
  connect \sum $xor$asicworld/verilog/code_hdl_models_full_adder_gates.v:16$7_Y
end
