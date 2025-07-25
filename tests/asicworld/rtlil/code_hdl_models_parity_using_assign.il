autoidx 8
attribute \cells_not_processed 1
attribute \src "asicworld/verilog/code_hdl_models_parity_using_assign.v:7.1-21.10"
module \parity_using_assign
  attribute \src "asicworld/verilog/code_hdl_models_parity_using_assign.v:16.23-16.46"
  wire $xor$asicworld/verilog/code_hdl_models_parity_using_assign.v:16$1_Y
  attribute \src "asicworld/verilog/code_hdl_models_parity_using_assign.v:16.22-17.47"
  wire $xor$asicworld/verilog/code_hdl_models_parity_using_assign.v:16$3_Y
  attribute \src "asicworld/verilog/code_hdl_models_parity_using_assign.v:16.22-18.47"
  wire $xor$asicworld/verilog/code_hdl_models_parity_using_assign.v:16$5_Y
  attribute \src "asicworld/verilog/code_hdl_models_parity_using_assign.v:16.22-19.47"
  wire $xor$asicworld/verilog/code_hdl_models_parity_using_assign.v:16$7_Y
  attribute \src "asicworld/verilog/code_hdl_models_parity_using_assign.v:17.23-17.46"
  wire $xor$asicworld/verilog/code_hdl_models_parity_using_assign.v:17$2_Y
  attribute \src "asicworld/verilog/code_hdl_models_parity_using_assign.v:18.23-18.46"
  wire $xor$asicworld/verilog/code_hdl_models_parity_using_assign.v:18$4_Y
  attribute \src "asicworld/verilog/code_hdl_models_parity_using_assign.v:19.23-19.46"
  wire $xor$asicworld/verilog/code_hdl_models_parity_using_assign.v:19$6_Y
  attribute \src "asicworld/verilog/code_hdl_models_parity_using_assign.v:12.13-12.20"
  wire width 8 input 1 \data_in
  attribute \src "asicworld/verilog/code_hdl_models_parity_using_assign.v:11.9-11.19"
  wire output 2 \parity_out
  attribute \src "asicworld/verilog/code_hdl_models_parity_using_assign.v:16.23-16.46"
  cell $xor $xor$asicworld/verilog/code_hdl_models_parity_using_assign.v:16$1
    parameter \A_SIGNED 0
    parameter \A_WIDTH 1
    parameter \B_SIGNED 0
    parameter \B_WIDTH 1
    parameter \Y_WIDTH 1
    connect \A \data_in [0]
    connect \B \data_in [1]
    connect \Y $xor$asicworld/verilog/code_hdl_models_parity_using_assign.v:16$1_Y
  end
  attribute \src "asicworld/verilog/code_hdl_models_parity_using_assign.v:16.22-17.47"
  cell $xor $xor$asicworld/verilog/code_hdl_models_parity_using_assign.v:16$3
    parameter \A_SIGNED 0
    parameter \A_WIDTH 1
    parameter \B_SIGNED 0
    parameter \B_WIDTH 1
    parameter \Y_WIDTH 1
    connect \A $xor$asicworld/verilog/code_hdl_models_parity_using_assign.v:16$1_Y
    connect \B $xor$asicworld/verilog/code_hdl_models_parity_using_assign.v:17$2_Y
    connect \Y $xor$asicworld/verilog/code_hdl_models_parity_using_assign.v:16$3_Y
  end
  attribute \src "asicworld/verilog/code_hdl_models_parity_using_assign.v:16.22-18.47"
  cell $xor $xor$asicworld/verilog/code_hdl_models_parity_using_assign.v:16$5
    parameter \A_SIGNED 0
    parameter \A_WIDTH 1
    parameter \B_SIGNED 0
    parameter \B_WIDTH 1
    parameter \Y_WIDTH 1
    connect \A $xor$asicworld/verilog/code_hdl_models_parity_using_assign.v:16$3_Y
    connect \B $xor$asicworld/verilog/code_hdl_models_parity_using_assign.v:18$4_Y
    connect \Y $xor$asicworld/verilog/code_hdl_models_parity_using_assign.v:16$5_Y
  end
  attribute \src "asicworld/verilog/code_hdl_models_parity_using_assign.v:16.22-19.47"
  cell $xor $xor$asicworld/verilog/code_hdl_models_parity_using_assign.v:16$7
    parameter \A_SIGNED 0
    parameter \A_WIDTH 1
    parameter \B_SIGNED 0
    parameter \B_WIDTH 1
    parameter \Y_WIDTH 1
    connect \A $xor$asicworld/verilog/code_hdl_models_parity_using_assign.v:16$5_Y
    connect \B $xor$asicworld/verilog/code_hdl_models_parity_using_assign.v:19$6_Y
    connect \Y $xor$asicworld/verilog/code_hdl_models_parity_using_assign.v:16$7_Y
  end
  attribute \src "asicworld/verilog/code_hdl_models_parity_using_assign.v:17.23-17.46"
  cell $xor $xor$asicworld/verilog/code_hdl_models_parity_using_assign.v:17$2
    parameter \A_SIGNED 0
    parameter \A_WIDTH 1
    parameter \B_SIGNED 0
    parameter \B_WIDTH 1
    parameter \Y_WIDTH 1
    connect \A \data_in [2]
    connect \B \data_in [3]
    connect \Y $xor$asicworld/verilog/code_hdl_models_parity_using_assign.v:17$2_Y
  end
  attribute \src "asicworld/verilog/code_hdl_models_parity_using_assign.v:18.23-18.46"
  cell $xor $xor$asicworld/verilog/code_hdl_models_parity_using_assign.v:18$4
    parameter \A_SIGNED 0
    parameter \A_WIDTH 1
    parameter \B_SIGNED 0
    parameter \B_WIDTH 1
    parameter \Y_WIDTH 1
    connect \A \data_in [4]
    connect \B \data_in [5]
    connect \Y $xor$asicworld/verilog/code_hdl_models_parity_using_assign.v:18$4_Y
  end
  attribute \src "asicworld/verilog/code_hdl_models_parity_using_assign.v:19.23-19.46"
  cell $xor $xor$asicworld/verilog/code_hdl_models_parity_using_assign.v:19$6
    parameter \A_SIGNED 0
    parameter \A_WIDTH 1
    parameter \B_SIGNED 0
    parameter \B_WIDTH 1
    parameter \Y_WIDTH 1
    connect \A \data_in [6]
    connect \B \data_in [7]
    connect \Y $xor$asicworld/verilog/code_hdl_models_parity_using_assign.v:19$6_Y
  end
  connect \parity_out $xor$asicworld/verilog/code_hdl_models_parity_using_assign.v:16$7_Y
end
