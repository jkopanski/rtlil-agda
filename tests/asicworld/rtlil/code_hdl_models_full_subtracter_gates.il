autoidx 7
attribute \cells_not_processed 1
attribute \src "asicworld/verilog/code_hdl_models_full_subtracter_gates.v:7.1-20.10"
module \full_subtracter_gates
  attribute \src "asicworld/verilog/code_hdl_models_full_subtracter_gates.v:14.5-14.32"
  wire $and$asicworld/verilog/code_hdl_models_full_subtracter_gates.v:14$1_Y
  attribute \src "asicworld/verilog/code_hdl_models_full_subtracter_gates.v:15.5-15.32"
  wire $and$asicworld/verilog/code_hdl_models_full_subtracter_gates.v:15$2_Y
  attribute \src "asicworld/verilog/code_hdl_models_full_subtracter_gates.v:16.5-16.28"
  wire $and$asicworld/verilog/code_hdl_models_full_subtracter_gates.v:16$3_Y
  attribute \src "asicworld/verilog/code_hdl_models_full_subtracter_gates.v:0.0-0.0"
  wire $not$asicworld/verilog/code_hdl_models_full_subtracter_gates.v:0$6_Y
  attribute \src "asicworld/verilog/code_hdl_models_full_subtracter_gates.v:18.5-18.48"
  wire $xor$asicworld/verilog/code_hdl_models_full_subtracter_gates.v:18$4_Y
  attribute \src "asicworld/verilog/code_hdl_models_full_subtracter_gates.v:18.5-18.48"
  wire $xor$asicworld/verilog/code_hdl_models_full_subtracter_gates.v:18$5_Y
  attribute \src "asicworld/verilog/code_hdl_models_full_subtracter_gates.v:9.19-9.25"
  wire output 5 \borrow
  attribute \src "asicworld/verilog/code_hdl_models_full_subtracter_gates.v:11.12-11.19"
  wire \borrow1
  attribute \src "asicworld/verilog/code_hdl_models_full_subtracter_gates.v:11.20-11.27"
  wire \borrow2
  attribute \src "asicworld/verilog/code_hdl_models_full_subtracter_gates.v:11.28-11.35"
  wire \borrow3
  attribute \src "asicworld/verilog/code_hdl_models_full_subtracter_gates.v:18.40-18.47"
  wire \borrows
  attribute \src "asicworld/verilog/code_hdl_models_full_subtracter_gates.v:9.8-9.18"
  wire output 4 \difference
  attribute \src "asicworld/verilog/code_hdl_models_full_subtracter_gates.v:11.6-11.11"
  wire \inv_x
  attribute \src "asicworld/verilog/code_hdl_models_full_subtracter_gates.v:8.7-8.8"
  wire input 1 \x
  attribute \src "asicworld/verilog/code_hdl_models_full_subtracter_gates.v:8.9-8.10"
  wire input 2 \y
  attribute \src "asicworld/verilog/code_hdl_models_full_subtracter_gates.v:8.11-8.12"
  wire input 3 \z
  attribute \src "asicworld/verilog/code_hdl_models_full_subtracter_gates.v:14.5-14.32"
  cell $and $and$asicworld/verilog/code_hdl_models_full_subtracter_gates.v:14$1
    parameter \A_SIGNED 0
    parameter \A_WIDTH 1
    parameter \B_SIGNED 0
    parameter \B_WIDTH 1
    parameter \Y_WIDTH 1
    connect \A \inv_x
    connect \B \y
    connect \Y $and$asicworld/verilog/code_hdl_models_full_subtracter_gates.v:14$1_Y
  end
  attribute \src "asicworld/verilog/code_hdl_models_full_subtracter_gates.v:15.5-15.32"
  cell $and $and$asicworld/verilog/code_hdl_models_full_subtracter_gates.v:15$2
    parameter \A_SIGNED 0
    parameter \A_WIDTH 1
    parameter \B_SIGNED 0
    parameter \B_WIDTH 1
    parameter \Y_WIDTH 1
    connect \A \inv_x
    connect \B \z
    connect \Y $and$asicworld/verilog/code_hdl_models_full_subtracter_gates.v:15$2_Y
  end
  attribute \src "asicworld/verilog/code_hdl_models_full_subtracter_gates.v:16.5-16.28"
  cell $and $and$asicworld/verilog/code_hdl_models_full_subtracter_gates.v:16$3
    parameter \A_SIGNED 0
    parameter \A_WIDTH 1
    parameter \B_SIGNED 0
    parameter \B_WIDTH 1
    parameter \Y_WIDTH 1
    connect \A \y
    connect \B \z
    connect \Y $and$asicworld/verilog/code_hdl_models_full_subtracter_gates.v:16$3_Y
  end
  attribute \src "asicworld/verilog/code_hdl_models_full_subtracter_gates.v:0.0-0.0"
  cell $not $not$asicworld/verilog/code_hdl_models_full_subtracter_gates.v:0$6
    parameter \A_SIGNED 0
    parameter \A_WIDTH 1
    parameter \Y_WIDTH 1
    connect \A \x
    connect \Y $not$asicworld/verilog/code_hdl_models_full_subtracter_gates.v:0$6_Y
  end
  attribute \src "asicworld/verilog/code_hdl_models_full_subtracter_gates.v:18.5-18.48"
  cell $xor $xor$asicworld/verilog/code_hdl_models_full_subtracter_gates.v:18$4
    parameter \A_SIGNED 0
    parameter \A_WIDTH 1
    parameter \B_SIGNED 0
    parameter \B_WIDTH 1
    parameter \Y_WIDTH 1
    connect \A \borrow1
    connect \B \borrow2
    connect \Y $xor$asicworld/verilog/code_hdl_models_full_subtracter_gates.v:18$4_Y
  end
  attribute \src "asicworld/verilog/code_hdl_models_full_subtracter_gates.v:18.5-18.48"
  cell $xor $xor$asicworld/verilog/code_hdl_models_full_subtracter_gates.v:18$5
    parameter \A_SIGNED 0
    parameter \A_WIDTH 1
    parameter \B_SIGNED 0
    parameter \B_WIDTH 1
    parameter \Y_WIDTH 1
    connect \A $xor$asicworld/verilog/code_hdl_models_full_subtracter_gates.v:18$4_Y
    connect \B \borrows
    connect \Y $xor$asicworld/verilog/code_hdl_models_full_subtracter_gates.v:18$5_Y
  end
  connect \borrow1 $and$asicworld/verilog/code_hdl_models_full_subtracter_gates.v:14$1_Y
  connect \borrow2 $and$asicworld/verilog/code_hdl_models_full_subtracter_gates.v:15$2_Y
  connect \borrow3 $and$asicworld/verilog/code_hdl_models_full_subtracter_gates.v:16$3_Y
  connect \difference $xor$asicworld/verilog/code_hdl_models_full_subtracter_gates.v:18$5_Y
  connect \inv_x $not$asicworld/verilog/code_hdl_models_full_subtracter_gates.v:0$6_Y
end
