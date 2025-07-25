autoidx 4
attribute \cells_not_processed 1
attribute \src "asicworld/verilog/code_verilog_tutorial_n_out_primitive.v:1.1-13.10"
module \n_out_primitive
  attribute \src "asicworld/verilog/code_verilog_tutorial_n_out_primitive.v:0.0-0.0"
  wire $not$asicworld/verilog/code_verilog_tutorial_n_out_primitive.v:0$1_Y
  attribute \src "asicworld/verilog/code_verilog_tutorial_n_out_primitive.v:0.0-0.0"
  wire $not$asicworld/verilog/code_verilog_tutorial_n_out_primitive.v:0$2_Y
  attribute \src "asicworld/verilog/code_verilog_tutorial_n_out_primitive.v:0.0-0.0"
  wire $not$asicworld/verilog/code_verilog_tutorial_n_out_primitive.v:0$3_Y
  attribute \src "asicworld/verilog/code_verilog_tutorial_n_out_primitive.v:4.6-4.8"
  wire \in
  attribute \src "asicworld/verilog/code_verilog_tutorial_n_out_primitive.v:3.6-3.9"
  wire \out
  attribute \src "asicworld/verilog/code_verilog_tutorial_n_out_primitive.v:3.10-3.15"
  wire \out_0
  attribute \src "asicworld/verilog/code_verilog_tutorial_n_out_primitive.v:3.16-3.21"
  wire \out_1
  attribute \src "asicworld/verilog/code_verilog_tutorial_n_out_primitive.v:3.22-3.27"
  wire \out_2
  attribute \src "asicworld/verilog/code_verilog_tutorial_n_out_primitive.v:3.28-3.33"
  wire \out_3
  attribute \src "asicworld/verilog/code_verilog_tutorial_n_out_primitive.v:3.34-3.39"
  wire \out_a
  attribute \src "asicworld/verilog/code_verilog_tutorial_n_out_primitive.v:3.40-3.45"
  wire \out_b
  attribute \src "asicworld/verilog/code_verilog_tutorial_n_out_primitive.v:3.46-3.51"
  wire \out_c
  attribute \src "asicworld/verilog/code_verilog_tutorial_n_out_primitive.v:0.0-0.0"
  cell $not $not$asicworld/verilog/code_verilog_tutorial_n_out_primitive.v:0$1
    parameter \A_SIGNED 0
    parameter \A_WIDTH 1
    parameter \Y_WIDTH 1
    connect \A \in
    connect \Y $not$asicworld/verilog/code_verilog_tutorial_n_out_primitive.v:0$1_Y
  end
  attribute \src "asicworld/verilog/code_verilog_tutorial_n_out_primitive.v:0.0-0.0"
  cell $not $not$asicworld/verilog/code_verilog_tutorial_n_out_primitive.v:0$2
    parameter \A_SIGNED 0
    parameter \A_WIDTH 1
    parameter \Y_WIDTH 1
    connect \A \in
    connect \Y $not$asicworld/verilog/code_verilog_tutorial_n_out_primitive.v:0$2_Y
  end
  attribute \src "asicworld/verilog/code_verilog_tutorial_n_out_primitive.v:0.0-0.0"
  cell $not $not$asicworld/verilog/code_verilog_tutorial_n_out_primitive.v:0$3
    parameter \A_SIGNED 0
    parameter \A_WIDTH 1
    parameter \Y_WIDTH 1
    connect \A \in
    connect \Y $not$asicworld/verilog/code_verilog_tutorial_n_out_primitive.v:0$3_Y
  end
  connect \out \in
  connect \out_0 \in
  connect \out_1 \in
  connect \out_2 \in
  connect \out_3 \in
  connect \out_a $not$asicworld/verilog/code_verilog_tutorial_n_out_primitive.v:0$1_Y
  connect \out_b $not$asicworld/verilog/code_verilog_tutorial_n_out_primitive.v:0$2_Y
  connect \out_c $not$asicworld/verilog/code_verilog_tutorial_n_out_primitive.v:0$3_Y
end
