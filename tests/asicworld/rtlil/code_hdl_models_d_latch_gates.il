autoidx 10
attribute \cells_not_processed 1
attribute \src "asicworld/verilog/code_hdl_models_d_latch_gates.v:1.1-15.10"
module \d_latch_gates
  attribute \src "asicworld/verilog/code_hdl_models_d_latch_gates.v:10.5-10.17"
  wire $and$asicworld/verilog/code_hdl_models_d_latch_gates.v:10$3_Y
  attribute \src "asicworld/verilog/code_hdl_models_d_latch_gates.v:12.5-12.18"
  wire $and$asicworld/verilog/code_hdl_models_d_latch_gates.v:12$5_Y
  attribute \src "asicworld/verilog/code_hdl_models_d_latch_gates.v:13.5-13.18"
  wire $and$asicworld/verilog/code_hdl_models_d_latch_gates.v:13$7_Y
  attribute \src "asicworld/verilog/code_hdl_models_d_latch_gates.v:9.5-9.16"
  wire $and$asicworld/verilog/code_hdl_models_d_latch_gates.v:9$1_Y
  attribute \src "asicworld/verilog/code_hdl_models_d_latch_gates.v:0.0-0.0"
  wire $not$asicworld/verilog/code_hdl_models_d_latch_gates.v:0$2_Y
  attribute \src "asicworld/verilog/code_hdl_models_d_latch_gates.v:0.0-0.0"
  wire $not$asicworld/verilog/code_hdl_models_d_latch_gates.v:0$4_Y
  attribute \src "asicworld/verilog/code_hdl_models_d_latch_gates.v:0.0-0.0"
  wire $not$asicworld/verilog/code_hdl_models_d_latch_gates.v:0$6_Y
  attribute \src "asicworld/verilog/code_hdl_models_d_latch_gates.v:0.0-0.0"
  wire $not$asicworld/verilog/code_hdl_models_d_latch_gates.v:0$8_Y
  attribute \src "asicworld/verilog/code_hdl_models_d_latch_gates.v:0.0-0.0"
  wire $not$asicworld/verilog/code_hdl_models_d_latch_gates.v:0$9_Y
  attribute \src "asicworld/verilog/code_hdl_models_d_latch_gates.v:2.9-2.12"
  wire input 2 \clk
  attribute \src "asicworld/verilog/code_hdl_models_d_latch_gates.v:2.7-2.8"
  wire input 1 \d
  attribute \src "asicworld/verilog/code_hdl_models_d_latch_gates.v:5.6-5.8"
  wire \n1
  attribute \src "asicworld/verilog/code_hdl_models_d_latch_gates.v:5.9-5.11"
  wire \n2
  attribute \src "asicworld/verilog/code_hdl_models_d_latch_gates.v:5.12-5.14"
  wire \n3
  attribute \src "asicworld/verilog/code_hdl_models_d_latch_gates.v:3.8-3.9"
  wire output 3 \q
  attribute \src "asicworld/verilog/code_hdl_models_d_latch_gates.v:3.11-3.16"
  wire output 4 \q_bar
  attribute \src "asicworld/verilog/code_hdl_models_d_latch_gates.v:10.5-10.17"
  cell $and $and$asicworld/verilog/code_hdl_models_d_latch_gates.v:10$3
    parameter \A_SIGNED 0
    parameter \A_WIDTH 1
    parameter \B_SIGNED 0
    parameter \B_WIDTH 1
    parameter \Y_WIDTH 1
    connect \A \n1
    connect \B \clk
    connect \Y $and$asicworld/verilog/code_hdl_models_d_latch_gates.v:10$3_Y
  end
  attribute \src "asicworld/verilog/code_hdl_models_d_latch_gates.v:12.5-12.18"
  cell $and $and$asicworld/verilog/code_hdl_models_d_latch_gates.v:12$5
    parameter \A_SIGNED 0
    parameter \A_WIDTH 1
    parameter \B_SIGNED 0
    parameter \B_WIDTH 1
    parameter \Y_WIDTH 1
    connect \A \q_bar
    connect \B \n2
    connect \Y $and$asicworld/verilog/code_hdl_models_d_latch_gates.v:12$5_Y
  end
  attribute \src "asicworld/verilog/code_hdl_models_d_latch_gates.v:13.5-13.18"
  cell $and $and$asicworld/verilog/code_hdl_models_d_latch_gates.v:13$7
    parameter \A_SIGNED 0
    parameter \A_WIDTH 1
    parameter \B_SIGNED 0
    parameter \B_WIDTH 1
    parameter \Y_WIDTH 1
    connect \A \q
    connect \B \n3
    connect \Y $and$asicworld/verilog/code_hdl_models_d_latch_gates.v:13$7_Y
  end
  attribute \src "asicworld/verilog/code_hdl_models_d_latch_gates.v:9.5-9.16"
  cell $and $and$asicworld/verilog/code_hdl_models_d_latch_gates.v:9$1
    parameter \A_SIGNED 0
    parameter \A_WIDTH 1
    parameter \B_SIGNED 0
    parameter \B_WIDTH 1
    parameter \Y_WIDTH 1
    connect \A \d
    connect \B \clk
    connect \Y $and$asicworld/verilog/code_hdl_models_d_latch_gates.v:9$1_Y
  end
  attribute \src "asicworld/verilog/code_hdl_models_d_latch_gates.v:0.0-0.0"
  cell $not $not$asicworld/verilog/code_hdl_models_d_latch_gates.v:0$2
    parameter \A_SIGNED 0
    parameter \A_WIDTH 1
    parameter \Y_WIDTH 1
    connect \A $and$asicworld/verilog/code_hdl_models_d_latch_gates.v:9$1_Y
    connect \Y $not$asicworld/verilog/code_hdl_models_d_latch_gates.v:0$2_Y
  end
  attribute \src "asicworld/verilog/code_hdl_models_d_latch_gates.v:0.0-0.0"
  cell $not $not$asicworld/verilog/code_hdl_models_d_latch_gates.v:0$4
    parameter \A_SIGNED 0
    parameter \A_WIDTH 1
    parameter \Y_WIDTH 1
    connect \A $and$asicworld/verilog/code_hdl_models_d_latch_gates.v:10$3_Y
    connect \Y $not$asicworld/verilog/code_hdl_models_d_latch_gates.v:0$4_Y
  end
  attribute \src "asicworld/verilog/code_hdl_models_d_latch_gates.v:0.0-0.0"
  cell $not $not$asicworld/verilog/code_hdl_models_d_latch_gates.v:0$6
    parameter \A_SIGNED 0
    parameter \A_WIDTH 1
    parameter \Y_WIDTH 1
    connect \A $and$asicworld/verilog/code_hdl_models_d_latch_gates.v:12$5_Y
    connect \Y $not$asicworld/verilog/code_hdl_models_d_latch_gates.v:0$6_Y
  end
  attribute \src "asicworld/verilog/code_hdl_models_d_latch_gates.v:0.0-0.0"
  cell $not $not$asicworld/verilog/code_hdl_models_d_latch_gates.v:0$8
    parameter \A_SIGNED 0
    parameter \A_WIDTH 1
    parameter \Y_WIDTH 1
    connect \A $and$asicworld/verilog/code_hdl_models_d_latch_gates.v:13$7_Y
    connect \Y $not$asicworld/verilog/code_hdl_models_d_latch_gates.v:0$8_Y
  end
  attribute \src "asicworld/verilog/code_hdl_models_d_latch_gates.v:0.0-0.0"
  cell $not $not$asicworld/verilog/code_hdl_models_d_latch_gates.v:0$9
    parameter \A_SIGNED 0
    parameter \A_WIDTH 1
    parameter \Y_WIDTH 1
    connect \A \d
    connect \Y $not$asicworld/verilog/code_hdl_models_d_latch_gates.v:0$9_Y
  end
  connect \n2 $not$asicworld/verilog/code_hdl_models_d_latch_gates.v:0$2_Y
  connect \n3 $not$asicworld/verilog/code_hdl_models_d_latch_gates.v:0$4_Y
  connect \q $not$asicworld/verilog/code_hdl_models_d_latch_gates.v:0$6_Y
  connect \q_bar $not$asicworld/verilog/code_hdl_models_d_latch_gates.v:0$8_Y
  connect \n1 $not$asicworld/verilog/code_hdl_models_d_latch_gates.v:0$9_Y
end
