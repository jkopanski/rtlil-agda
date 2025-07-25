autoidx 4
attribute \cells_not_processed 1
attribute \src "asicworld/verilog/code_verilog_tutorial_parity.v:9.1-41.10"
module \parity
  attribute \src "asicworld/verilog/code_verilog_tutorial_parity.v:35.5-35.19"
  wire $xor$asicworld/verilog/code_verilog_tutorial_parity.v:35$1_Y
  attribute \src "asicworld/verilog/code_verilog_tutorial_parity.v:37.5-37.19"
  wire $xor$asicworld/verilog/code_verilog_tutorial_parity.v:37$2_Y
  attribute \src "asicworld/verilog/code_verilog_tutorial_parity.v:39.5-39.23"
  wire $xor$asicworld/verilog/code_verilog_tutorial_parity.v:39$3_Y
  attribute \src "asicworld/verilog/code_verilog_tutorial_parity.v:18.13-18.14"
  wire input 1 \a
  attribute \src "asicworld/verilog/code_verilog_tutorial_parity.v:19.13-19.14"
  wire input 2 \b
  attribute \src "asicworld/verilog/code_verilog_tutorial_parity.v:20.13-20.14"
  wire input 3 \c
  attribute \src "asicworld/verilog/code_verilog_tutorial_parity.v:21.13-21.14"
  wire input 4 \d
  attribute \src "asicworld/verilog/code_verilog_tutorial_parity.v:31.13-31.18"
  wire \out_0
  attribute \src "asicworld/verilog/code_verilog_tutorial_parity.v:32.13-32.18"
  wire \out_1
  attribute \src "asicworld/verilog/code_verilog_tutorial_parity.v:23.13-23.14"
  wire output 5 \y
  attribute \src "asicworld/verilog/code_verilog_tutorial_parity.v:35.5-35.19"
  cell $xor $xor$asicworld/verilog/code_verilog_tutorial_parity.v:35$1
    parameter \A_SIGNED 0
    parameter \A_WIDTH 1
    parameter \B_SIGNED 0
    parameter \B_WIDTH 1
    parameter \Y_WIDTH 1
    connect \A \a
    connect \B \b
    connect \Y $xor$asicworld/verilog/code_verilog_tutorial_parity.v:35$1_Y
  end
  attribute \src "asicworld/verilog/code_verilog_tutorial_parity.v:37.5-37.19"
  cell $xor $xor$asicworld/verilog/code_verilog_tutorial_parity.v:37$2
    parameter \A_SIGNED 0
    parameter \A_WIDTH 1
    parameter \B_SIGNED 0
    parameter \B_WIDTH 1
    parameter \Y_WIDTH 1
    connect \A \c
    connect \B \d
    connect \Y $xor$asicworld/verilog/code_verilog_tutorial_parity.v:37$2_Y
  end
  attribute \src "asicworld/verilog/code_verilog_tutorial_parity.v:39.5-39.23"
  cell $xor $xor$asicworld/verilog/code_verilog_tutorial_parity.v:39$3
    parameter \A_SIGNED 0
    parameter \A_WIDTH 1
    parameter \B_SIGNED 0
    parameter \B_WIDTH 1
    parameter \Y_WIDTH 1
    connect \A \out_0
    connect \B \out_1
    connect \Y $xor$asicworld/verilog/code_verilog_tutorial_parity.v:39$3_Y
  end
  connect \out_0 $xor$asicworld/verilog/code_verilog_tutorial_parity.v:35$1_Y
  connect \out_1 $xor$asicworld/verilog/code_verilog_tutorial_parity.v:37$2_Y
  connect \y $xor$asicworld/verilog/code_verilog_tutorial_parity.v:39$3_Y
end
