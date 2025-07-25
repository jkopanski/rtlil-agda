autoidx 2
attribute \cells_not_processed 1
attribute \src "asicworld/verilog/code_verilog_tutorial_multiply.v:1.1-8.10"
module \muliply
  attribute \src "asicworld/verilog/code_verilog_tutorial_multiply.v:6.25-6.31"
  wire width 5 $shl$asicworld/verilog/code_verilog_tutorial_multiply.v:6$1_Y
  attribute \src "asicworld/verilog/code_verilog_tutorial_multiply.v:2.19-2.20"
  wire width 4 input 1 \a
  attribute \src "asicworld/verilog/code_verilog_tutorial_multiply.v:3.20-3.27"
  wire width 5 output 2 \product
  attribute \src "asicworld/verilog/code_verilog_tutorial_multiply.v:6.25-6.31"
  cell $shl $shl$asicworld/verilog/code_verilog_tutorial_multiply.v:6$1
    parameter \A_SIGNED 0
    parameter \A_WIDTH 4
    parameter \B_SIGNED 0
    parameter \B_WIDTH 32
    parameter \Y_WIDTH 5
    connect \A \a
    connect \B 1
    connect \Y $shl$asicworld/verilog/code_verilog_tutorial_multiply.v:6$1_Y
  end
  connect \product $shl$asicworld/verilog/code_verilog_tutorial_multiply.v:6$1_Y
end
