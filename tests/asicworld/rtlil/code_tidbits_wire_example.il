autoidx 2
attribute \cells_not_processed 1
attribute \src "asicworld/verilog/code_tidbits_wire_example.v:1.1-9.10"
module \wire_example
  attribute \src "asicworld/verilog/code_tidbits_wire_example.v:7.14-7.19"
  wire $and$asicworld/verilog/code_tidbits_wire_example.v:7$1_Y
  attribute \src "asicworld/verilog/code_tidbits_wire_example.v:2.9-2.10"
  wire input 1 \a
  attribute \src "asicworld/verilog/code_tidbits_wire_example.v:2.12-2.13"
  wire input 2 \b
  attribute \src "asicworld/verilog/code_tidbits_wire_example.v:3.10-3.11"
  wire output 3 \y
  attribute \src "asicworld/verilog/code_tidbits_wire_example.v:7.14-7.19"
  cell $and $and$asicworld/verilog/code_tidbits_wire_example.v:7$1
    parameter \A_SIGNED 0
    parameter \A_WIDTH 1
    parameter \B_SIGNED 0
    parameter \B_WIDTH 1
    parameter \Y_WIDTH 1
    connect \A \a
    connect \B \b
    connect \Y $and$asicworld/verilog/code_tidbits_wire_example.v:7$1_Y
  end
  connect \y $and$asicworld/verilog/code_tidbits_wire_example.v:7$1_Y
end
