autoidx 3
attribute \cells_not_processed 1
attribute \src "asicworld/verilog/code_verilog_tutorial_flip_flop.v:1.1-15.10"
module \flif_flop
  attribute \src "asicworld/verilog/code_verilog_tutorial_flip_flop.v:6.1-13.4"
  wire $0\q[0:0]
  attribute \src "asicworld/verilog/code_verilog_tutorial_flip_flop.v:8.7-8.17"
  wire $eq$asicworld/verilog/code_verilog_tutorial_flip_flop.v:8$2_Y
  attribute \src "asicworld/verilog/code_verilog_tutorial_flip_flop.v:2.7-2.10"
  wire input 1 \clk
  attribute \src "asicworld/verilog/code_verilog_tutorial_flip_flop.v:2.19-2.20"
  wire input 4 \d
  attribute \src "asicworld/verilog/code_verilog_tutorial_flip_flop.v:3.8-3.9"
  wire output 3 \q
  attribute \src "asicworld/verilog/code_verilog_tutorial_flip_flop.v:2.12-2.17"
  wire input 2 \reset
  attribute \src "asicworld/verilog/code_verilog_tutorial_flip_flop.v:8.7-8.17"
  cell $eq $eq$asicworld/verilog/code_verilog_tutorial_flip_flop.v:8$2
    parameter \A_SIGNED 0
    parameter \A_WIDTH 1
    parameter \B_SIGNED 0
    parameter \B_WIDTH 32
    parameter \Y_WIDTH 1
    connect \A \reset
    connect \B 1
    connect \Y $eq$asicworld/verilog/code_verilog_tutorial_flip_flop.v:8$2_Y
  end
  attribute \src "asicworld/verilog/code_verilog_tutorial_flip_flop.v:6.1-13.4"
  process $proc$asicworld/verilog/code_verilog_tutorial_flip_flop.v:6$1
    assign $0\q[0:0] \q
    attribute \src "asicworld/verilog/code_verilog_tutorial_flip_flop.v:8.3-12.6"
    switch $eq$asicworld/verilog/code_verilog_tutorial_flip_flop.v:8$2_Y
      attribute \src "asicworld/verilog/code_verilog_tutorial_flip_flop.v:8.7-8.17"
      case 1'1
        assign $0\q[0:0] 1'0
      attribute \src "asicworld/verilog/code_verilog_tutorial_flip_flop.v:10.7-10.11"
      case 
        assign $0\q[0:0] \d
    end
    sync posedge \clk
      update \q $0\q[0:0]
  end
end
