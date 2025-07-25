autoidx 3
attribute \cells_not_processed 1
attribute \src "asicworld/verilog/code_verilog_tutorial_d_ff.v:2.1-14.10"
module \d_ff
  attribute \src "asicworld/verilog/code_verilog_tutorial_d_ff.v:8.1-12.4"
  wire $0\q[0:0]
  attribute \src "asicworld/verilog/code_verilog_tutorial_d_ff.v:8.1-12.4"
  wire $0\q_bar[0:0]
  attribute \src "asicworld/verilog/code_verilog_tutorial_d_ff.v:11.12-11.14"
  wire $logic_not$asicworld/verilog/code_verilog_tutorial_d_ff.v:11$2_Y
  attribute \src "asicworld/verilog/code_verilog_tutorial_d_ff.v:3.10-3.13"
  wire input 2 \clk
  attribute \src "asicworld/verilog/code_verilog_tutorial_d_ff.v:3.7-3.8"
  wire input 1 \d
  attribute \src "asicworld/verilog/code_verilog_tutorial_d_ff.v:4.8-4.9"
  wire output 3 \q
  attribute \src "asicworld/verilog/code_verilog_tutorial_d_ff.v:4.11-4.16"
  wire output 4 \q_bar
  attribute \src "asicworld/verilog/code_verilog_tutorial_d_ff.v:11.12-11.14"
  cell $logic_not $logic_not$asicworld/verilog/code_verilog_tutorial_d_ff.v:11$2
    parameter \A_SIGNED 0
    parameter \A_WIDTH 1
    parameter \Y_WIDTH 1
    connect \A \d
    connect \Y $logic_not$asicworld/verilog/code_verilog_tutorial_d_ff.v:11$2_Y
  end
  attribute \src "asicworld/verilog/code_verilog_tutorial_d_ff.v:8.1-12.4"
  process $proc$asicworld/verilog/code_verilog_tutorial_d_ff.v:8$1
    assign { } { }
    assign { } { }
    assign $0\q[0:0] \d
    assign $0\q_bar[0:0] $logic_not$asicworld/verilog/code_verilog_tutorial_d_ff.v:11$2_Y
    sync posedge \clk
      update \q $0\q[0:0]
      update \q_bar $0\q_bar[0:0]
  end
end
