autoidx 2
attribute \cells_not_processed 1
attribute \src "asicworld/verilog/code_verilog_tutorial_which_clock.v:1.1-12.10"
module \which_clock
  attribute \src "asicworld/verilog/code_verilog_tutorial_which_clock.v:6.1-10.13"
  wire $0\q[0:0]
  attribute \src "asicworld/verilog/code_verilog_tutorial_which_clock.v:2.11-2.12"
  wire input 4 \d
  attribute \src "asicworld/verilog/code_verilog_tutorial_which_clock.v:3.8-3.9"
  wire output 3 \q
  attribute \src "asicworld/verilog/code_verilog_tutorial_which_clock.v:2.7-2.8"
  wire input 1 \x
  attribute \src "asicworld/verilog/code_verilog_tutorial_which_clock.v:2.9-2.10"
  wire input 2 \y
  attribute \src "asicworld/verilog/code_verilog_tutorial_which_clock.v:6.1-10.13"
  process $proc$asicworld/verilog/code_verilog_tutorial_which_clock.v:6$1
    assign $0\q[0:0] \q
    attribute \src "asicworld/verilog/code_verilog_tutorial_which_clock.v:7.4-10.13"
    switch \x
      attribute \src "asicworld/verilog/code_verilog_tutorial_which_clock.v:7.8-7.9"
      case 1'1
        assign $0\q[0:0] 1'0
      attribute \src "asicworld/verilog/code_verilog_tutorial_which_clock.v:9.4-9.8"
      case 
        assign $0\q[0:0] \d
    end
    sync posedge \x
      update \q $0\q[0:0]
    sync posedge \y
      update \q $0\q[0:0]
  end
end
