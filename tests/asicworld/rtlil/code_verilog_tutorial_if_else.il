autoidx 2
attribute \cells_not_processed 1
attribute \src "asicworld/verilog/code_verilog_tutorial_if_else.v:1.1-13.10"
module \if_else
  attribute \src "asicworld/verilog/code_verilog_tutorial_if_else.v:6.1-11.4"
  wire $0\dff[0:0]
  attribute \src "asicworld/verilog/code_verilog_tutorial_if_else.v:4.6-4.9"
  wire \clk
  attribute \src "asicworld/verilog/code_verilog_tutorial_if_else.v:3.5-3.8"
  wire \dff
  attribute \src "asicworld/verilog/code_verilog_tutorial_if_else.v:4.10-4.13"
  wire \din
  attribute \src "asicworld/verilog/code_verilog_tutorial_if_else.v:4.14-4.19"
  wire \reset
  attribute \src "asicworld/verilog/code_verilog_tutorial_if_else.v:6.1-11.4"
  process $proc$asicworld/verilog/code_verilog_tutorial_if_else.v:6$1
    assign $0\dff[0:0] \dff
    attribute \src "asicworld/verilog/code_verilog_tutorial_if_else.v:7.1-11.4"
    switch \reset
      attribute \src "asicworld/verilog/code_verilog_tutorial_if_else.v:7.5-7.10"
      case 1'1
        assign $0\dff[0:0] 1'0
      attribute \src "asicworld/verilog/code_verilog_tutorial_if_else.v:9.5-9.9"
      case 
        assign $0\dff[0:0] \din
    end
    sync posedge \clk
      update \dff $0\dff[0:0]
  end
end
