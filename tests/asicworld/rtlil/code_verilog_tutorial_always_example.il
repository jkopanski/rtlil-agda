autoidx 2
attribute \cells_not_processed 1
attribute \src "asicworld/verilog/code_verilog_tutorial_always_example.v:1.1-11.10"
module \always_example
  attribute \src "asicworld/verilog/code_verilog_tutorial_always_example.v:4.1-9.4"
  wire $0\data[0:0]
  attribute \src "asicworld/verilog/code_verilog_tutorial_always_example.v:2.5-2.8"
  wire \clk
  attribute \src "asicworld/verilog/code_verilog_tutorial_always_example.v:2.27-2.31"
  wire \data
  attribute \src "asicworld/verilog/code_verilog_tutorial_always_example.v:2.15-2.21"
  wire \enable
  attribute \src "asicworld/verilog/code_verilog_tutorial_always_example.v:2.22-2.26"
  wire \q_in
  attribute \src "asicworld/verilog/code_verilog_tutorial_always_example.v:2.9-2.14"
  wire \reset
  attribute \src "asicworld/verilog/code_verilog_tutorial_always_example.v:4.1-9.4"
  process $proc$asicworld/verilog/code_verilog_tutorial_always_example.v:4$1
    assign $0\data[0:0] \data
    attribute \src "asicworld/verilog/code_verilog_tutorial_always_example.v:5.1-9.4"
    switch \reset
      attribute \src "asicworld/verilog/code_verilog_tutorial_always_example.v:5.5-5.10"
      case 1'1
        assign $0\data[0:0] 1'0
      attribute \src "asicworld/verilog/code_verilog_tutorial_always_example.v:7.5-7.9"
      case 
        attribute \src "asicworld/verilog/code_verilog_tutorial_always_example.v:7.10-9.4"
        switch \enable
          attribute \src "asicworld/verilog/code_verilog_tutorial_always_example.v:7.14-7.20"
          case 1'1
            assign $0\data[0:0] \q_in
          case 
        end
    end
    sync posedge \clk
      update \data $0\data[0:0]
  end
end
