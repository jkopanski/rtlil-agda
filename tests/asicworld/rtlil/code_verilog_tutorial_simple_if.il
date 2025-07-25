autoidx 2
attribute \cells_not_processed 1
attribute \src "asicworld/verilog/code_verilog_tutorial_simple_if.v:1.1-11.10"
module \simple_if
  attribute \src "asicworld/verilog/code_verilog_tutorial_simple_if.v:6.1-9.4"
  wire $0\latch[0:0]
  attribute \src "asicworld/verilog/code_verilog_tutorial_simple_if.v:4.13-4.16"
  wire \din
  attribute \src "asicworld/verilog/code_verilog_tutorial_simple_if.v:4.6-4.12"
  wire \enable
  attribute \src "asicworld/verilog/code_verilog_tutorial_simple_if.v:3.5-3.10"
  wire \latch
  attribute \src "asicworld/verilog/code_verilog_tutorial_simple_if.v:6.1-9.4"
  process $proc$asicworld/verilog/code_verilog_tutorial_simple_if.v:6$1
    assign $0\latch[0:0] \latch
    attribute \src "asicworld/verilog/code_verilog_tutorial_simple_if.v:7.1-9.4"
    switch \enable
      attribute \src "asicworld/verilog/code_verilog_tutorial_simple_if.v:7.5-7.11"
      case 1'1
        assign $0\latch[0:0] \din
      case 
    end
    sync always
      update \latch $0\latch[0:0]
  end
end
