autoidx 1
attribute \cells_not_processed 1
attribute \src "asicworld/verilog/code_verilog_tutorial_bus_con.v:1.1-8.10"
module \bus_con
  attribute \src "asicworld/verilog/code_verilog_tutorial_bus_con.v:2.19-2.20"
  wire width 4 input 1 \a
  attribute \src "asicworld/verilog/code_verilog_tutorial_bus_con.v:2.22-2.23"
  wire width 4 input 2 \b
  attribute \src "asicworld/verilog/code_verilog_tutorial_bus_con.v:3.20-3.21"
  wire width 8 output 3 \y
  connect \y { \a \b }
end
