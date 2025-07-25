autoidx 2
attribute \cells_not_processed 1
attribute \src "asicworld/verilog/code_verilog_tutorial_mux_21.v:1.1-9.10"
module \mux_21
  attribute \src "asicworld/verilog/code_verilog_tutorial_mux_21.v:7.18-7.31"
  wire $ternary$asicworld/verilog/code_verilog_tutorial_mux_21.v:7$1_Y
  attribute \src "asicworld/verilog/code_verilog_tutorial_mux_21.v:2.13-2.14"
  wire input 1 \a
  attribute \src "asicworld/verilog/code_verilog_tutorial_mux_21.v:2.16-2.17"
  wire input 2 \b
  attribute \src "asicworld/verilog/code_verilog_tutorial_mux_21.v:4.13-4.16"
  wire input 3 \sel
  attribute \src "asicworld/verilog/code_verilog_tutorial_mux_21.v:3.14-3.15"
  wire output 4 \y
  attribute \src "asicworld/verilog/code_verilog_tutorial_mux_21.v:7.18-7.31"
  cell $mux $ternary$asicworld/verilog/code_verilog_tutorial_mux_21.v:7$1
    parameter \WIDTH 1
    connect \A \a
    connect \B \b
    connect \S \sel
    connect \Y $ternary$asicworld/verilog/code_verilog_tutorial_mux_21.v:7$1_Y
  end
  connect \y $ternary$asicworld/verilog/code_verilog_tutorial_mux_21.v:7$1_Y
end
