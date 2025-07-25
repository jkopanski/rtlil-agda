autoidx 2
attribute \cells_not_processed 1
attribute \src "asicworld/verilog/code_verilog_tutorial_tri_buf.v:1.1-9.10"
module \tri_buf
  attribute \src "asicworld/verilog/code_verilog_tutorial_tri_buf.v:7.12-7.31"
  wire $ternary$asicworld/verilog/code_verilog_tutorial_tri_buf.v:7$1_Y
  attribute \src "asicworld/verilog/code_verilog_tutorial_tri_buf.v:2.8-2.9"
  wire input 1 \a
  attribute \src "asicworld/verilog/code_verilog_tutorial_tri_buf.v:3.9-3.10"
  wire output 2 \b
  attribute \src "asicworld/verilog/code_verilog_tutorial_tri_buf.v:4.8-4.14"
  wire input 3 \enable
  attribute \src "asicworld/verilog/code_verilog_tutorial_tri_buf.v:7.12-7.31"
  cell $mux $ternary$asicworld/verilog/code_verilog_tutorial_tri_buf.v:7$1
    parameter \WIDTH 1
    connect \A 1'z
    connect \B \a
    connect \S \enable
    connect \Y $ternary$asicworld/verilog/code_verilog_tutorial_tri_buf.v:7$1_Y
  end
  connect \b $ternary$asicworld/verilog/code_verilog_tutorial_tri_buf.v:7$1_Y
end
