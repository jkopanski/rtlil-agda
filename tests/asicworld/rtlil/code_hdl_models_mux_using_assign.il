autoidx 2
attribute \cells_not_processed 1
attribute \src "asicworld/verilog/code_hdl_models_mux_using_assign.v:7.1-22.10"
module \mux_using_assign
  attribute \src "asicworld/verilog/code_hdl_models_mux_using_assign.v:20.18-20.39"
  wire $ternary$asicworld/verilog/code_hdl_models_mux_using_assign.v:20$1_Y
  attribute \src "asicworld/verilog/code_hdl_models_mux_using_assign.v:14.7-14.12"
  wire input 1 \din_0
  attribute \src "asicworld/verilog/code_hdl_models_mux_using_assign.v:14.14-14.19"
  wire input 2 \din_1
  attribute \src "asicworld/verilog/code_hdl_models_mux_using_assign.v:16.8-16.15"
  wire output 4 \mux_out
  attribute \src "asicworld/verilog/code_hdl_models_mux_using_assign.v:14.21-14.24"
  wire input 3 \sel
  attribute \src "asicworld/verilog/code_hdl_models_mux_using_assign.v:20.18-20.39"
  cell $mux $ternary$asicworld/verilog/code_hdl_models_mux_using_assign.v:20$1
    parameter \WIDTH 1
    connect \A \din_0
    connect \B \din_1
    connect \S \sel
    connect \Y $ternary$asicworld/verilog/code_hdl_models_mux_using_assign.v:20$1_Y
  end
  connect \mux_out $ternary$asicworld/verilog/code_hdl_models_mux_using_assign.v:20$1_Y
end
