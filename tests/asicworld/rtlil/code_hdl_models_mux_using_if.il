autoidx 3
attribute \cells_not_processed 1
attribute \src "asicworld/verilog/code_hdl_models_mux_using_if.v:7.1-29.10"
module \mux_using_if
  attribute \src "asicworld/verilog/code_hdl_models_mux_using_if.v:20.1-27.4"
  wire $0\mux_out[0:0]
  attribute \src "asicworld/verilog/code_hdl_models_mux_using_if.v:20.1-27.4"
  wire $1\mux_out[0:0]
  attribute \src "asicworld/verilog/code_hdl_models_mux_using_if.v:22.7-22.18"
  wire $eq$asicworld/verilog/code_hdl_models_mux_using_if.v:22$2_Y
  attribute \src "asicworld/verilog/code_hdl_models_mux_using_if.v:14.7-14.12"
  wire input 1 \din_0
  attribute \src "asicworld/verilog/code_hdl_models_mux_using_if.v:14.14-14.19"
  wire input 2 \din_1
  attribute \src "asicworld/verilog/code_hdl_models_mux_using_if.v:16.8-16.15"
  wire output 4 \mux_out
  attribute \src "asicworld/verilog/code_hdl_models_mux_using_if.v:14.21-14.24"
  wire input 3 \sel
  attribute \src "asicworld/verilog/code_hdl_models_mux_using_if.v:22.7-22.18"
  cell $eq $eq$asicworld/verilog/code_hdl_models_mux_using_if.v:22$2
    parameter \A_SIGNED 0
    parameter \A_WIDTH 1
    parameter \B_SIGNED 0
    parameter \B_WIDTH 1
    parameter \Y_WIDTH 1
    connect \A \sel
    connect \B 1'0
    connect \Y $eq$asicworld/verilog/code_hdl_models_mux_using_if.v:22$2_Y
  end
  attribute \src "asicworld/verilog/code_hdl_models_mux_using_if.v:20.1-27.4"
  process $proc$asicworld/verilog/code_hdl_models_mux_using_if.v:20$1
    assign { } { }
    assign $0\mux_out[0:0] $1\mux_out[0:0]
    attribute \src "asicworld/verilog/code_hdl_models_mux_using_if.v:22.3-26.6"
    switch $eq$asicworld/verilog/code_hdl_models_mux_using_if.v:22$2_Y
      attribute \src "asicworld/verilog/code_hdl_models_mux_using_if.v:22.7-22.18"
      case 1'1
        assign { } { }
        assign $1\mux_out[0:0] \din_0
      attribute \src "asicworld/verilog/code_hdl_models_mux_using_if.v:24.7-24.11"
      case 
        assign { } { }
        assign $1\mux_out[0:0] \din_1
    end
    sync always
      update \mux_out $0\mux_out[0:0]
  end
end
