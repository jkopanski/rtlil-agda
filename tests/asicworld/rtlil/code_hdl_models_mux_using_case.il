autoidx 2
attribute \cells_not_processed 1
attribute \src "asicworld/verilog/code_hdl_models_mux_using_case.v:7.1-28.10"
module \mux_using_case
  attribute \src "asicworld/verilog/code_hdl_models_mux_using_case.v:20.1-26.4"
  wire $0\mux_out[0:0]
  attribute \src "asicworld/verilog/code_hdl_models_mux_using_case.v:20.1-26.4"
  wire $1\mux_out[0:0]
  attribute \src "asicworld/verilog/code_hdl_models_mux_using_case.v:14.7-14.12"
  wire input 1 \din_0
  attribute \src "asicworld/verilog/code_hdl_models_mux_using_case.v:14.14-14.19"
  wire input 2 \din_1
  attribute \src "asicworld/verilog/code_hdl_models_mux_using_case.v:16.8-16.15"
  wire output 4 \mux_out
  attribute \src "asicworld/verilog/code_hdl_models_mux_using_case.v:14.21-14.24"
  wire input 3 \sel
  attribute \src "asicworld/verilog/code_hdl_models_mux_using_case.v:20.1-26.4"
  process $proc$asicworld/verilog/code_hdl_models_mux_using_case.v:20$1
    assign { } { }
    assign $0\mux_out[0:0] $1\mux_out[0:0]
    attribute \src "asicworld/verilog/code_hdl_models_mux_using_case.v:22.2-25.9"
    switch \sel
      attribute \src "asicworld/verilog/code_hdl_models_mux_using_case.v:0.0-0.0"
      case 1'0
        assign { } { }
        assign $1\mux_out[0:0] \din_0
      attribute \src "asicworld/verilog/code_hdl_models_mux_using_case.v:0.0-0.0"
      case 1'1
        assign { } { }
        assign $1\mux_out[0:0] \din_1
      case 
        assign $1\mux_out[0:0] \mux_out
    end
    sync always
      update \mux_out $0\mux_out[0:0]
  end
end
