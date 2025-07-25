autoidx 3
attribute \cells_not_processed 1
attribute \src "asicworld/verilog/code_hdl_models_dff_async_reset.v:7.1-30.10"
module \dff_async_reset
  attribute \src "asicworld/verilog/code_hdl_models_dff_async_reset.v:23.1-28.4"
  wire $0\q[0:0]
  attribute \src "asicworld/verilog/code_hdl_models_dff_async_reset.v:24.5-24.11"
  wire $not$asicworld/verilog/code_hdl_models_dff_async_reset.v:24$2_Y
  attribute \src "asicworld/verilog/code_hdl_models_dff_async_reset.v:14.13-14.16"
  wire input 2 \clk
  attribute \src "asicworld/verilog/code_hdl_models_dff_async_reset.v:14.7-14.11"
  wire input 1 \data
  attribute \src "asicworld/verilog/code_hdl_models_dff_async_reset.v:17.8-17.9"
  wire output 4 \q
  attribute \src "asicworld/verilog/code_hdl_models_dff_async_reset.v:14.18-14.23"
  wire input 3 \reset
  attribute \src "asicworld/verilog/code_hdl_models_dff_async_reset.v:24.5-24.11"
  cell $not $not$asicworld/verilog/code_hdl_models_dff_async_reset.v:24$2
    parameter \A_SIGNED 0
    parameter \A_WIDTH 1
    parameter \Y_WIDTH 1
    connect \A \reset
    connect \Y $not$asicworld/verilog/code_hdl_models_dff_async_reset.v:24$2_Y
  end
  attribute \src "asicworld/verilog/code_hdl_models_dff_async_reset.v:23.1-28.4"
  process $proc$asicworld/verilog/code_hdl_models_dff_async_reset.v:23$1
    assign $0\q[0:0] \q
    attribute \src "asicworld/verilog/code_hdl_models_dff_async_reset.v:24.1-28.4"
    switch $not$asicworld/verilog/code_hdl_models_dff_async_reset.v:24$2_Y
      attribute \src "asicworld/verilog/code_hdl_models_dff_async_reset.v:24.5-24.11"
      case 1'1
        assign $0\q[0:0] 1'0
      attribute \src "asicworld/verilog/code_hdl_models_dff_async_reset.v:26.6-26.10"
      case 
        assign $0\q[0:0] \data
    end
    sync posedge \clk
      update \q $0\q[0:0]
    sync negedge \reset
      update \q $0\q[0:0]
  end
end
