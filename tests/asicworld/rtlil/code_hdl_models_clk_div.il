autoidx 3
attribute \cells_not_processed 1
attribute \src "asicworld/verilog/code_hdl_models_clk_div.v:8.1-27.10"
module \clk_div
  attribute \src "asicworld/verilog/code_hdl_models_clk_div.v:20.1-25.4"
  wire $0\clk_out[0:0]
  attribute \src "asicworld/verilog/code_hdl_models_clk_div.v:24.14-24.22"
  wire $logic_not$asicworld/verilog/code_hdl_models_clk_div.v:24$2_Y
  attribute \src "asicworld/verilog/code_hdl_models_clk_div.v:10.22-10.28"
  wire input 1 \clk_in
  attribute \src "asicworld/verilog/code_hdl_models_clk_div.v:13.22-13.29"
  wire output 4 \clk_out
  attribute \src "asicworld/verilog/code_hdl_models_clk_div.v:12.22-12.28"
  wire input 2 \enable
  attribute \src "asicworld/verilog/code_hdl_models_clk_div.v:11.22-11.27"
  wire input 3 \reset
  attribute \src "asicworld/verilog/code_hdl_models_clk_div.v:24.14-24.22"
  cell $logic_not $logic_not$asicworld/verilog/code_hdl_models_clk_div.v:24$2
    parameter \A_SIGNED 0
    parameter \A_WIDTH 1
    parameter \Y_WIDTH 1
    connect \A \clk_out
    connect \Y $logic_not$asicworld/verilog/code_hdl_models_clk_div.v:24$2_Y
  end
  attribute \src "asicworld/verilog/code_hdl_models_clk_div.v:20.1-25.4"
  process $proc$asicworld/verilog/code_hdl_models_clk_div.v:20$1
    assign $0\clk_out[0:0] \clk_out
    attribute \src "asicworld/verilog/code_hdl_models_clk_div.v:21.1-25.4"
    switch \reset
      attribute \src "asicworld/verilog/code_hdl_models_clk_div.v:21.5-21.10"
      case 1'1
        assign $0\clk_out[0:0] 1'0
      attribute \src "asicworld/verilog/code_hdl_models_clk_div.v:23.5-23.9"
      case 
        attribute \src "asicworld/verilog/code_hdl_models_clk_div.v:23.10-25.4"
        switch \enable
          attribute \src "asicworld/verilog/code_hdl_models_clk_div.v:23.14-23.20"
          case 1'1
            assign $0\clk_out[0:0] $logic_not$asicworld/verilog/code_hdl_models_clk_div.v:24$2_Y
          case 
        end
    end
    sync posedge \clk_in
      update \clk_out $0\clk_out[0:0]
  end
end
