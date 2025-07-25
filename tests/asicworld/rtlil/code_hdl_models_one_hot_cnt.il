autoidx 2
attribute \cells_not_processed 1
attribute \src "asicworld/verilog/code_hdl_models_one_hot_cnt.v:7.1-31.10"
module \one_hot_cnt
  attribute \src "asicworld/verilog/code_hdl_models_one_hot_cnt.v:23.1-29.4"
  wire width 8 $0\out[7:0]
  attribute \src "asicworld/verilog/code_hdl_models_one_hot_cnt.v:17.15-17.18"
  wire input 3 \clk
  attribute \src "asicworld/verilog/code_hdl_models_one_hot_cnt.v:17.7-17.13"
  wire input 2 \enable
  attribute \src "asicworld/verilog/code_hdl_models_one_hot_cnt.v:14.14-14.17"
  wire width 8 output 1 \out
  attribute \src "asicworld/verilog/code_hdl_models_one_hot_cnt.v:17.20-17.25"
  wire input 4 \reset
  attribute \src "asicworld/verilog/code_hdl_models_one_hot_cnt.v:23.1-29.4"
  process $proc$asicworld/verilog/code_hdl_models_one_hot_cnt.v:23$1
    assign $0\out[7:0] \out
    attribute \src "asicworld/verilog/code_hdl_models_one_hot_cnt.v:24.1-29.4"
    switch \reset
      attribute \src "asicworld/verilog/code_hdl_models_one_hot_cnt.v:24.5-24.10"
      case 1'1
        assign $0\out[7:0] 8'00000001
      attribute \src "asicworld/verilog/code_hdl_models_one_hot_cnt.v:26.5-26.9"
      case 
        attribute \src "asicworld/verilog/code_hdl_models_one_hot_cnt.v:26.10-29.4"
        switch \enable
          attribute \src "asicworld/verilog/code_hdl_models_one_hot_cnt.v:26.14-26.20"
          case 1'1
            assign $0\out[7:0] { \out [6:0] \out [7] }
          case 
        end
    end
    sync posedge \clk
      update \out $0\out[7:0]
  end
end
