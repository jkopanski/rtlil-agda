autoidx 3
attribute \cells_not_processed 1
attribute \src "asicworld/verilog/code_hdl_models_up_counter.v:7.1-28.10"
module \up_counter
  attribute \src "asicworld/verilog/code_hdl_models_up_counter.v:20.1-25.4"
  wire width 8 $0\out[7:0]
  attribute \src "asicworld/verilog/code_hdl_models_up_counter.v:24.10-24.17"
  wire width 32 $add$asicworld/verilog/code_hdl_models_up_counter.v:24$2_Y
  attribute \src "asicworld/verilog/code_hdl_models_up_counter.v:16.20-16.23"
  wire input 3 \clk
  attribute \src "asicworld/verilog/code_hdl_models_up_counter.v:16.12-16.18"
  wire input 2 \enable
  attribute \src "asicworld/verilog/code_hdl_models_up_counter.v:14.18-14.21"
  wire width 8 output 1 \out
  attribute \src "asicworld/verilog/code_hdl_models_up_counter.v:16.25-16.30"
  wire input 4 \reset
  attribute \src "asicworld/verilog/code_hdl_models_up_counter.v:24.10-24.17"
  cell $add $add$asicworld/verilog/code_hdl_models_up_counter.v:24$2
    parameter \A_SIGNED 0
    parameter \A_WIDTH 8
    parameter \B_SIGNED 0
    parameter \B_WIDTH 32
    parameter \Y_WIDTH 32
    connect \A \out
    connect \B 1
    connect \Y $add$asicworld/verilog/code_hdl_models_up_counter.v:24$2_Y
  end
  attribute \src "asicworld/verilog/code_hdl_models_up_counter.v:20.1-25.4"
  process $proc$asicworld/verilog/code_hdl_models_up_counter.v:20$1
    assign $0\out[7:0] \out
    attribute \src "asicworld/verilog/code_hdl_models_up_counter.v:21.1-25.4"
    switch \reset
      attribute \src "asicworld/verilog/code_hdl_models_up_counter.v:21.5-21.10"
      case 1'1
        assign $0\out[7:0] 8'00000000
      attribute \src "asicworld/verilog/code_hdl_models_up_counter.v:23.5-23.9"
      case 
        attribute \src "asicworld/verilog/code_hdl_models_up_counter.v:23.10-25.4"
        switch \enable
          attribute \src "asicworld/verilog/code_hdl_models_up_counter.v:23.14-23.20"
          case 1'1
            assign $0\out[7:0] $add$asicworld/verilog/code_hdl_models_up_counter.v:24$2_Y [7:0]
          case 
        end
    end
    sync posedge \clk
      update \out $0\out[7:0]
  end
end
