autoidx 4
attribute \cells_not_processed 1
attribute \src "asicworld/verilog/code_hdl_models_up_down_counter.v:7.1-29.10"
module \up_down_counter
  attribute \src "asicworld/verilog/code_hdl_models_up_down_counter.v:20.1-27.4"
  wire width 8 $0\out[7:0]
  attribute \src "asicworld/verilog/code_hdl_models_up_down_counter.v:24.10-24.17"
  wire width 32 $add$asicworld/verilog/code_hdl_models_up_down_counter.v:24$2_Y
  attribute \src "asicworld/verilog/code_hdl_models_up_down_counter.v:26.10-26.17"
  wire width 32 $sub$asicworld/verilog/code_hdl_models_up_down_counter.v:26$3_Y
  attribute \src "asicworld/verilog/code_hdl_models_up_down_counter.v:16.16-16.19"
  wire input 3 \clk
  attribute \src "asicworld/verilog/code_hdl_models_up_down_counter.v:14.14-14.17"
  wire width 8 output 1 \out
  attribute \src "asicworld/verilog/code_hdl_models_up_down_counter.v:16.21-16.26"
  wire input 4 \reset
  attribute \src "asicworld/verilog/code_hdl_models_up_down_counter.v:16.7-16.14"
  wire input 2 \up_down
  attribute \src "asicworld/verilog/code_hdl_models_up_down_counter.v:24.10-24.17"
  cell $add $add$asicworld/verilog/code_hdl_models_up_down_counter.v:24$2
    parameter \A_SIGNED 0
    parameter \A_WIDTH 8
    parameter \B_SIGNED 0
    parameter \B_WIDTH 32
    parameter \Y_WIDTH 32
    connect \A \out
    connect \B 1
    connect \Y $add$asicworld/verilog/code_hdl_models_up_down_counter.v:24$2_Y
  end
  attribute \src "asicworld/verilog/code_hdl_models_up_down_counter.v:26.10-26.17"
  cell $sub $sub$asicworld/verilog/code_hdl_models_up_down_counter.v:26$3
    parameter \A_SIGNED 0
    parameter \A_WIDTH 8
    parameter \B_SIGNED 0
    parameter \B_WIDTH 32
    parameter \Y_WIDTH 32
    connect \A \out
    connect \B 1
    connect \Y $sub$asicworld/verilog/code_hdl_models_up_down_counter.v:26$3_Y
  end
  attribute \src "asicworld/verilog/code_hdl_models_up_down_counter.v:20.1-27.4"
  process $proc$asicworld/verilog/code_hdl_models_up_down_counter.v:20$1
    assign $0\out[7:0] \out
    attribute \src "asicworld/verilog/code_hdl_models_up_down_counter.v:21.1-27.4"
    switch \reset
      attribute \src "asicworld/verilog/code_hdl_models_up_down_counter.v:21.5-21.10"
      case 1'1
        assign $0\out[7:0] 8'00000000
      attribute \src "asicworld/verilog/code_hdl_models_up_down_counter.v:23.5-23.9"
      case 
        attribute \src "asicworld/verilog/code_hdl_models_up_down_counter.v:23.10-27.4"
        switch \up_down
          attribute \src "asicworld/verilog/code_hdl_models_up_down_counter.v:23.14-23.21"
          case 1'1
            assign $0\out[7:0] $add$asicworld/verilog/code_hdl_models_up_down_counter.v:24$2_Y [7:0]
          attribute \src "asicworld/verilog/code_hdl_models_up_down_counter.v:25.5-25.9"
          case 
            assign $0\out[7:0] $sub$asicworld/verilog/code_hdl_models_up_down_counter.v:26$3_Y [7:0]
        end
    end
    sync posedge \clk
      update \out $0\out[7:0]
  end
end
