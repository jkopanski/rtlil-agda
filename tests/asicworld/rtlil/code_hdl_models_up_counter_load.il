autoidx 3
attribute \cells_not_processed 1
attribute \src "asicworld/verilog/code_hdl_models_up_counter_load.v:7.1-32.10"
module \up_counter_load
  attribute \src "asicworld/verilog/code_hdl_models_up_counter_load.v:23.1-30.4"
  wire width 8 $0\out[7:0]
  attribute \src "asicworld/verilog/code_hdl_models_up_counter_load.v:29.10-29.17"
  wire width 32 $add$asicworld/verilog/code_hdl_models_up_counter_load.v:29$2_Y
  attribute \src "asicworld/verilog/code_hdl_models_up_counter_load.v:19.21-19.24"
  wire input 5 \clk
  attribute \src "asicworld/verilog/code_hdl_models_up_counter_load.v:18.13-18.17"
  wire width 8 input 2 \data
  attribute \src "asicworld/verilog/code_hdl_models_up_counter_load.v:19.13-19.19"
  wire input 4 \enable
  attribute \src "asicworld/verilog/code_hdl_models_up_counter_load.v:19.7-19.11"
  wire input 3 \load
  attribute \src "asicworld/verilog/code_hdl_models_up_counter_load.v:16.14-16.17"
  wire width 8 output 1 \out
  attribute \src "asicworld/verilog/code_hdl_models_up_counter_load.v:19.26-19.31"
  wire input 6 \reset
  attribute \src "asicworld/verilog/code_hdl_models_up_counter_load.v:29.10-29.17"
  cell $add $add$asicworld/verilog/code_hdl_models_up_counter_load.v:29$2
    parameter \A_SIGNED 0
    parameter \A_WIDTH 8
    parameter \B_SIGNED 0
    parameter \B_WIDTH 32
    parameter \Y_WIDTH 32
    connect \A \out
    connect \B 1
    connect \Y $add$asicworld/verilog/code_hdl_models_up_counter_load.v:29$2_Y
  end
  attribute \src "asicworld/verilog/code_hdl_models_up_counter_load.v:23.1-30.4"
  process $proc$asicworld/verilog/code_hdl_models_up_counter_load.v:23$1
    assign $0\out[7:0] \out
    attribute \src "asicworld/verilog/code_hdl_models_up_counter_load.v:24.1-30.4"
    switch \reset
      attribute \src "asicworld/verilog/code_hdl_models_up_counter_load.v:24.5-24.10"
      case 1'1
        assign $0\out[7:0] 8'00000000
      attribute \src "asicworld/verilog/code_hdl_models_up_counter_load.v:26.5-26.9"
      case 
        attribute \src "asicworld/verilog/code_hdl_models_up_counter_load.v:26.10-30.4"
        switch \load
          attribute \src "asicworld/verilog/code_hdl_models_up_counter_load.v:26.14-26.18"
          case 1'1
            assign $0\out[7:0] \data
          attribute \src "asicworld/verilog/code_hdl_models_up_counter_load.v:28.5-28.9"
          case 
            attribute \src "asicworld/verilog/code_hdl_models_up_counter_load.v:28.10-30.4"
            switch \enable
              attribute \src "asicworld/verilog/code_hdl_models_up_counter_load.v:28.14-28.20"
              case 1'1
                assign $0\out[7:0] $add$asicworld/verilog/code_hdl_models_up_counter_load.v:29$2_Y [7:0]
              case 
            end
        end
    end
    sync posedge \clk
      update \out $0\out[7:0]
  end
end
