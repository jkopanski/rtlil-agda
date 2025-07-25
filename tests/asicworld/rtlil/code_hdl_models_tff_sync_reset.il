autoidx 4
attribute \cells_not_processed 1
attribute \src "asicworld/verilog/code_hdl_models_tff_sync_reset.v:7.1-27.10"
module \tff_sync_reset
  attribute \src "asicworld/verilog/code_hdl_models_tff_sync_reset.v:20.1-25.4"
  wire $0\q[0:0]
  attribute \src "asicworld/verilog/code_hdl_models_tff_sync_reset.v:24.8-24.10"
  wire $logic_not$asicworld/verilog/code_hdl_models_tff_sync_reset.v:24$3_Y
  attribute \src "asicworld/verilog/code_hdl_models_tff_sync_reset.v:21.5-21.11"
  wire $not$asicworld/verilog/code_hdl_models_tff_sync_reset.v:21$2_Y
  attribute \src "asicworld/verilog/code_hdl_models_tff_sync_reset.v:14.13-14.16"
  wire input 2 \clk
  attribute \src "asicworld/verilog/code_hdl_models_tff_sync_reset.v:14.7-14.11"
  wire input 1 \data
  attribute \src "asicworld/verilog/code_hdl_models_tff_sync_reset.v:16.8-16.9"
  wire output 4 \q
  attribute \src "asicworld/verilog/code_hdl_models_tff_sync_reset.v:14.18-14.23"
  wire input 3 \reset
  attribute \src "asicworld/verilog/code_hdl_models_tff_sync_reset.v:24.8-24.10"
  cell $logic_not $logic_not$asicworld/verilog/code_hdl_models_tff_sync_reset.v:24$3
    parameter \A_SIGNED 0
    parameter \A_WIDTH 1
    parameter \Y_WIDTH 1
    connect \A \q
    connect \Y $logic_not$asicworld/verilog/code_hdl_models_tff_sync_reset.v:24$3_Y
  end
  attribute \src "asicworld/verilog/code_hdl_models_tff_sync_reset.v:21.5-21.11"
  cell $not $not$asicworld/verilog/code_hdl_models_tff_sync_reset.v:21$2
    parameter \A_SIGNED 0
    parameter \A_WIDTH 1
    parameter \Y_WIDTH 1
    connect \A \reset
    connect \Y $not$asicworld/verilog/code_hdl_models_tff_sync_reset.v:21$2_Y
  end
  attribute \src "asicworld/verilog/code_hdl_models_tff_sync_reset.v:20.1-25.4"
  process $proc$asicworld/verilog/code_hdl_models_tff_sync_reset.v:20$1
    assign $0\q[0:0] \q
    attribute \src "asicworld/verilog/code_hdl_models_tff_sync_reset.v:21.1-25.4"
    switch $not$asicworld/verilog/code_hdl_models_tff_sync_reset.v:21$2_Y
      attribute \src "asicworld/verilog/code_hdl_models_tff_sync_reset.v:21.5-21.11"
      case 1'1
        assign $0\q[0:0] 1'0
      attribute \src "asicworld/verilog/code_hdl_models_tff_sync_reset.v:23.5-23.9"
      case 
        attribute \src "asicworld/verilog/code_hdl_models_tff_sync_reset.v:23.10-25.4"
        switch \data
          attribute \src "asicworld/verilog/code_hdl_models_tff_sync_reset.v:23.14-23.18"
          case 1'1
            assign $0\q[0:0] $logic_not$asicworld/verilog/code_hdl_models_tff_sync_reset.v:24$3_Y
          case 
        end
    end
    sync posedge \clk
      update \q $0\q[0:0]
  end
end
