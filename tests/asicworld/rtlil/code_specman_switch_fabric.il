autoidx 2
attribute \cells_not_processed 1
attribute \src "asicworld/verilog/code_specman_switch_fabric.v:51.1-82.10"
module \switch
  attribute \src "asicworld/verilog/code_specman_switch_fabric.v:70.1-80.4"
  wire width 8 $0\data_out[7:0]
  attribute \src "asicworld/verilog/code_specman_switch_fabric.v:70.1-80.4"
  wire $0\data_out_ack[0:0]
  attribute \src "asicworld/verilog/code_specman_switch_fabric.v:60.9-60.12"
  wire input 1 \clk
  attribute \src "asicworld/verilog/code_specman_switch_fabric.v:62.14-62.21"
  wire width 8 input 3 \data_in
  attribute \src "asicworld/verilog/code_specman_switch_fabric.v:63.9-63.22"
  wire input 4 \data_in_valid
  attribute \src "asicworld/verilog/code_specman_switch_fabric.v:64.15-64.23"
  wire width 8 output 5 \data_out
  attribute \src "asicworld/verilog/code_specman_switch_fabric.v:65.9-65.21"
  wire output 6 \data_out_ack
  attribute \src "asicworld/verilog/code_specman_switch_fabric.v:61.9-61.14"
  wire input 2 \reset
  attribute \src "asicworld/verilog/code_specman_switch_fabric.v:70.1-80.4"
  process $proc$asicworld/verilog/code_specman_switch_fabric.v:70$1
    assign $0\data_out[7:0] \data_out
    assign $0\data_out_ack[0:0] \data_out_ack
    attribute \src "asicworld/verilog/code_specman_switch_fabric.v:71.1-80.4"
    switch \reset
      attribute \src "asicworld/verilog/code_specman_switch_fabric.v:71.5-71.10"
      case 1'1
        assign $0\data_out[7:0] 8'00000000
        assign $0\data_out_ack[0:0] 1'0
      attribute \src "asicworld/verilog/code_specman_switch_fabric.v:74.5-74.9"
      case 
        attribute \src "asicworld/verilog/code_specman_switch_fabric.v:74.10-80.4"
        switch \data_in_valid
          attribute \src "asicworld/verilog/code_specman_switch_fabric.v:74.14-74.27"
          case 1'1
            assign $0\data_out[7:0] \data_in
            assign $0\data_out_ack[0:0] 1'1
          attribute \src "asicworld/verilog/code_specman_switch_fabric.v:77.5-77.9"
          case 
            assign $0\data_out[7:0] 8'00000000
            assign $0\data_out_ack[0:0] 1'0
        end
    end
    sync posedge \clk
      update \data_out $0\data_out[7:0]
      update \data_out_ack $0\data_out_ack[0:0]
  end
end
attribute \cells_not_processed 1
attribute \src "asicworld/verilog/code_specman_switch_fabric.v:1.1-49.10"
module \switch_fabric
  attribute \gentb_clock 1
  attribute \src "asicworld/verilog/code_specman_switch_fabric.v:12.17-12.20"
  wire input 1 \clk
  attribute \src "asicworld/verilog/code_specman_switch_fabric.v:13.17-13.25"
  wire width 8 input 3 \data_in0
  attribute \src "asicworld/verilog/code_specman_switch_fabric.v:13.27-13.35"
  wire width 8 input 4 \data_in1
  attribute \src "asicworld/verilog/code_specman_switch_fabric.v:13.37-13.45"
  wire width 8 input 5 \data_in2
  attribute \src "asicworld/verilog/code_specman_switch_fabric.v:13.47-13.55"
  wire width 8 input 6 \data_in3
  attribute \src "asicworld/verilog/code_specman_switch_fabric.v:14.17-14.25"
  wire width 8 input 7 \data_in4
  attribute \src "asicworld/verilog/code_specman_switch_fabric.v:14.27-14.35"
  wire width 8 input 8 \data_in5
  attribute \src "asicworld/verilog/code_specman_switch_fabric.v:15.17-15.31"
  wire input 9 \data_in_valid0
  attribute \src "asicworld/verilog/code_specman_switch_fabric.v:15.33-15.47"
  wire input 10 \data_in_valid1
  attribute \src "asicworld/verilog/code_specman_switch_fabric.v:15.49-15.63"
  wire input 11 \data_in_valid2
  attribute \src "asicworld/verilog/code_specman_switch_fabric.v:16.17-16.31"
  wire width 8 input 12 \data_in_valid3
  attribute \src "asicworld/verilog/code_specman_switch_fabric.v:16.33-16.47"
  wire width 8 input 13 \data_in_valid4
  attribute \src "asicworld/verilog/code_specman_switch_fabric.v:16.49-16.63"
  wire width 8 input 14 \data_in_valid5
  attribute \src "asicworld/verilog/code_specman_switch_fabric.v:17.17-17.26"
  wire width 8 output 15 \data_out0
  attribute \src "asicworld/verilog/code_specman_switch_fabric.v:17.28-17.37"
  wire width 8 output 16 \data_out1
  attribute \src "asicworld/verilog/code_specman_switch_fabric.v:17.39-17.48"
  wire width 8 output 17 \data_out2
  attribute \src "asicworld/verilog/code_specman_switch_fabric.v:17.50-17.59"
  wire width 8 output 18 \data_out3
  attribute \src "asicworld/verilog/code_specman_switch_fabric.v:18.17-18.26"
  wire width 8 output 19 \data_out4
  attribute \src "asicworld/verilog/code_specman_switch_fabric.v:18.28-18.37"
  wire width 8 output 20 \data_out5
  attribute \src "asicworld/verilog/code_specman_switch_fabric.v:19.17-19.30"
  wire output 21 \data_out_ack0
  attribute \src "asicworld/verilog/code_specman_switch_fabric.v:19.32-19.45"
  wire output 22 \data_out_ack1
  attribute \src "asicworld/verilog/code_specman_switch_fabric.v:19.47-19.60"
  wire output 23 \data_out_ack2
  attribute \src "asicworld/verilog/code_specman_switch_fabric.v:20.17-20.30"
  wire width 8 output 24 \data_out_ack3
  attribute \src "asicworld/verilog/code_specman_switch_fabric.v:20.32-20.45"
  wire width 8 output 25 \data_out_ack4
  attribute \src "asicworld/verilog/code_specman_switch_fabric.v:20.47-20.60"
  wire width 8 output 26 \data_out_ack5
  attribute \src "asicworld/verilog/code_specman_switch_fabric.v:12.22-12.27"
  wire input 2 \reset
  attribute \module_not_derived 1
  attribute \src "asicworld/verilog/code_specman_switch_fabric.v:25.8-27.32"
  cell \switch \port_0
    connect \clk \clk
    connect \data_in \data_in0
    connect \data_in_valid \data_in_valid0
    connect \data_out \data_out0
    connect \data_out_ack \data_out_ack0
    connect \reset \reset
  end
  attribute \module_not_derived 1
  attribute \src "asicworld/verilog/code_specman_switch_fabric.v:29.8-31.32"
  cell \switch \port_1
    connect \clk \clk
    connect \data_in \data_in1
    connect \data_in_valid \data_in_valid1
    connect \data_out \data_out1
    connect \data_out_ack \data_out_ack1
    connect \reset \reset
  end
  attribute \module_not_derived 1
  attribute \src "asicworld/verilog/code_specman_switch_fabric.v:33.8-35.31"
  cell \switch \port_2
    connect \clk \clk
    connect \data_in \data_in2
    connect \data_in_valid \data_in_valid2
    connect \data_out \data_out2
    connect \data_out_ack \data_out_ack2
    connect \reset \reset
  end
  attribute \module_not_derived 1
  attribute \src "asicworld/verilog/code_specman_switch_fabric.v:37.8-39.32"
  cell \switch \port_3
    connect \clk \clk
    connect \data_in \data_in3
    connect \data_in_valid \data_in_valid3
    connect \data_out \data_out3
    connect \data_out_ack \data_out_ack3
    connect \reset \reset
  end
  attribute \module_not_derived 1
  attribute \src "asicworld/verilog/code_specman_switch_fabric.v:41.8-43.32"
  cell \switch \port_4
    connect \clk \clk
    connect \data_in \data_in4
    connect \data_in_valid \data_in_valid4
    connect \data_out \data_out4
    connect \data_out_ack \data_out_ack4
    connect \reset \reset
  end
  attribute \module_not_derived 1
  attribute \src "asicworld/verilog/code_specman_switch_fabric.v:45.8-47.32"
  cell \switch \port_5
    connect \clk \clk
    connect \data_in \data_in5
    connect \data_in_valid \data_in_valid5
    connect \data_out \data_out5
    connect \data_out_ack \data_out_ack5
    connect \reset \reset
  end
end
