autoidx 5
attribute \cells_not_processed 1
attribute \src "asicworld/verilog/code_verilog_tutorial_first_counter.v:9.1-47.10"
module \first_counter
  attribute \src "asicworld/verilog/code_verilog_tutorial_first_counter.v:34.1-45.4"
  wire width 4 $0\counter_out[3:0]
  attribute \src "asicworld/verilog/code_verilog_tutorial_first_counter.v:43.20-43.35"
  wire width 32 $add$asicworld/verilog/code_verilog_tutorial_first_counter.v:43$4_Y
  attribute \src "asicworld/verilog/code_verilog_tutorial_first_counter.v:38.7-38.20"
  wire $eq$asicworld/verilog/code_verilog_tutorial_first_counter.v:38$2_Y
  attribute \src "asicworld/verilog/code_verilog_tutorial_first_counter.v:42.12-42.26"
  wire $eq$asicworld/verilog/code_verilog_tutorial_first_counter.v:42$3_Y
  attribute \src "asicworld/verilog/code_verilog_tutorial_first_counter.v:16.7-16.12"
  wire input 1 \clock
  attribute \src "asicworld/verilog/code_verilog_tutorial_first_counter.v:20.14-20.25"
  wire width 4 output 4 \counter_out
  attribute \src "asicworld/verilog/code_verilog_tutorial_first_counter.v:18.7-18.13"
  wire input 3 \enable
  attribute \src "asicworld/verilog/code_verilog_tutorial_first_counter.v:17.7-17.12"
  wire input 2 \reset
  attribute \src "asicworld/verilog/code_verilog_tutorial_first_counter.v:43.20-43.35"
  cell $add $add$asicworld/verilog/code_verilog_tutorial_first_counter.v:43$4
    parameter \A_SIGNED 0
    parameter \A_WIDTH 4
    parameter \B_SIGNED 0
    parameter \B_WIDTH 32
    parameter \Y_WIDTH 32
    connect \A \counter_out
    connect \B 1
    connect \Y $add$asicworld/verilog/code_verilog_tutorial_first_counter.v:43$4_Y
  end
  attribute \src "asicworld/verilog/code_verilog_tutorial_first_counter.v:38.7-38.20"
  cell $eq $eq$asicworld/verilog/code_verilog_tutorial_first_counter.v:38$2
    parameter \A_SIGNED 0
    parameter \A_WIDTH 1
    parameter \B_SIGNED 0
    parameter \B_WIDTH 1
    parameter \Y_WIDTH 1
    connect \A \reset
    connect \B 1'1
    connect \Y $eq$asicworld/verilog/code_verilog_tutorial_first_counter.v:38$2_Y
  end
  attribute \src "asicworld/verilog/code_verilog_tutorial_first_counter.v:42.12-42.26"
  cell $eq $eq$asicworld/verilog/code_verilog_tutorial_first_counter.v:42$3
    parameter \A_SIGNED 0
    parameter \A_WIDTH 1
    parameter \B_SIGNED 0
    parameter \B_WIDTH 1
    parameter \Y_WIDTH 1
    connect \A \enable
    connect \B 1'1
    connect \Y $eq$asicworld/verilog/code_verilog_tutorial_first_counter.v:42$3_Y
  end
  attribute \src "asicworld/verilog/code_verilog_tutorial_first_counter.v:34.1-45.4"
  process $proc$asicworld/verilog/code_verilog_tutorial_first_counter.v:34$1
    assign $0\counter_out[3:0] \counter_out
    attribute \src "asicworld/verilog/code_verilog_tutorial_first_counter.v:38.3-44.6"
    switch $eq$asicworld/verilog/code_verilog_tutorial_first_counter.v:38$2_Y
      attribute \src "asicworld/verilog/code_verilog_tutorial_first_counter.v:38.7-38.20"
      case 1'1
        assign $0\counter_out[3:0] 4'0000
      attribute \src "asicworld/verilog/code_verilog_tutorial_first_counter.v:42.3-42.7"
      case 
        attribute \src "asicworld/verilog/code_verilog_tutorial_first_counter.v:42.8-44.6"
        switch $eq$asicworld/verilog/code_verilog_tutorial_first_counter.v:42$3_Y
          attribute \src "asicworld/verilog/code_verilog_tutorial_first_counter.v:42.12-42.26"
          case 1'1
            assign $0\counter_out[3:0] $add$asicworld/verilog/code_verilog_tutorial_first_counter.v:43$4_Y [3:0]
          case 
        end
    end
    sync posedge \clock
      update \counter_out $0\counter_out[3:0]
  end
end
