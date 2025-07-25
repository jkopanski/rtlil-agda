autoidx 5
attribute \cells_not_processed 1
attribute \src "asicworld/verilog/code_verilog_tutorial_counter.v:7.1-19.10"
module \counter
  attribute \src "asicworld/verilog/code_verilog_tutorial_counter.v:12.1-17.4"
  wire width 4 $0\count[3:0]
  attribute \src "asicworld/verilog/code_verilog_tutorial_counter.v:16.12-16.21"
  wire width 32 $add$asicworld/verilog/code_verilog_tutorial_counter.v:16$4_Y
  attribute \src "asicworld/verilog/code_verilog_tutorial_counter.v:13.5-13.18"
  wire $eq$asicworld/verilog/code_verilog_tutorial_counter.v:13$2_Y
  attribute \src "asicworld/verilog/code_verilog_tutorial_counter.v:15.15-15.29"
  wire $eq$asicworld/verilog/code_verilog_tutorial_counter.v:15$3_Y
  attribute \src "asicworld/verilog/code_verilog_tutorial_counter.v:8.7-8.10"
  wire input 1 \clk
  attribute \src "asicworld/verilog/code_verilog_tutorial_counter.v:9.14-9.19"
  wire width 4 output 4 \count
  attribute \src "asicworld/verilog/code_verilog_tutorial_counter.v:8.19-8.25"
  wire input 3 \enable
  attribute \src "asicworld/verilog/code_verilog_tutorial_counter.v:8.12-8.17"
  wire input 2 \reset
  attribute \src "asicworld/verilog/code_verilog_tutorial_counter.v:16.12-16.21"
  cell $add $add$asicworld/verilog/code_verilog_tutorial_counter.v:16$4
    parameter \A_SIGNED 0
    parameter \A_WIDTH 4
    parameter \B_SIGNED 0
    parameter \B_WIDTH 32
    parameter \Y_WIDTH 32
    connect \A \count
    connect \B 1
    connect \Y $add$asicworld/verilog/code_verilog_tutorial_counter.v:16$4_Y
  end
  attribute \src "asicworld/verilog/code_verilog_tutorial_counter.v:13.5-13.18"
  cell $eq $eq$asicworld/verilog/code_verilog_tutorial_counter.v:13$2
    parameter \A_SIGNED 0
    parameter \A_WIDTH 1
    parameter \B_SIGNED 0
    parameter \B_WIDTH 1
    parameter \Y_WIDTH 1
    connect \A \reset
    connect \B 1'1
    connect \Y $eq$asicworld/verilog/code_verilog_tutorial_counter.v:13$2_Y
  end
  attribute \src "asicworld/verilog/code_verilog_tutorial_counter.v:15.15-15.29"
  cell $eq $eq$asicworld/verilog/code_verilog_tutorial_counter.v:15$3
    parameter \A_SIGNED 0
    parameter \A_WIDTH 1
    parameter \B_SIGNED 0
    parameter \B_WIDTH 1
    parameter \Y_WIDTH 1
    connect \A \enable
    connect \B 1'1
    connect \Y $eq$asicworld/verilog/code_verilog_tutorial_counter.v:15$3_Y
  end
  attribute \src "asicworld/verilog/code_verilog_tutorial_counter.v:12.1-17.4"
  process $proc$asicworld/verilog/code_verilog_tutorial_counter.v:12$1
    assign $0\count[3:0] \count
    attribute \src "asicworld/verilog/code_verilog_tutorial_counter.v:13.1-17.4"
    switch $eq$asicworld/verilog/code_verilog_tutorial_counter.v:13$2_Y
      attribute \src "asicworld/verilog/code_verilog_tutorial_counter.v:13.5-13.18"
      case 1'1
        assign $0\count[3:0] 4'0000
      attribute \src "asicworld/verilog/code_verilog_tutorial_counter.v:15.5-15.9"
      case 
        attribute \src "asicworld/verilog/code_verilog_tutorial_counter.v:15.10-17.4"
        switch $eq$asicworld/verilog/code_verilog_tutorial_counter.v:15$3_Y
          attribute \src "asicworld/verilog/code_verilog_tutorial_counter.v:15.15-15.29"
          case 1'1
            assign $0\count[3:0] $add$asicworld/verilog/code_verilog_tutorial_counter.v:16$4_Y [3:0]
          case 
        end
    end
    sync posedge \clk
      update \count $0\count[3:0]
  end
end
