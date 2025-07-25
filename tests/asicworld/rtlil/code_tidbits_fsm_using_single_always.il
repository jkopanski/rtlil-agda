autoidx 7
attribute \dynports 1
attribute \cells_not_processed 1
attribute \src "asicworld/verilog/code_tidbits_fsm_using_single_always.v:7.1-63.10"
module \fsm_using_single_always
  parameter \SIZE 3
  parameter \IDLE 3'001
  parameter \GNT0 3'010
  parameter \GNT1 3'100
  attribute \src "asicworld/verilog/code_tidbits_fsm_using_single_always.v:30.1-61.4"
  wire $0\gnt_0[0:0]
  attribute \src "asicworld/verilog/code_tidbits_fsm_using_single_always.v:30.1-61.4"
  wire $0\gnt_1[0:0]
  attribute \src "asicworld/verilog/code_tidbits_fsm_using_single_always.v:30.1-61.4"
  wire width 3 $0\state[2:0]
  attribute \src "asicworld/verilog/code_tidbits_fsm_using_single_always.v:32.5-32.18"
  wire $eq$asicworld/verilog/code_tidbits_fsm_using_single_always.v:32$2_Y
  attribute \src "asicworld/verilog/code_tidbits_fsm_using_single_always.v:38.15-38.28"
  wire $eq$asicworld/verilog/code_tidbits_fsm_using_single_always.v:38$3_Y
  attribute \src "asicworld/verilog/code_tidbits_fsm_using_single_always.v:41.28-41.41"
  wire $eq$asicworld/verilog/code_tidbits_fsm_using_single_always.v:41$4_Y
  attribute \src "asicworld/verilog/code_tidbits_fsm_using_single_always.v:47.15-47.28"
  wire $eq$asicworld/verilog/code_tidbits_fsm_using_single_always.v:47$5_Y
  attribute \src "asicworld/verilog/code_tidbits_fsm_using_single_always.v:53.15-53.28"
  wire $eq$asicworld/verilog/code_tidbits_fsm_using_single_always.v:53$6_Y
  attribute \src "asicworld/verilog/code_tidbits_fsm_using_single_always.v:16.9-16.14"
  wire input 1 \clock
  attribute \src "asicworld/verilog/code_tidbits_fsm_using_single_always.v:18.9-18.14"
  wire output 5 \gnt_0
  attribute \src "asicworld/verilog/code_tidbits_fsm_using_single_always.v:18.15-18.20"
  wire output 6 \gnt_1
  attribute \src "asicworld/verilog/code_tidbits_fsm_using_single_always.v:28.27-28.37"
  wire width 3 \next_state
  attribute \src "asicworld/verilog/code_tidbits_fsm_using_single_always.v:16.21-16.26"
  wire input 3 \req_0
  attribute \src "asicworld/verilog/code_tidbits_fsm_using_single_always.v:16.27-16.32"
  wire input 4 \req_1
  attribute \src "asicworld/verilog/code_tidbits_fsm_using_single_always.v:16.15-16.20"
  wire input 2 \reset
  attribute \src "asicworld/verilog/code_tidbits_fsm_using_single_always.v:27.27-27.32"
  wire width 3 \state
  attribute \src "asicworld/verilog/code_tidbits_fsm_using_single_always.v:32.5-32.18"
  cell $eq $eq$asicworld/verilog/code_tidbits_fsm_using_single_always.v:32$2
    parameter \A_SIGNED 0
    parameter \A_WIDTH 1
    parameter \B_SIGNED 0
    parameter \B_WIDTH 1
    parameter \Y_WIDTH 1
    connect \A \reset
    connect \B 1'1
    connect \Y $eq$asicworld/verilog/code_tidbits_fsm_using_single_always.v:32$2_Y
  end
  attribute \src "asicworld/verilog/code_tidbits_fsm_using_single_always.v:38.15-38.28"
  cell $eq $eq$asicworld/verilog/code_tidbits_fsm_using_single_always.v:38$3
    parameter \A_SIGNED 0
    parameter \A_WIDTH 1
    parameter \B_SIGNED 0
    parameter \B_WIDTH 1
    parameter \Y_WIDTH 1
    connect \A \req_0
    connect \B 1'1
    connect \Y $eq$asicworld/verilog/code_tidbits_fsm_using_single_always.v:38$3_Y
  end
  attribute \src "asicworld/verilog/code_tidbits_fsm_using_single_always.v:41.28-41.41"
  cell $eq $eq$asicworld/verilog/code_tidbits_fsm_using_single_always.v:41$4
    parameter \A_SIGNED 0
    parameter \A_WIDTH 1
    parameter \B_SIGNED 0
    parameter \B_WIDTH 1
    parameter \Y_WIDTH 1
    connect \A \req_1
    connect \B 1'1
    connect \Y $eq$asicworld/verilog/code_tidbits_fsm_using_single_always.v:41$4_Y
  end
  attribute \src "asicworld/verilog/code_tidbits_fsm_using_single_always.v:47.15-47.28"
  cell $eq $eq$asicworld/verilog/code_tidbits_fsm_using_single_always.v:47$5
    parameter \A_SIGNED 0
    parameter \A_WIDTH 1
    parameter \B_SIGNED 0
    parameter \B_WIDTH 1
    parameter \Y_WIDTH 1
    connect \A \req_0
    connect \B 1'1
    connect \Y $eq$asicworld/verilog/code_tidbits_fsm_using_single_always.v:47$5_Y
  end
  attribute \src "asicworld/verilog/code_tidbits_fsm_using_single_always.v:53.15-53.28"
  cell $eq $eq$asicworld/verilog/code_tidbits_fsm_using_single_always.v:53$6
    parameter \A_SIGNED 0
    parameter \A_WIDTH 1
    parameter \B_SIGNED 0
    parameter \B_WIDTH 1
    parameter \Y_WIDTH 1
    connect \A \req_1
    connect \B 1'1
    connect \Y $eq$asicworld/verilog/code_tidbits_fsm_using_single_always.v:53$6_Y
  end
  attribute \src "asicworld/verilog/code_tidbits_fsm_using_single_always.v:30.1-61.4"
  process $proc$asicworld/verilog/code_tidbits_fsm_using_single_always.v:30$1
    assign $0\gnt_0[0:0] \gnt_0
    assign $0\gnt_1[0:0] \gnt_1
    assign $0\state[2:0] \state
    attribute \src "asicworld/verilog/code_tidbits_fsm_using_single_always.v:32.1-60.8"
    switch $eq$asicworld/verilog/code_tidbits_fsm_using_single_always.v:32$2_Y
      attribute \src "asicworld/verilog/code_tidbits_fsm_using_single_always.v:32.5-32.18"
      case 1'1
        assign $0\state[2:0] 3'001
        assign $0\gnt_0[0:0] 1'0
        assign $0\gnt_1[0:0] 1'0
      attribute \src "asicworld/verilog/code_tidbits_fsm_using_single_always.v:36.5-36.9"
      case 
        attribute \src "asicworld/verilog/code_tidbits_fsm_using_single_always.v:37.2-60.8"
        switch \state
          attribute \src "asicworld/verilog/code_tidbits_fsm_using_single_always.v:0.0-0.0"
          case 3'001
            attribute \src "asicworld/verilog/code_tidbits_fsm_using_single_always.v:38.11-46.18"
            switch $eq$asicworld/verilog/code_tidbits_fsm_using_single_always.v:38$3_Y
              attribute \src "asicworld/verilog/code_tidbits_fsm_using_single_always.v:38.15-38.28"
              case 1'1
                assign $0\state[2:0] 3'010
                assign $0\gnt_0[0:0] 1'1
              attribute \src "asicworld/verilog/code_tidbits_fsm_using_single_always.v:41.19-41.23"
              case 
                attribute \src "asicworld/verilog/code_tidbits_fsm_using_single_always.v:41.24-46.18"
                switch $eq$asicworld/verilog/code_tidbits_fsm_using_single_always.v:41$4_Y
                  attribute \src "asicworld/verilog/code_tidbits_fsm_using_single_always.v:41.28-41.41"
                  case 1'1
                    assign $0\gnt_1[0:0] 1'1
                    assign $0\state[2:0] 3'100
                  attribute \src "asicworld/verilog/code_tidbits_fsm_using_single_always.v:44.19-44.23"
                  case 
                    assign $0\state[2:0] 3'001
                end
            end
          attribute \src "asicworld/verilog/code_tidbits_fsm_using_single_always.v:0.0-0.0"
          case 3'010
            attribute \src "asicworld/verilog/code_tidbits_fsm_using_single_always.v:47.11-52.18"
            switch $eq$asicworld/verilog/code_tidbits_fsm_using_single_always.v:47$5_Y
              attribute \src "asicworld/verilog/code_tidbits_fsm_using_single_always.v:47.15-47.28"
              case 1'1
                assign $0\state[2:0] 3'010
              attribute \src "asicworld/verilog/code_tidbits_fsm_using_single_always.v:49.19-49.23"
              case 
                assign $0\gnt_0[0:0] 1'0
                assign $0\state[2:0] 3'001
            end
          attribute \src "asicworld/verilog/code_tidbits_fsm_using_single_always.v:0.0-0.0"
          case 3'100
            attribute \src "asicworld/verilog/code_tidbits_fsm_using_single_always.v:53.11-58.18"
            switch $eq$asicworld/verilog/code_tidbits_fsm_using_single_always.v:53$6_Y
              attribute \src "asicworld/verilog/code_tidbits_fsm_using_single_always.v:53.15-53.28"
              case 1'1
                assign $0\state[2:0] 3'100
              attribute \src "asicworld/verilog/code_tidbits_fsm_using_single_always.v:55.19-55.23"
              case 
                assign $0\gnt_1[0:0] 1'0
                assign $0\state[2:0] 3'001
            end
          attribute \src "asicworld/verilog/code_tidbits_fsm_using_single_always.v:0.0-0.0"
          case 
            assign $0\state[2:0] 3'001
        end
    end
    sync posedge \clock
      update \gnt_0 $0\gnt_0[0:0]
      update \gnt_1 $0\gnt_1[0:0]
      update \state $0\state[2:0]
  end
end
