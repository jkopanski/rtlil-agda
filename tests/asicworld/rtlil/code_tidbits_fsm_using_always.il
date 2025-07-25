autoidx 10
attribute \dynports 1
attribute \cells_not_processed 1
attribute \src "asicworld/verilog/code_tidbits_fsm_using_always.v:6.1-91.10"
module \fsm_using_always
  parameter \SIZE 3
  parameter \IDLE 3'001
  parameter \GNT0 3'010
  parameter \GNT1 3'100
  attribute \src "asicworld/verilog/code_tidbits_fsm_using_always.v:63.1-89.4"
  wire $0\gnt_0[0:0]
  attribute \src "asicworld/verilog/code_tidbits_fsm_using_always.v:63.1-89.4"
  wire $0\gnt_1[0:0]
  attribute \src "asicworld/verilog/code_tidbits_fsm_using_always.v:29.1-52.4"
  wire width 3 $0\next_state[2:0]
  attribute \src "asicworld/verilog/code_tidbits_fsm_using_always.v:54.1-61.4"
  wire width 3 $0\state[2:0]
  attribute \src "asicworld/verilog/code_tidbits_fsm_using_always.v:29.1-52.4"
  wire width 3 $1\next_state[2:0]
  attribute \src "asicworld/verilog/code_tidbits_fsm_using_always.v:29.1-52.4"
  wire width 3 $2\next_state[2:0]
  attribute \src "asicworld/verilog/code_tidbits_fsm_using_always.v:29.1-52.4"
  wire width 3 $3\next_state[2:0]
  attribute \src "asicworld/verilog/code_tidbits_fsm_using_always.v:29.1-52.4"
  wire width 3 $4\next_state[2:0]
  attribute \src "asicworld/verilog/code_tidbits_fsm_using_always.v:29.1-52.4"
  wire width 3 $5\next_state[2:0]
  attribute \src "asicworld/verilog/code_tidbits_fsm_using_always.v:33.15-33.28"
  wire $eq$asicworld/verilog/code_tidbits_fsm_using_always.v:33$2_Y
  attribute \src "asicworld/verilog/code_tidbits_fsm_using_always.v:35.28-35.41"
  wire $eq$asicworld/verilog/code_tidbits_fsm_using_always.v:35$3_Y
  attribute \src "asicworld/verilog/code_tidbits_fsm_using_always.v:40.15-40.28"
  wire $eq$asicworld/verilog/code_tidbits_fsm_using_always.v:40$4_Y
  attribute \src "asicworld/verilog/code_tidbits_fsm_using_always.v:45.15-45.28"
  wire $eq$asicworld/verilog/code_tidbits_fsm_using_always.v:45$5_Y
  attribute \src "asicworld/verilog/code_tidbits_fsm_using_always.v:56.7-56.20"
  wire $eq$asicworld/verilog/code_tidbits_fsm_using_always.v:56$7_Y
  attribute \src "asicworld/verilog/code_tidbits_fsm_using_always.v:65.5-65.18"
  wire $eq$asicworld/verilog/code_tidbits_fsm_using_always.v:65$9_Y
  attribute \src "asicworld/verilog/code_tidbits_fsm_using_always.v:15.9-15.14"
  wire input 1 \clock
  attribute \src "asicworld/verilog/code_tidbits_fsm_using_always.v:17.9-17.14"
  wire output 5 \gnt_0
  attribute \src "asicworld/verilog/code_tidbits_fsm_using_always.v:17.15-17.20"
  wire output 6 \gnt_1
  attribute \src "asicworld/verilog/code_tidbits_fsm_using_always.v:27.27-27.37"
  wire width 3 \next_state
  attribute \src "asicworld/verilog/code_tidbits_fsm_using_always.v:15.21-15.26"
  wire input 3 \req_0
  attribute \src "asicworld/verilog/code_tidbits_fsm_using_always.v:15.27-15.32"
  wire input 4 \req_1
  attribute \src "asicworld/verilog/code_tidbits_fsm_using_always.v:15.15-15.20"
  wire input 2 \reset
  attribute \src "asicworld/verilog/code_tidbits_fsm_using_always.v:26.27-26.32"
  wire width 3 \state
  attribute \src "asicworld/verilog/code_tidbits_fsm_using_always.v:33.15-33.28"
  cell $eq $eq$asicworld/verilog/code_tidbits_fsm_using_always.v:33$2
    parameter \A_SIGNED 0
    parameter \A_WIDTH 1
    parameter \B_SIGNED 0
    parameter \B_WIDTH 1
    parameter \Y_WIDTH 1
    connect \A \req_0
    connect \B 1'1
    connect \Y $eq$asicworld/verilog/code_tidbits_fsm_using_always.v:33$2_Y
  end
  attribute \src "asicworld/verilog/code_tidbits_fsm_using_always.v:35.28-35.41"
  cell $eq $eq$asicworld/verilog/code_tidbits_fsm_using_always.v:35$3
    parameter \A_SIGNED 0
    parameter \A_WIDTH 1
    parameter \B_SIGNED 0
    parameter \B_WIDTH 1
    parameter \Y_WIDTH 1
    connect \A \req_1
    connect \B 1'1
    connect \Y $eq$asicworld/verilog/code_tidbits_fsm_using_always.v:35$3_Y
  end
  attribute \src "asicworld/verilog/code_tidbits_fsm_using_always.v:40.15-40.28"
  cell $eq $eq$asicworld/verilog/code_tidbits_fsm_using_always.v:40$4
    parameter \A_SIGNED 0
    parameter \A_WIDTH 1
    parameter \B_SIGNED 0
    parameter \B_WIDTH 1
    parameter \Y_WIDTH 1
    connect \A \req_0
    connect \B 1'1
    connect \Y $eq$asicworld/verilog/code_tidbits_fsm_using_always.v:40$4_Y
  end
  attribute \src "asicworld/verilog/code_tidbits_fsm_using_always.v:45.15-45.28"
  cell $eq $eq$asicworld/verilog/code_tidbits_fsm_using_always.v:45$5
    parameter \A_SIGNED 0
    parameter \A_WIDTH 1
    parameter \B_SIGNED 0
    parameter \B_WIDTH 1
    parameter \Y_WIDTH 1
    connect \A \req_1
    connect \B 1'1
    connect \Y $eq$asicworld/verilog/code_tidbits_fsm_using_always.v:45$5_Y
  end
  attribute \src "asicworld/verilog/code_tidbits_fsm_using_always.v:56.7-56.20"
  cell $eq $eq$asicworld/verilog/code_tidbits_fsm_using_always.v:56$7
    parameter \A_SIGNED 0
    parameter \A_WIDTH 1
    parameter \B_SIGNED 0
    parameter \B_WIDTH 1
    parameter \Y_WIDTH 1
    connect \A \reset
    connect \B 1'1
    connect \Y $eq$asicworld/verilog/code_tidbits_fsm_using_always.v:56$7_Y
  end
  attribute \src "asicworld/verilog/code_tidbits_fsm_using_always.v:65.5-65.18"
  cell $eq $eq$asicworld/verilog/code_tidbits_fsm_using_always.v:65$9
    parameter \A_SIGNED 0
    parameter \A_WIDTH 1
    parameter \B_SIGNED 0
    parameter \B_WIDTH 1
    parameter \Y_WIDTH 1
    connect \A \reset
    connect \B 1'1
    connect \Y $eq$asicworld/verilog/code_tidbits_fsm_using_always.v:65$9_Y
  end
  attribute \src "asicworld/verilog/code_tidbits_fsm_using_always.v:29.1-52.4"
  process $proc$asicworld/verilog/code_tidbits_fsm_using_always.v:29$1
    assign { } { }
    assign { } { }
    assign $0\next_state[2:0] $1\next_state[2:0]
    attribute \src "asicworld/verilog/code_tidbits_fsm_using_always.v:32.2-51.10"
    switch \state
      attribute \src "asicworld/verilog/code_tidbits_fsm_using_always.v:0.0-0.0"
      case 3'001
        assign { } { }
        assign $1\next_state[2:0] $2\next_state[2:0]
        attribute \src "asicworld/verilog/code_tidbits_fsm_using_always.v:33.11-39.18"
        switch $eq$asicworld/verilog/code_tidbits_fsm_using_always.v:33$2_Y
          attribute \src "asicworld/verilog/code_tidbits_fsm_using_always.v:33.15-33.28"
          case 1'1
            assign { } { }
            assign $2\next_state[2:0] 3'010
          attribute \src "asicworld/verilog/code_tidbits_fsm_using_always.v:35.19-35.23"
          case 
            assign { } { }
            assign $2\next_state[2:0] $3\next_state[2:0]
            attribute \src "asicworld/verilog/code_tidbits_fsm_using_always.v:35.24-39.18"
            switch $eq$asicworld/verilog/code_tidbits_fsm_using_always.v:35$3_Y
              attribute \src "asicworld/verilog/code_tidbits_fsm_using_always.v:35.28-35.41"
              case 1'1
                assign { } { }
                assign $3\next_state[2:0] 3'100
              attribute \src "asicworld/verilog/code_tidbits_fsm_using_always.v:37.19-37.23"
              case 
                assign { } { }
                assign $3\next_state[2:0] 3'001
            end
        end
      attribute \src "asicworld/verilog/code_tidbits_fsm_using_always.v:0.0-0.0"
      case 3'010
        assign { } { }
        assign $1\next_state[2:0] $4\next_state[2:0]
        attribute \src "asicworld/verilog/code_tidbits_fsm_using_always.v:40.11-44.18"
        switch $eq$asicworld/verilog/code_tidbits_fsm_using_always.v:40$4_Y
          attribute \src "asicworld/verilog/code_tidbits_fsm_using_always.v:40.15-40.28"
          case 1'1
            assign { } { }
            assign $4\next_state[2:0] 3'010
          attribute \src "asicworld/verilog/code_tidbits_fsm_using_always.v:42.19-42.23"
          case 
            assign { } { }
            assign $4\next_state[2:0] 3'001
        end
      attribute \src "asicworld/verilog/code_tidbits_fsm_using_always.v:0.0-0.0"
      case 3'100
        assign { } { }
        assign $1\next_state[2:0] $5\next_state[2:0]
        attribute \src "asicworld/verilog/code_tidbits_fsm_using_always.v:45.11-49.18"
        switch $eq$asicworld/verilog/code_tidbits_fsm_using_always.v:45$5_Y
          attribute \src "asicworld/verilog/code_tidbits_fsm_using_always.v:45.15-45.28"
          case 1'1
            assign { } { }
            assign $5\next_state[2:0] 3'100
          attribute \src "asicworld/verilog/code_tidbits_fsm_using_always.v:47.19-47.23"
          case 
            assign { } { }
            assign $5\next_state[2:0] 3'001
        end
      attribute \src "asicworld/verilog/code_tidbits_fsm_using_always.v:0.0-0.0"
      case 
        assign { } { }
        assign $1\next_state[2:0] 3'001
    end
    sync always
      update \next_state $0\next_state[2:0]
  end
  attribute \src "asicworld/verilog/code_tidbits_fsm_using_always.v:54.1-61.4"
  process $proc$asicworld/verilog/code_tidbits_fsm_using_always.v:54$6
    assign $0\state[2:0] \state
    attribute \src "asicworld/verilog/code_tidbits_fsm_using_always.v:56.3-60.6"
    switch $eq$asicworld/verilog/code_tidbits_fsm_using_always.v:56$7_Y
      attribute \src "asicworld/verilog/code_tidbits_fsm_using_always.v:56.7-56.20"
      case 1'1
        assign $0\state[2:0] 3'001
      attribute \src "asicworld/verilog/code_tidbits_fsm_using_always.v:58.7-58.11"
      case 
        assign $0\state[2:0] \next_state
    end
    sync posedge \clock
      update \state $0\state[2:0]
  end
  attribute \src "asicworld/verilog/code_tidbits_fsm_using_always.v:63.1-89.4"
  process $proc$asicworld/verilog/code_tidbits_fsm_using_always.v:63$8
    assign $0\gnt_0[0:0] \gnt_0
    assign $0\gnt_1[0:0] \gnt_1
    attribute \src "asicworld/verilog/code_tidbits_fsm_using_always.v:65.1-88.4"
    switch $eq$asicworld/verilog/code_tidbits_fsm_using_always.v:65$9_Y
      attribute \src "asicworld/verilog/code_tidbits_fsm_using_always.v:65.5-65.18"
      case 1'1
        assign $0\gnt_0[0:0] 1'0
        assign $0\gnt_1[0:0] 1'0
      attribute \src "asicworld/verilog/code_tidbits_fsm_using_always.v:69.1-69.5"
      case 
        attribute \src "asicworld/verilog/code_tidbits_fsm_using_always.v:70.3-87.10"
        switch \state
          attribute \src "asicworld/verilog/code_tidbits_fsm_using_always.v:0.0-0.0"
          case 3'001
            assign $0\gnt_0[0:0] 1'0
            assign $0\gnt_1[0:0] 1'0
          attribute \src "asicworld/verilog/code_tidbits_fsm_using_always.v:0.0-0.0"
          case 3'010
            assign $0\gnt_0[0:0] 1'1
            assign $0\gnt_1[0:0] 1'0
          attribute \src "asicworld/verilog/code_tidbits_fsm_using_always.v:0.0-0.0"
          case 3'100
            assign $0\gnt_0[0:0] 1'0
            assign $0\gnt_1[0:0] 1'1
          attribute \src "asicworld/verilog/code_tidbits_fsm_using_always.v:0.0-0.0"
          case 
            assign $0\gnt_0[0:0] 1'0
            assign $0\gnt_1[0:0] 1'0
        end
    end
    sync posedge \clock
      update \gnt_0 $0\gnt_0[0:0]
      update \gnt_1 $0\gnt_1[0:0]
  end
end
