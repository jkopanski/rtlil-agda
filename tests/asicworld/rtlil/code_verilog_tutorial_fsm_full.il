autoidx 11
attribute \cells_not_processed 1
attribute \src "asicworld/verilog/code_verilog_tutorial_fsm_full.v:1.1-114.10"
module \fsm_full
  parameter \IDLE 3'000
  parameter \GNT0 3'001
  parameter \GNT1 3'010
  parameter \GNT2 3'011
  parameter \GNT3 3'100
  attribute \src "asicworld/verilog/code_verilog_tutorial_fsm_full.v:78.1-112.4"
  wire $0\gnt_0[0:0]
  attribute \src "asicworld/verilog/code_verilog_tutorial_fsm_full.v:78.1-112.4"
  wire $0\gnt_1[0:0]
  attribute \src "asicworld/verilog/code_verilog_tutorial_fsm_full.v:78.1-112.4"
  wire $0\gnt_2[0:0]
  attribute \src "asicworld/verilog/code_verilog_tutorial_fsm_full.v:78.1-112.4"
  wire $0\gnt_3[0:0]
  attribute \src "asicworld/verilog/code_verilog_tutorial_fsm_full.v:39.1-76.4"
  wire width 3 $0\next_state[2:0]
  attribute \src "asicworld/verilog/code_verilog_tutorial_fsm_full.v:78.1-112.4"
  wire width 3 $0\state[2:0]
  attribute \src "asicworld/verilog/code_verilog_tutorial_fsm_full.v:39.1-76.4"
  wire width 3 $1\next_state[2:0]
  attribute \src "asicworld/verilog/code_verilog_tutorial_fsm_full.v:39.1-76.4"
  wire width 3 $2\next_state[2:0]
  attribute \src "asicworld/verilog/code_verilog_tutorial_fsm_full.v:39.1-76.4"
  wire width 3 $3\next_state[2:0]
  attribute \src "asicworld/verilog/code_verilog_tutorial_fsm_full.v:39.1-76.4"
  wire width 3 $4\next_state[2:0]
  attribute \src "asicworld/verilog/code_verilog_tutorial_fsm_full.v:39.1-76.4"
  wire width 3 $5\next_state[2:0]
  attribute \src "asicworld/verilog/code_verilog_tutorial_fsm_full.v:39.1-76.4"
  wire width 3 $6\next_state[2:0]
  attribute \src "asicworld/verilog/code_verilog_tutorial_fsm_full.v:39.1-76.4"
  wire width 3 $7\next_state[2:0]
  attribute \src "asicworld/verilog/code_verilog_tutorial_fsm_full.v:39.1-76.4"
  wire width 3 $8\next_state[2:0]
  attribute \src "asicworld/verilog/code_verilog_tutorial_fsm_full.v:39.1-76.4"
  wire width 3 $9\next_state[2:0]
  attribute \src "asicworld/verilog/code_verilog_tutorial_fsm_full.v:43.16-43.29"
  wire $eq$asicworld/verilog/code_verilog_tutorial_fsm_full.v:43$2_Y
  attribute \src "asicworld/verilog/code_verilog_tutorial_fsm_full.v:45.25-45.38"
  wire $eq$asicworld/verilog/code_verilog_tutorial_fsm_full.v:45$3_Y
  attribute \src "asicworld/verilog/code_verilog_tutorial_fsm_full.v:47.25-47.38"
  wire $eq$asicworld/verilog/code_verilog_tutorial_fsm_full.v:47$4_Y
  attribute \src "asicworld/verilog/code_verilog_tutorial_fsm_full.v:49.25-49.38"
  wire $eq$asicworld/verilog/code_verilog_tutorial_fsm_full.v:49$5_Y
  attribute \src "asicworld/verilog/code_verilog_tutorial_fsm_full.v:54.16-54.29"
  wire $eq$asicworld/verilog/code_verilog_tutorial_fsm_full.v:54$6_Y
  attribute \src "asicworld/verilog/code_verilog_tutorial_fsm_full.v:59.16-59.29"
  wire $eq$asicworld/verilog/code_verilog_tutorial_fsm_full.v:59$7_Y
  attribute \src "asicworld/verilog/code_verilog_tutorial_fsm_full.v:64.16-64.29"
  wire $eq$asicworld/verilog/code_verilog_tutorial_fsm_full.v:64$8_Y
  attribute \src "asicworld/verilog/code_verilog_tutorial_fsm_full.v:69.16-69.29"
  wire $eq$asicworld/verilog/code_verilog_tutorial_fsm_full.v:69$9_Y
  attribute \src "asicworld/verilog/code_verilog_tutorial_fsm_full.v:14.7-14.12"
  wire input 1 \clock
  attribute \src "asicworld/verilog/code_verilog_tutorial_fsm_full.v:20.8-20.13"
  wire output 7 \gnt_0
  attribute \src "asicworld/verilog/code_verilog_tutorial_fsm_full.v:21.8-21.13"
  wire output 8 \gnt_1
  attribute \src "asicworld/verilog/code_verilog_tutorial_fsm_full.v:22.8-22.13"
  wire output 9 \gnt_2
  attribute \src "asicworld/verilog/code_verilog_tutorial_fsm_full.v:23.8-23.13"
  wire output 10 \gnt_3
  attribute \src "asicworld/verilog/code_verilog_tutorial_fsm_full.v:37.18-37.28"
  wire width 3 \next_state
  attribute \src "asicworld/verilog/code_verilog_tutorial_fsm_full.v:16.7-16.12"
  wire input 3 \req_0
  attribute \src "asicworld/verilog/code_verilog_tutorial_fsm_full.v:17.7-17.12"
  wire input 4 \req_1
  attribute \src "asicworld/verilog/code_verilog_tutorial_fsm_full.v:18.7-18.12"
  wire input 5 \req_2
  attribute \src "asicworld/verilog/code_verilog_tutorial_fsm_full.v:19.7-19.12"
  wire input 6 \req_3
  attribute \src "asicworld/verilog/code_verilog_tutorial_fsm_full.v:15.7-15.12"
  wire input 2 \reset
  attribute \src "asicworld/verilog/code_verilog_tutorial_fsm_full.v:37.11-37.16"
  wire width 3 \state
  attribute \src "asicworld/verilog/code_verilog_tutorial_fsm_full.v:43.16-43.29"
  cell $eq $eq$asicworld/verilog/code_verilog_tutorial_fsm_full.v:43$2
    parameter \A_SIGNED 0
    parameter \A_WIDTH 1
    parameter \B_SIGNED 0
    parameter \B_WIDTH 1
    parameter \Y_WIDTH 1
    connect \A \req_0
    connect \B 1'1
    connect \Y $eq$asicworld/verilog/code_verilog_tutorial_fsm_full.v:43$2_Y
  end
  attribute \src "asicworld/verilog/code_verilog_tutorial_fsm_full.v:45.25-45.38"
  cell $eq $eq$asicworld/verilog/code_verilog_tutorial_fsm_full.v:45$3
    parameter \A_SIGNED 0
    parameter \A_WIDTH 1
    parameter \B_SIGNED 0
    parameter \B_WIDTH 1
    parameter \Y_WIDTH 1
    connect \A \req_1
    connect \B 1'1
    connect \Y $eq$asicworld/verilog/code_verilog_tutorial_fsm_full.v:45$3_Y
  end
  attribute \src "asicworld/verilog/code_verilog_tutorial_fsm_full.v:47.25-47.38"
  cell $eq $eq$asicworld/verilog/code_verilog_tutorial_fsm_full.v:47$4
    parameter \A_SIGNED 0
    parameter \A_WIDTH 1
    parameter \B_SIGNED 0
    parameter \B_WIDTH 1
    parameter \Y_WIDTH 1
    connect \A \req_2
    connect \B 1'1
    connect \Y $eq$asicworld/verilog/code_verilog_tutorial_fsm_full.v:47$4_Y
  end
  attribute \src "asicworld/verilog/code_verilog_tutorial_fsm_full.v:49.25-49.38"
  cell $eq $eq$asicworld/verilog/code_verilog_tutorial_fsm_full.v:49$5
    parameter \A_SIGNED 0
    parameter \A_WIDTH 1
    parameter \B_SIGNED 0
    parameter \B_WIDTH 1
    parameter \Y_WIDTH 1
    connect \A \req_3
    connect \B 1'1
    connect \Y $eq$asicworld/verilog/code_verilog_tutorial_fsm_full.v:49$5_Y
  end
  attribute \src "asicworld/verilog/code_verilog_tutorial_fsm_full.v:54.16-54.29"
  cell $eq $eq$asicworld/verilog/code_verilog_tutorial_fsm_full.v:54$6
    parameter \A_SIGNED 0
    parameter \A_WIDTH 1
    parameter \B_SIGNED 0
    parameter \B_WIDTH 1
    parameter \Y_WIDTH 1
    connect \A \req_0
    connect \B 1'0
    connect \Y $eq$asicworld/verilog/code_verilog_tutorial_fsm_full.v:54$6_Y
  end
  attribute \src "asicworld/verilog/code_verilog_tutorial_fsm_full.v:59.16-59.29"
  cell $eq $eq$asicworld/verilog/code_verilog_tutorial_fsm_full.v:59$7
    parameter \A_SIGNED 0
    parameter \A_WIDTH 1
    parameter \B_SIGNED 0
    parameter \B_WIDTH 1
    parameter \Y_WIDTH 1
    connect \A \req_1
    connect \B 1'0
    connect \Y $eq$asicworld/verilog/code_verilog_tutorial_fsm_full.v:59$7_Y
  end
  attribute \src "asicworld/verilog/code_verilog_tutorial_fsm_full.v:64.16-64.29"
  cell $eq $eq$asicworld/verilog/code_verilog_tutorial_fsm_full.v:64$8
    parameter \A_SIGNED 0
    parameter \A_WIDTH 1
    parameter \B_SIGNED 0
    parameter \B_WIDTH 1
    parameter \Y_WIDTH 1
    connect \A \req_2
    connect \B 1'0
    connect \Y $eq$asicworld/verilog/code_verilog_tutorial_fsm_full.v:64$8_Y
  end
  attribute \src "asicworld/verilog/code_verilog_tutorial_fsm_full.v:69.16-69.29"
  cell $eq $eq$asicworld/verilog/code_verilog_tutorial_fsm_full.v:69$9
    parameter \A_SIGNED 0
    parameter \A_WIDTH 1
    parameter \B_SIGNED 0
    parameter \B_WIDTH 1
    parameter \Y_WIDTH 1
    connect \A \req_3
    connect \B 1'0
    connect \Y $eq$asicworld/verilog/code_verilog_tutorial_fsm_full.v:69$9_Y
  end
  attribute \src "asicworld/verilog/code_verilog_tutorial_fsm_full.v:39.1-76.4"
  process $proc$asicworld/verilog/code_verilog_tutorial_fsm_full.v:39$1
    assign { } { }
    assign { } { }
    assign $0\next_state[2:0] $1\next_state[2:0]
    attribute \src "asicworld/verilog/code_verilog_tutorial_fsm_full.v:42.3-75.10"
    switch \state
      attribute \src "asicworld/verilog/code_verilog_tutorial_fsm_full.v:0.0-0.0"
      case 3'000
        assign { } { }
        assign $1\next_state[2:0] $2\next_state[2:0]
        attribute \src "asicworld/verilog/code_verilog_tutorial_fsm_full.v:43.12-53.15"
        switch $eq$asicworld/verilog/code_verilog_tutorial_fsm_full.v:43$2_Y
          attribute \src "asicworld/verilog/code_verilog_tutorial_fsm_full.v:43.16-43.29"
          case 1'1
            assign { } { }
            assign $2\next_state[2:0] 3'001
          attribute \src "asicworld/verilog/code_verilog_tutorial_fsm_full.v:45.16-45.20"
          case 
            assign { } { }
            assign $2\next_state[2:0] $3\next_state[2:0]
            attribute \src "asicworld/verilog/code_verilog_tutorial_fsm_full.v:45.21-53.15"
            switch $eq$asicworld/verilog/code_verilog_tutorial_fsm_full.v:45$3_Y
              attribute \src "asicworld/verilog/code_verilog_tutorial_fsm_full.v:45.25-45.38"
              case 1'1
                assign { } { }
                assign $3\next_state[2:0] 3'010
              attribute \src "asicworld/verilog/code_verilog_tutorial_fsm_full.v:47.16-47.20"
              case 
                assign { } { }
                assign $3\next_state[2:0] $4\next_state[2:0]
                attribute \src "asicworld/verilog/code_verilog_tutorial_fsm_full.v:47.21-53.15"
                switch $eq$asicworld/verilog/code_verilog_tutorial_fsm_full.v:47$4_Y
                  attribute \src "asicworld/verilog/code_verilog_tutorial_fsm_full.v:47.25-47.38"
                  case 1'1
                    assign { } { }
                    assign $4\next_state[2:0] 3'011
                  attribute \src "asicworld/verilog/code_verilog_tutorial_fsm_full.v:49.16-49.20"
                  case 
                    assign { } { }
                    assign $4\next_state[2:0] $5\next_state[2:0]
                    attribute \src "asicworld/verilog/code_verilog_tutorial_fsm_full.v:49.21-53.15"
                    switch $eq$asicworld/verilog/code_verilog_tutorial_fsm_full.v:49$5_Y
                      attribute \src "asicworld/verilog/code_verilog_tutorial_fsm_full.v:49.25-49.38"
                      case 1'1
                        assign { } { }
                        assign $5\next_state[2:0] 3'100
                      attribute \src "asicworld/verilog/code_verilog_tutorial_fsm_full.v:51.9-51.13"
                      case 
                        assign { } { }
                        assign $5\next_state[2:0] 3'000
                    end
                end
            end
        end
      attribute \src "asicworld/verilog/code_verilog_tutorial_fsm_full.v:0.0-0.0"
      case 3'001
        assign { } { }
        assign $1\next_state[2:0] $6\next_state[2:0]
        attribute \src "asicworld/verilog/code_verilog_tutorial_fsm_full.v:54.12-58.7"
        switch $eq$asicworld/verilog/code_verilog_tutorial_fsm_full.v:54$6_Y
          attribute \src "asicworld/verilog/code_verilog_tutorial_fsm_full.v:54.16-54.29"
          case 1'1
            assign { } { }
            assign $6\next_state[2:0] 3'000
          attribute \src "asicworld/verilog/code_verilog_tutorial_fsm_full.v:56.16-56.20"
          case 
            assign { } { }
            assign $6\next_state[2:0] 3'001
        end
      attribute \src "asicworld/verilog/code_verilog_tutorial_fsm_full.v:0.0-0.0"
      case 3'010
        assign { } { }
        assign $1\next_state[2:0] $7\next_state[2:0]
        attribute \src "asicworld/verilog/code_verilog_tutorial_fsm_full.v:59.12-63.7"
        switch $eq$asicworld/verilog/code_verilog_tutorial_fsm_full.v:59$7_Y
          attribute \src "asicworld/verilog/code_verilog_tutorial_fsm_full.v:59.16-59.29"
          case 1'1
            assign { } { }
            assign $7\next_state[2:0] 3'000
          attribute \src "asicworld/verilog/code_verilog_tutorial_fsm_full.v:61.16-61.20"
          case 
            assign { } { }
            assign $7\next_state[2:0] 3'010
        end
      attribute \src "asicworld/verilog/code_verilog_tutorial_fsm_full.v:0.0-0.0"
      case 3'011
        assign { } { }
        assign $1\next_state[2:0] $8\next_state[2:0]
        attribute \src "asicworld/verilog/code_verilog_tutorial_fsm_full.v:64.12-68.7"
        switch $eq$asicworld/verilog/code_verilog_tutorial_fsm_full.v:64$8_Y
          attribute \src "asicworld/verilog/code_verilog_tutorial_fsm_full.v:64.16-64.29"
          case 1'1
            assign { } { }
            assign $8\next_state[2:0] 3'000
          attribute \src "asicworld/verilog/code_verilog_tutorial_fsm_full.v:66.16-66.20"
          case 
            assign { } { }
            assign $8\next_state[2:0] 3'011
        end
      attribute \src "asicworld/verilog/code_verilog_tutorial_fsm_full.v:0.0-0.0"
      case 3'100
        assign { } { }
        assign $1\next_state[2:0] $9\next_state[2:0]
        attribute \src "asicworld/verilog/code_verilog_tutorial_fsm_full.v:69.12-73.7"
        switch $eq$asicworld/verilog/code_verilog_tutorial_fsm_full.v:69$9_Y
          attribute \src "asicworld/verilog/code_verilog_tutorial_fsm_full.v:69.16-69.29"
          case 1'1
            assign { } { }
            assign $9\next_state[2:0] 3'000
          attribute \src "asicworld/verilog/code_verilog_tutorial_fsm_full.v:71.16-71.20"
          case 
            assign { } { }
            assign $9\next_state[2:0] 3'100
        end
      attribute \src "asicworld/verilog/code_verilog_tutorial_fsm_full.v:0.0-0.0"
      case 
        assign { } { }
        assign $1\next_state[2:0] 3'000
    end
    sync always
      update \next_state $0\next_state[2:0]
  end
  attribute \src "asicworld/verilog/code_verilog_tutorial_fsm_full.v:78.1-112.4"
  process $proc$asicworld/verilog/code_verilog_tutorial_fsm_full.v:78$10
    assign $0\gnt_0[0:0] \gnt_0
    assign $0\gnt_1[0:0] \gnt_1
    assign $0\gnt_2[0:0] \gnt_2
    assign $0\gnt_3[0:0] \gnt_3
    assign $0\state[2:0] \state
    attribute \src "asicworld/verilog/code_verilog_tutorial_fsm_full.v:80.3-111.6"
    switch \reset
      attribute \src "asicworld/verilog/code_verilog_tutorial_fsm_full.v:80.7-80.12"
      case 1'1
        assign $0\gnt_0[0:0] 1'0
        assign $0\gnt_1[0:0] 1'0
        assign $0\gnt_2[0:0] 1'0
        assign $0\gnt_3[0:0] 1'0
        assign $0\state[2:0] 3'000
      attribute \src "asicworld/verilog/code_verilog_tutorial_fsm_full.v:86.7-86.11"
      case 
        assign $0\state[2:0] \next_state
        attribute \src "asicworld/verilog/code_verilog_tutorial_fsm_full.v:88.5-110.12"
        switch \state
          attribute \src "asicworld/verilog/code_verilog_tutorial_fsm_full.v:0.0-0.0"
          case 3'000
            assign $0\gnt_0[0:0] 1'0
            assign $0\gnt_1[0:0] 1'0
            assign $0\gnt_2[0:0] 1'0
            assign $0\gnt_3[0:0] 1'0
          attribute \src "asicworld/verilog/code_verilog_tutorial_fsm_full.v:0.0-0.0"
          case 3'001
            assign $0\gnt_0[0:0] 1'1
          attribute \src "asicworld/verilog/code_verilog_tutorial_fsm_full.v:0.0-0.0"
          case 3'010
            assign $0\gnt_1[0:0] 1'1
          attribute \src "asicworld/verilog/code_verilog_tutorial_fsm_full.v:0.0-0.0"
          case 3'011
            assign $0\gnt_2[0:0] 1'1
          attribute \src "asicworld/verilog/code_verilog_tutorial_fsm_full.v:0.0-0.0"
          case 3'100
            assign $0\gnt_3[0:0] 1'1
          attribute \src "asicworld/verilog/code_verilog_tutorial_fsm_full.v:0.0-0.0"
          case 
            assign $0\state[2:0] 3'000
        end
    end
    sync posedge \clock
      update \gnt_0 $0\gnt_0[0:0]
      update \gnt_1 $0\gnt_1[0:0]
      update \gnt_2 $0\gnt_2[0:0]
      update \gnt_3 $0\gnt_3[0:0]
      update \state $0\state[2:0]
  end
end
