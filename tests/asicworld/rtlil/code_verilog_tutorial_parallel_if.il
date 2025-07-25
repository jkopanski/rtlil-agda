autoidx 11
attribute \cells_not_processed 1
attribute \src "asicworld/verilog/code_verilog_tutorial_parallel_if.v:1.1-21.10"
module \parallel_if
  attribute \src "asicworld/verilog/code_verilog_tutorial_parallel_if.v:6.1-19.4"
  wire width 4 $0\counter[3:0]
  attribute \src "asicworld/verilog/code_verilog_tutorial_parallel_if.v:13.16-13.30"
  wire width 4 $add$asicworld/verilog/code_verilog_tutorial_parallel_if.v:13$6_Y
  attribute \src "asicworld/verilog/code_verilog_tutorial_parallel_if.v:12.7-12.21"
  wire $eq$asicworld/verilog/code_verilog_tutorial_parallel_if.v:12$3_Y
  attribute \src "asicworld/verilog/code_verilog_tutorial_parallel_if.v:12.25-12.38"
  wire $eq$asicworld/verilog/code_verilog_tutorial_parallel_if.v:12$4_Y
  attribute \src "asicworld/verilog/code_verilog_tutorial_parallel_if.v:16.7-16.21"
  wire $eq$asicworld/verilog/code_verilog_tutorial_parallel_if.v:16$7_Y
  attribute \src "asicworld/verilog/code_verilog_tutorial_parallel_if.v:16.25-16.40"
  wire $eq$asicworld/verilog/code_verilog_tutorial_parallel_if.v:16$8_Y
  attribute \src "asicworld/verilog/code_verilog_tutorial_parallel_if.v:8.5-8.18"
  wire $eq$asicworld/verilog/code_verilog_tutorial_parallel_if.v:8$2_Y
  attribute \src "asicworld/verilog/code_verilog_tutorial_parallel_if.v:12.7-12.38"
  wire $logic_and$asicworld/verilog/code_verilog_tutorial_parallel_if.v:12$5_Y
  attribute \src "asicworld/verilog/code_verilog_tutorial_parallel_if.v:16.7-16.40"
  wire $logic_and$asicworld/verilog/code_verilog_tutorial_parallel_if.v:16$9_Y
  attribute \src "asicworld/verilog/code_verilog_tutorial_parallel_if.v:17.16-17.30"
  wire width 4 $sub$asicworld/verilog/code_verilog_tutorial_parallel_if.v:17$10_Y
  attribute \src "asicworld/verilog/code_verilog_tutorial_parallel_if.v:4.6-4.9"
  wire \clk
  attribute \src "asicworld/verilog/code_verilog_tutorial_parallel_if.v:3.11-3.18"
  wire width 4 \counter
  attribute \src "asicworld/verilog/code_verilog_tutorial_parallel_if.v:4.31-4.38"
  wire \down_en
  attribute \src "asicworld/verilog/code_verilog_tutorial_parallel_if.v:4.16-4.22"
  wire \enable
  attribute \src "asicworld/verilog/code_verilog_tutorial_parallel_if.v:4.10-4.15"
  wire \reset
  attribute \src "asicworld/verilog/code_verilog_tutorial_parallel_if.v:4.24-4.29"
  wire \up_en
  attribute \src "asicworld/verilog/code_verilog_tutorial_parallel_if.v:13.16-13.30"
  cell $add $add$asicworld/verilog/code_verilog_tutorial_parallel_if.v:13$6
    parameter \A_SIGNED 0
    parameter \A_WIDTH 4
    parameter \B_SIGNED 0
    parameter \B_WIDTH 1
    parameter \Y_WIDTH 4
    connect \A \counter
    connect \B 1'1
    connect \Y $add$asicworld/verilog/code_verilog_tutorial_parallel_if.v:13$6_Y
  end
  attribute \src "asicworld/verilog/code_verilog_tutorial_parallel_if.v:12.7-12.21"
  cell $eq $eq$asicworld/verilog/code_verilog_tutorial_parallel_if.v:12$3
    parameter \A_SIGNED 0
    parameter \A_WIDTH 1
    parameter \B_SIGNED 0
    parameter \B_WIDTH 1
    parameter \Y_WIDTH 1
    connect \A \enable
    connect \B 1'1
    connect \Y $eq$asicworld/verilog/code_verilog_tutorial_parallel_if.v:12$3_Y
  end
  attribute \src "asicworld/verilog/code_verilog_tutorial_parallel_if.v:12.25-12.38"
  cell $eq $eq$asicworld/verilog/code_verilog_tutorial_parallel_if.v:12$4
    parameter \A_SIGNED 0
    parameter \A_WIDTH 1
    parameter \B_SIGNED 0
    parameter \B_WIDTH 1
    parameter \Y_WIDTH 1
    connect \A \up_en
    connect \B 1'1
    connect \Y $eq$asicworld/verilog/code_verilog_tutorial_parallel_if.v:12$4_Y
  end
  attribute \src "asicworld/verilog/code_verilog_tutorial_parallel_if.v:16.7-16.21"
  cell $eq $eq$asicworld/verilog/code_verilog_tutorial_parallel_if.v:16$7
    parameter \A_SIGNED 0
    parameter \A_WIDTH 1
    parameter \B_SIGNED 0
    parameter \B_WIDTH 1
    parameter \Y_WIDTH 1
    connect \A \enable
    connect \B 1'1
    connect \Y $eq$asicworld/verilog/code_verilog_tutorial_parallel_if.v:16$7_Y
  end
  attribute \src "asicworld/verilog/code_verilog_tutorial_parallel_if.v:16.25-16.40"
  cell $eq $eq$asicworld/verilog/code_verilog_tutorial_parallel_if.v:16$8
    parameter \A_SIGNED 0
    parameter \A_WIDTH 1
    parameter \B_SIGNED 0
    parameter \B_WIDTH 1
    parameter \Y_WIDTH 1
    connect \A \down_en
    connect \B 1'1
    connect \Y $eq$asicworld/verilog/code_verilog_tutorial_parallel_if.v:16$8_Y
  end
  attribute \src "asicworld/verilog/code_verilog_tutorial_parallel_if.v:8.5-8.18"
  cell $eq $eq$asicworld/verilog/code_verilog_tutorial_parallel_if.v:8$2
    parameter \A_SIGNED 0
    parameter \A_WIDTH 1
    parameter \B_SIGNED 0
    parameter \B_WIDTH 1
    parameter \Y_WIDTH 1
    connect \A \reset
    connect \B 1'0
    connect \Y $eq$asicworld/verilog/code_verilog_tutorial_parallel_if.v:8$2_Y
  end
  attribute \src "asicworld/verilog/code_verilog_tutorial_parallel_if.v:12.7-12.38"
  cell $logic_and $logic_and$asicworld/verilog/code_verilog_tutorial_parallel_if.v:12$5
    parameter \A_SIGNED 0
    parameter \A_WIDTH 1
    parameter \B_SIGNED 0
    parameter \B_WIDTH 1
    parameter \Y_WIDTH 1
    connect \A $eq$asicworld/verilog/code_verilog_tutorial_parallel_if.v:12$3_Y
    connect \B $eq$asicworld/verilog/code_verilog_tutorial_parallel_if.v:12$4_Y
    connect \Y $logic_and$asicworld/verilog/code_verilog_tutorial_parallel_if.v:12$5_Y
  end
  attribute \src "asicworld/verilog/code_verilog_tutorial_parallel_if.v:16.7-16.40"
  cell $logic_and $logic_and$asicworld/verilog/code_verilog_tutorial_parallel_if.v:16$9
    parameter \A_SIGNED 0
    parameter \A_WIDTH 1
    parameter \B_SIGNED 0
    parameter \B_WIDTH 1
    parameter \Y_WIDTH 1
    connect \A $eq$asicworld/verilog/code_verilog_tutorial_parallel_if.v:16$7_Y
    connect \B $eq$asicworld/verilog/code_verilog_tutorial_parallel_if.v:16$8_Y
    connect \Y $logic_and$asicworld/verilog/code_verilog_tutorial_parallel_if.v:16$9_Y
  end
  attribute \src "asicworld/verilog/code_verilog_tutorial_parallel_if.v:17.16-17.30"
  cell $sub $sub$asicworld/verilog/code_verilog_tutorial_parallel_if.v:17$10
    parameter \A_SIGNED 0
    parameter \A_WIDTH 4
    parameter \B_SIGNED 0
    parameter \B_WIDTH 1
    parameter \Y_WIDTH 4
    connect \A \counter
    connect \B 1'1
    connect \Y $sub$asicworld/verilog/code_verilog_tutorial_parallel_if.v:17$10_Y
  end
  attribute \src "asicworld/verilog/code_verilog_tutorial_parallel_if.v:6.1-19.4"
  process $proc$asicworld/verilog/code_verilog_tutorial_parallel_if.v:6$1
    assign $0\counter[3:0] \counter
    attribute \src "asicworld/verilog/code_verilog_tutorial_parallel_if.v:8.1-19.4"
    switch $eq$asicworld/verilog/code_verilog_tutorial_parallel_if.v:8$2_Y
      attribute \src "asicworld/verilog/code_verilog_tutorial_parallel_if.v:8.5-8.18"
      case 1'1
        assign $0\counter[3:0] 4'0000
      attribute \src "asicworld/verilog/code_verilog_tutorial_parallel_if.v:10.5-10.9"
      case 
        attribute \src "asicworld/verilog/code_verilog_tutorial_parallel_if.v:12.3-14.6"
        switch $logic_and$asicworld/verilog/code_verilog_tutorial_parallel_if.v:12$5_Y
          attribute \src "asicworld/verilog/code_verilog_tutorial_parallel_if.v:12.7-12.38"
          case 1'1
            assign $0\counter[3:0] $add$asicworld/verilog/code_verilog_tutorial_parallel_if.v:13$6_Y
          case 
        end
        attribute \src "asicworld/verilog/code_verilog_tutorial_parallel_if.v:16.3-18.6"
        switch $logic_and$asicworld/verilog/code_verilog_tutorial_parallel_if.v:16$9_Y
          attribute \src "asicworld/verilog/code_verilog_tutorial_parallel_if.v:16.7-16.40"
          case 1'1
            assign $0\counter[3:0] $sub$asicworld/verilog/code_verilog_tutorial_parallel_if.v:17$10_Y
          case 
        end
    end
    sync posedge \clk
      update \counter $0\counter[3:0]
  end
end
