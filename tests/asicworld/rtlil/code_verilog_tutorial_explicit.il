autoidx 5
attribute \cells_not_processed 1
attribute \src "asicworld/verilog/code_verilog_tutorial_explicit.v:19.1-35.10"
module \dff
  attribute \src "asicworld/verilog/code_verilog_tutorial_explicit.v:26.1-33.4"
  wire $0\q[0:0]
  attribute \src "asicworld/verilog/code_verilog_tutorial_explicit.v:27.5-27.16"
  wire $eq$asicworld/verilog/code_verilog_tutorial_explicit.v:27$3_Y
  attribute \src "asicworld/verilog/code_verilog_tutorial_explicit.v:29.14-29.25"
  wire $eq$asicworld/verilog/code_verilog_tutorial_explicit.v:29$4_Y
  attribute \src "asicworld/verilog/code_verilog_tutorial_explicit.v:24.16-24.18"
  wire $not$asicworld/verilog/code_verilog_tutorial_explicit.v:24$1_Y
  attribute \src "asicworld/verilog/code_verilog_tutorial_explicit.v:20.7-20.10"
  wire input 3 \clk
  attribute \src "asicworld/verilog/code_verilog_tutorial_explicit.v:20.12-20.13"
  wire input 4 \d
  attribute \src "asicworld/verilog/code_verilog_tutorial_explicit.v:20.20-20.23"
  wire input 6 \pre
  attribute \src "asicworld/verilog/code_verilog_tutorial_explicit.v:21.8-21.9"
  wire output 1 \q
  attribute \src "asicworld/verilog/code_verilog_tutorial_explicit.v:21.11-21.16"
  wire output 2 \q_bar
  attribute \src "asicworld/verilog/code_verilog_tutorial_explicit.v:20.15-20.18"
  wire input 5 \rst
  attribute \src "asicworld/verilog/code_verilog_tutorial_explicit.v:27.5-27.16"
  cell $eq $eq$asicworld/verilog/code_verilog_tutorial_explicit.v:27$3
    parameter \A_SIGNED 0
    parameter \A_WIDTH 1
    parameter \B_SIGNED 0
    parameter \B_WIDTH 1
    parameter \Y_WIDTH 1
    connect \A \rst
    connect \B 1'1
    connect \Y $eq$asicworld/verilog/code_verilog_tutorial_explicit.v:27$3_Y
  end
  attribute \src "asicworld/verilog/code_verilog_tutorial_explicit.v:29.14-29.25"
  cell $eq $eq$asicworld/verilog/code_verilog_tutorial_explicit.v:29$4
    parameter \A_SIGNED 0
    parameter \A_WIDTH 1
    parameter \B_SIGNED 0
    parameter \B_WIDTH 1
    parameter \Y_WIDTH 1
    connect \A \pre
    connect \B 1'1
    connect \Y $eq$asicworld/verilog/code_verilog_tutorial_explicit.v:29$4_Y
  end
  attribute \src "asicworld/verilog/code_verilog_tutorial_explicit.v:24.16-24.18"
  cell $not $not$asicworld/verilog/code_verilog_tutorial_explicit.v:24$1
    parameter \A_SIGNED 0
    parameter \A_WIDTH 1
    parameter \Y_WIDTH 1
    connect \A \q
    connect \Y $not$asicworld/verilog/code_verilog_tutorial_explicit.v:24$1_Y
  end
  attribute \src "asicworld/verilog/code_verilog_tutorial_explicit.v:26.1-33.4"
  process $proc$asicworld/verilog/code_verilog_tutorial_explicit.v:26$2
    assign $0\q[0:0] \q
    attribute \src "asicworld/verilog/code_verilog_tutorial_explicit.v:27.1-33.4"
    switch $eq$asicworld/verilog/code_verilog_tutorial_explicit.v:27$3_Y
      attribute \src "asicworld/verilog/code_verilog_tutorial_explicit.v:27.5-27.16"
      case 1'1
        assign $0\q[0:0] 1'0
      attribute \src "asicworld/verilog/code_verilog_tutorial_explicit.v:29.5-29.9"
      case 
        attribute \src "asicworld/verilog/code_verilog_tutorial_explicit.v:29.10-33.4"
        switch $eq$asicworld/verilog/code_verilog_tutorial_explicit.v:29$4_Y
          attribute \src "asicworld/verilog/code_verilog_tutorial_explicit.v:29.14-29.25"
          case 1'1
            assign $0\q[0:0] 1'1
          attribute \src "asicworld/verilog/code_verilog_tutorial_explicit.v:31.5-31.9"
          case 
            assign $0\q[0:0] \d
        end
    end
    sync posedge \clk
      update \q $0\q[0:0]
  end
  connect \q_bar $not$asicworld/verilog/code_verilog_tutorial_explicit.v:24$1_Y
end
attribute \cells_not_processed 1
attribute \src "asicworld/verilog/code_verilog_tutorial_explicit.v:1.1-16.10"
module \explicit
  attribute \src "asicworld/verilog/code_verilog_tutorial_explicit.v:2.5-2.8"
  wire \clk
  attribute \src "asicworld/verilog/code_verilog_tutorial_explicit.v:2.9-2.10"
  wire \d
  attribute \src "asicworld/verilog/code_verilog_tutorial_explicit.v:2.15-2.18"
  wire \pre
  attribute \src "asicworld/verilog/code_verilog_tutorial_explicit.v:3.6-3.7"
  wire \q
  attribute \src "asicworld/verilog/code_verilog_tutorial_explicit.v:2.11-2.14"
  wire \rst
  attribute \module_not_derived 1
  attribute \src "asicworld/verilog/code_verilog_tutorial_explicit.v:7.5-14.2"
  cell \dff \u0
    connect \clk \clk
    connect \d \d
    connect \pre \pre
    connect \q \q
    connect \q_bar { }
    connect \rst \rst
  end
end
