autoidx 3
attribute \cells_not_processed 1
attribute \src "asicworld/verilog/code_verilog_tutorial_addbit.v:1.1-24.10"
module \addbit
  attribute \src "asicworld/verilog/code_verilog_tutorial_addbit.v:22.19-22.24"
  wire width 2 $add$asicworld/verilog/code_verilog_tutorial_addbit.v:22$1_Y
  attribute \src "asicworld/verilog/code_verilog_tutorial_addbit.v:22.19-22.29"
  wire width 2 $add$asicworld/verilog/code_verilog_tutorial_addbit.v:22$2_Y
  attribute \src "asicworld/verilog/code_verilog_tutorial_addbit.v:9.7-9.8"
  wire input 1 \a
  attribute \src "asicworld/verilog/code_verilog_tutorial_addbit.v:10.7-10.8"
  wire input 2 \b
  attribute \src "asicworld/verilog/code_verilog_tutorial_addbit.v:11.7-11.9"
  wire input 3 \ci
  attribute \src "asicworld/verilog/code_verilog_tutorial_addbit.v:14.8-14.10"
  wire output 5 \co
  attribute \src "asicworld/verilog/code_verilog_tutorial_addbit.v:13.8-13.11"
  wire output 4 \sum
  attribute \src "asicworld/verilog/code_verilog_tutorial_addbit.v:22.19-22.24"
  cell $add $add$asicworld/verilog/code_verilog_tutorial_addbit.v:22$1
    parameter \A_SIGNED 0
    parameter \A_WIDTH 1
    parameter \B_SIGNED 0
    parameter \B_WIDTH 1
    parameter \Y_WIDTH 2
    connect \A \a
    connect \B \b
    connect \Y $add$asicworld/verilog/code_verilog_tutorial_addbit.v:22$1_Y
  end
  attribute \src "asicworld/verilog/code_verilog_tutorial_addbit.v:22.19-22.29"
  cell $add $add$asicworld/verilog/code_verilog_tutorial_addbit.v:22$2
    parameter \A_SIGNED 0
    parameter \A_WIDTH 2
    parameter \B_SIGNED 0
    parameter \B_WIDTH 1
    parameter \Y_WIDTH 2
    connect \A $add$asicworld/verilog/code_verilog_tutorial_addbit.v:22$1_Y
    connect \B \ci
    connect \Y $add$asicworld/verilog/code_verilog_tutorial_addbit.v:22$2_Y
  end
  connect { \co \sum } $add$asicworld/verilog/code_verilog_tutorial_addbit.v:22$2_Y
end
