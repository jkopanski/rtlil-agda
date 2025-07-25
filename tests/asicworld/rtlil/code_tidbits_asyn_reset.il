autoidx 3
attribute \cells_not_processed 1
attribute \src "asicworld/verilog/code_tidbits_asyn_reset.v:1.1-18.10"
module \asyn_reset
  attribute \src "asicworld/verilog/code_tidbits_asyn_reset.v:12.1-17.5"
  wire $0\c[0:0]
  attribute \src "asicworld/verilog/code_tidbits_asyn_reset.v:13.7-13.20"
  wire $eq$asicworld/verilog/code_tidbits_asyn_reset.v:13$2_Y
  attribute \src "asicworld/verilog/code_tidbits_asyn_reset.v:4.12-4.13"
  wire input 3 \a
  attribute \src "asicworld/verilog/code_tidbits_asyn_reset.v:5.13-5.14"
  wire output 4 \c
  attribute \src "asicworld/verilog/code_tidbits_asyn_reset.v:2.12-2.15"
  wire input 1 \clk
  attribute \src "asicworld/verilog/code_tidbits_asyn_reset.v:3.12-3.17"
  wire input 2 \reset
  attribute \src "asicworld/verilog/code_tidbits_asyn_reset.v:13.7-13.20"
  cell $eq $eq$asicworld/verilog/code_tidbits_asyn_reset.v:13$2
    parameter \A_SIGNED 0
    parameter \A_WIDTH 1
    parameter \B_SIGNED 0
    parameter \B_WIDTH 1
    parameter \Y_WIDTH 1
    connect \A \reset
    connect \B 1'1
    connect \Y $eq$asicworld/verilog/code_tidbits_asyn_reset.v:13$2_Y
  end
  attribute \src "asicworld/verilog/code_tidbits_asyn_reset.v:12.1-17.5"
  process $proc$asicworld/verilog/code_tidbits_asyn_reset.v:12$1
    assign $0\c[0:0] \c
    attribute \src "asicworld/verilog/code_tidbits_asyn_reset.v:13.2-17.5"
    switch $eq$asicworld/verilog/code_tidbits_asyn_reset.v:13$2_Y
      attribute \src "asicworld/verilog/code_tidbits_asyn_reset.v:13.7-13.20"
      case 1'1
        assign $0\c[0:0] 1'0
      attribute \src "asicworld/verilog/code_tidbits_asyn_reset.v:15.6-15.10"
      case 
        assign $0\c[0:0] \a
    end
    sync posedge \clk
      update \c $0\c[0:0]
    sync posedge \reset
      update \c $0\c[0:0]
  end
end
