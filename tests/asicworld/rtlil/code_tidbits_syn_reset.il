autoidx 3
attribute \cells_not_processed 1
attribute \src "asicworld/verilog/code_tidbits_syn_reset.v:1.1-19.10"
module \syn_reset
  attribute \src "asicworld/verilog/code_tidbits_syn_reset.v:12.1-17.6"
  wire $0\c[0:0]
  attribute \src "asicworld/verilog/code_tidbits_syn_reset.v:13.8-13.21"
  wire $eq$asicworld/verilog/code_tidbits_syn_reset.v:13$2_Y
  attribute \src "asicworld/verilog/code_tidbits_syn_reset.v:4.10-4.11"
  wire input 3 \a
  attribute \src "asicworld/verilog/code_tidbits_syn_reset.v:5.11-5.12"
  wire output 4 \c
  attribute \src "asicworld/verilog/code_tidbits_syn_reset.v:2.10-2.13"
  wire input 1 \clk
  attribute \src "asicworld/verilog/code_tidbits_syn_reset.v:3.10-3.15"
  wire input 2 \reset
  attribute \src "asicworld/verilog/code_tidbits_syn_reset.v:13.8-13.21"
  cell $eq $eq$asicworld/verilog/code_tidbits_syn_reset.v:13$2
    parameter \A_SIGNED 0
    parameter \A_WIDTH 1
    parameter \B_SIGNED 0
    parameter \B_WIDTH 1
    parameter \Y_WIDTH 1
    connect \A \reset
    connect \B 1'1
    connect \Y $eq$asicworld/verilog/code_tidbits_syn_reset.v:13$2_Y
  end
  attribute \src "asicworld/verilog/code_tidbits_syn_reset.v:12.1-17.6"
  process $proc$asicworld/verilog/code_tidbits_syn_reset.v:12$1
    assign $0\c[0:0] \c
    attribute \src "asicworld/verilog/code_tidbits_syn_reset.v:13.3-17.6"
    switch $eq$asicworld/verilog/code_tidbits_syn_reset.v:13$2_Y
      attribute \src "asicworld/verilog/code_tidbits_syn_reset.v:13.8-13.21"
      case 1'1
        assign $0\c[0:0] 1'0
      attribute \src "asicworld/verilog/code_tidbits_syn_reset.v:15.7-15.11"
      case 
        assign $0\c[0:0] \a
    end
    sync posedge \clk
      update \c $0\c[0:0]
  end
end
