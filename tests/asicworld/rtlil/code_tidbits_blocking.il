autoidx 2
attribute \cells_not_processed 1
attribute \src "asicworld/verilog/code_tidbits_blocking.v:1.1-17.10"
module \blocking
  attribute \src "asicworld/verilog/code_tidbits_blocking.v:11.1-15.4"
  wire $0\b[0:0]
  attribute \src "asicworld/verilog/code_tidbits_blocking.v:11.1-15.4"
  wire $0\c[0:0]
  attribute \src "asicworld/verilog/code_tidbits_blocking.v:3.7-3.8"
  wire input 2 \a
  attribute \src "asicworld/verilog/code_tidbits_blocking.v:9.5-9.6"
  wire \b
  attribute \src "asicworld/verilog/code_tidbits_blocking.v:4.8-4.9"
  wire output 3 \c
  attribute \src "asicworld/verilog/code_tidbits_blocking.v:2.7-2.10"
  wire input 1 \clk
  attribute \src "asicworld/verilog/code_tidbits_blocking.v:11.1-15.4"
  process $proc$asicworld/verilog/code_tidbits_blocking.v:11$1
    assign { } { }
    assign { } { }
    assign $0\b[0:0] \a
    assign $0\c[0:0] \a
    sync posedge \clk
      update \c $0\c[0:0]
      update \b $0\b[0:0]
  end
end
