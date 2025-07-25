autoidx 2
attribute \cells_not_processed 1
attribute \src "asicworld/verilog/code_tidbits_reg_seq_example.v:1.1-15.10"
module \reg_seq_example
  attribute \src "asicworld/verilog/code_tidbits_reg_seq_example.v:8.1-13.4"
  wire $0\q[0:0]
  attribute \src "asicworld/verilog/code_tidbits_reg_seq_example.v:2.7-2.10"
  wire input 1 \clk
  attribute \src "asicworld/verilog/code_tidbits_reg_seq_example.v:2.19-2.20"
  wire input 3 \d
  attribute \src "asicworld/verilog/code_tidbits_reg_seq_example.v:3.8-3.9"
  wire output 4 \q
  attribute \src "asicworld/verilog/code_tidbits_reg_seq_example.v:2.12-2.17"
  wire input 2 \reset
  attribute \src "asicworld/verilog/code_tidbits_reg_seq_example.v:8.1-13.4"
  process $proc$asicworld/verilog/code_tidbits_reg_seq_example.v:8$1
    assign $0\q[0:0] \q
    attribute \src "asicworld/verilog/code_tidbits_reg_seq_example.v:9.1-13.4"
    switch \reset
      attribute \src "asicworld/verilog/code_tidbits_reg_seq_example.v:9.5-9.10"
      case 1'1
        assign $0\q[0:0] 1'0
      attribute \src "asicworld/verilog/code_tidbits_reg_seq_example.v:11.5-11.9"
      case 
        assign $0\q[0:0] \d
    end
    sync posedge \clk
      update \q $0\q[0:0]
    sync posedge \reset
      update \q $0\q[0:0]
  end
end
