autoidx 2
attribute \cells_not_processed 1
attribute \src "asicworld/verilog/code_verilog_tutorial_decoder_always.v:1.1-20.10"
module \decoder_always
  attribute \src "asicworld/verilog/code_verilog_tutorial_decoder_always.v:6.1-18.4"
  wire width 8 $0\out[7:0]
  attribute \src "asicworld/verilog/code_verilog_tutorial_decoder_always.v:6.1-18.4"
  wire width 8 $1\out[7:0]
  attribute \src "asicworld/verilog/code_verilog_tutorial_decoder_always.v:2.13-2.15"
  wire width 3 input 1 \in
  attribute \src "asicworld/verilog/code_verilog_tutorial_decoder_always.v:3.14-3.17"
  wire width 8 output 2 \out
  attribute \src "asicworld/verilog/code_verilog_tutorial_decoder_always.v:6.1-18.4"
  process $proc$asicworld/verilog/code_verilog_tutorial_decoder_always.v:6$1
    assign { } { }
    assign { } { }
    assign $0\out[7:0] $1\out[7:0]
    attribute \src "asicworld/verilog/code_verilog_tutorial_decoder_always.v:9.3-17.10"
    switch \in
      attribute \src "asicworld/verilog/code_verilog_tutorial_decoder_always.v:0.0-0.0"
      case 3'001
        assign { } { }
        assign $1\out[7:0] 8'00000001
      attribute \src "asicworld/verilog/code_verilog_tutorial_decoder_always.v:0.0-0.0"
      case 3'010
        assign { } { }
        assign $1\out[7:0] 8'00000010
      attribute \src "asicworld/verilog/code_verilog_tutorial_decoder_always.v:0.0-0.0"
      case 3'011
        assign { } { }
        assign $1\out[7:0] 8'00000100
      attribute \src "asicworld/verilog/code_verilog_tutorial_decoder_always.v:0.0-0.0"
      case 3'100
        assign { } { }
        assign $1\out[7:0] 8'00001000
      attribute \src "asicworld/verilog/code_verilog_tutorial_decoder_always.v:0.0-0.0"
      case 3'101
        assign { } { }
        assign $1\out[7:0] 8'00010000
      attribute \src "asicworld/verilog/code_verilog_tutorial_decoder_always.v:0.0-0.0"
      case 3'110
        assign { } { }
        assign $1\out[7:0] 8'01000000
      attribute \src "asicworld/verilog/code_verilog_tutorial_decoder_always.v:0.0-0.0"
      case 3'111
        assign { } { }
        assign $1\out[7:0] 8'10000000
      case 
        assign $1\out[7:0] 8'00000000
    end
    sync always
      update \out $0\out[7:0]
  end
end
