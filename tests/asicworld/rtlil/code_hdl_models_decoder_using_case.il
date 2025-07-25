autoidx 2
attribute \cells_not_processed 1
attribute \src "asicworld/verilog/code_hdl_models_decoder_using_case.v:7.1-43.10"
module \decoder_using_case
  attribute \src "asicworld/verilog/code_hdl_models_decoder_using_case.v:18.1-41.4"
  wire width 16 $0\decoder_out[15:0]
  attribute \src "asicworld/verilog/code_hdl_models_decoder_using_case.v:18.1-41.4"
  wire width 16 $1\decoder_out[15:0]
  attribute \src "asicworld/verilog/code_hdl_models_decoder_using_case.v:18.1-41.4"
  wire width 16 $2\decoder_out[15:0]
  attribute \src "asicworld/verilog/code_hdl_models_decoder_using_case.v:12.13-12.22"
  wire width 4 input 1 \binary_in
  attribute \src "asicworld/verilog/code_hdl_models_decoder_using_case.v:14.15-14.26"
  wire width 16 output 2 \decoder_out
  attribute \src "asicworld/verilog/code_hdl_models_decoder_using_case.v:13.8-13.14"
  wire input 3 \enable
  attribute \src "asicworld/verilog/code_hdl_models_decoder_using_case.v:18.1-41.4"
  process $proc$asicworld/verilog/code_hdl_models_decoder_using_case.v:18$1
    assign { } { }
    assign { } { }
    assign $0\decoder_out[15:0] $1\decoder_out[15:0]
    attribute \src "asicworld/verilog/code_hdl_models_decoder_using_case.v:21.3-40.6"
    switch \enable
      attribute \src "asicworld/verilog/code_hdl_models_decoder_using_case.v:21.7-21.13"
      case 1'1
        assign { } { }
        assign $1\decoder_out[15:0] $2\decoder_out[15:0]
        attribute \src "asicworld/verilog/code_hdl_models_decoder_using_case.v:22.5-39.12"
        switch \binary_in
          attribute \src "asicworld/verilog/code_hdl_models_decoder_using_case.v:0.0-0.0"
          case 4'0000
            assign { } { }
            assign $2\decoder_out[15:0] 16'0000000000000001
          attribute \src "asicworld/verilog/code_hdl_models_decoder_using_case.v:0.0-0.0"
          case 4'0001
            assign { } { }
            assign $2\decoder_out[15:0] 16'0000000000000010
          attribute \src "asicworld/verilog/code_hdl_models_decoder_using_case.v:0.0-0.0"
          case 4'0010
            assign { } { }
            assign $2\decoder_out[15:0] 16'0000000000000100
          attribute \src "asicworld/verilog/code_hdl_models_decoder_using_case.v:0.0-0.0"
          case 4'0011
            assign { } { }
            assign $2\decoder_out[15:0] 16'0000000000001000
          attribute \src "asicworld/verilog/code_hdl_models_decoder_using_case.v:0.0-0.0"
          case 4'0100
            assign { } { }
            assign $2\decoder_out[15:0] 16'0000000000010000
          attribute \src "asicworld/verilog/code_hdl_models_decoder_using_case.v:0.0-0.0"
          case 4'0101
            assign { } { }
            assign $2\decoder_out[15:0] 16'0000000000100000
          attribute \src "asicworld/verilog/code_hdl_models_decoder_using_case.v:0.0-0.0"
          case 4'0110
            assign { } { }
            assign $2\decoder_out[15:0] 16'0000000001000000
          attribute \src "asicworld/verilog/code_hdl_models_decoder_using_case.v:0.0-0.0"
          case 4'0111
            assign { } { }
            assign $2\decoder_out[15:0] 16'0000000010000000
          attribute \src "asicworld/verilog/code_hdl_models_decoder_using_case.v:0.0-0.0"
          case 4'1000
            assign { } { }
            assign $2\decoder_out[15:0] 16'0000000100000000
          attribute \src "asicworld/verilog/code_hdl_models_decoder_using_case.v:0.0-0.0"
          case 4'1001
            assign { } { }
            assign $2\decoder_out[15:0] 16'0000001000000000
          attribute \src "asicworld/verilog/code_hdl_models_decoder_using_case.v:0.0-0.0"
          case 4'1010
            assign { } { }
            assign $2\decoder_out[15:0] 16'0000010000000000
          attribute \src "asicworld/verilog/code_hdl_models_decoder_using_case.v:0.0-0.0"
          case 4'1011
            assign { } { }
            assign $2\decoder_out[15:0] 16'0000100000000000
          attribute \src "asicworld/verilog/code_hdl_models_decoder_using_case.v:0.0-0.0"
          case 4'1100
            assign { } { }
            assign $2\decoder_out[15:0] 16'0001000000000000
          attribute \src "asicworld/verilog/code_hdl_models_decoder_using_case.v:0.0-0.0"
          case 4'1101
            assign { } { }
            assign $2\decoder_out[15:0] 16'0010000000000000
          attribute \src "asicworld/verilog/code_hdl_models_decoder_using_case.v:0.0-0.0"
          case 4'1110
            assign { } { }
            assign $2\decoder_out[15:0] 16'0100000000000000
          attribute \src "asicworld/verilog/code_hdl_models_decoder_using_case.v:0.0-0.0"
          case 4'1111
            assign { } { }
            assign $2\decoder_out[15:0] 16'1000000000000000
          case 
            assign $2\decoder_out[15:0] 16'0000000000000000
        end
      case 
        assign $1\decoder_out[15:0] 16'0000000000000000
    end
    sync always
      update \decoder_out $0\decoder_out[15:0]
  end
end
