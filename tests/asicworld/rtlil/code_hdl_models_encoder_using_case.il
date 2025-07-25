autoidx 2
attribute \cells_not_processed 1
attribute \src "asicworld/verilog/code_hdl_models_encoder_using_case.v:7.1-42.10"
module \encoder_using_case
  attribute \src "asicworld/verilog/code_hdl_models_encoder_using_case.v:18.1-40.4"
  wire width 4 $0\binary_out[3:0]
  attribute \src "asicworld/verilog/code_hdl_models_encoder_using_case.v:18.1-40.4"
  wire width 4 $1\binary_out[3:0]
  attribute \src "asicworld/verilog/code_hdl_models_encoder_using_case.v:18.1-40.4"
  wire width 4 $2\binary_out[3:0]
  attribute \src "asicworld/verilog/code_hdl_models_encoder_using_case.v:12.14-12.24"
  wire width 4 output 1 \binary_out
  attribute \src "asicworld/verilog/code_hdl_models_encoder_using_case.v:13.8-13.14"
  wire input 3 \enable
  attribute \src "asicworld/verilog/code_hdl_models_encoder_using_case.v:14.14-14.24"
  wire width 16 input 2 \encoder_in
  attribute \src "asicworld/verilog/code_hdl_models_encoder_using_case.v:18.1-40.4"
  process $proc$asicworld/verilog/code_hdl_models_encoder_using_case.v:18$1
    assign { } { }
    assign { } { }
    assign $0\binary_out[3:0] $1\binary_out[3:0]
    attribute \src "asicworld/verilog/code_hdl_models_encoder_using_case.v:21.3-39.6"
    switch \enable
      attribute \src "asicworld/verilog/code_hdl_models_encoder_using_case.v:21.7-21.13"
      case 1'1
        assign { } { }
        assign $1\binary_out[3:0] $2\binary_out[3:0]
        attribute \src "asicworld/verilog/code_hdl_models_encoder_using_case.v:22.5-38.11"
        switch \encoder_in
          attribute \src "asicworld/verilog/code_hdl_models_encoder_using_case.v:0.0-0.0"
          case 16'0000000000000010
            assign { } { }
            assign $2\binary_out[3:0] 4'0001
          attribute \src "asicworld/verilog/code_hdl_models_encoder_using_case.v:0.0-0.0"
          case 16'0000000000000100
            assign { } { }
            assign $2\binary_out[3:0] 4'0010
          attribute \src "asicworld/verilog/code_hdl_models_encoder_using_case.v:0.0-0.0"
          case 16'0000000000001000
            assign { } { }
            assign $2\binary_out[3:0] 4'0011
          attribute \src "asicworld/verilog/code_hdl_models_encoder_using_case.v:0.0-0.0"
          case 16'0000000000010000
            assign { } { }
            assign $2\binary_out[3:0] 4'0100
          attribute \src "asicworld/verilog/code_hdl_models_encoder_using_case.v:0.0-0.0"
          case 16'0000000000100000
            assign { } { }
            assign $2\binary_out[3:0] 4'0101
          attribute \src "asicworld/verilog/code_hdl_models_encoder_using_case.v:0.0-0.0"
          case 16'0000000001000000
            assign { } { }
            assign $2\binary_out[3:0] 4'0110
          attribute \src "asicworld/verilog/code_hdl_models_encoder_using_case.v:0.0-0.0"
          case 16'0000000010000000
            assign { } { }
            assign $2\binary_out[3:0] 4'0111
          attribute \src "asicworld/verilog/code_hdl_models_encoder_using_case.v:0.0-0.0"
          case 16'0000000100000000
            assign { } { }
            assign $2\binary_out[3:0] 4'1000
          attribute \src "asicworld/verilog/code_hdl_models_encoder_using_case.v:0.0-0.0"
          case 16'0000001000000000
            assign { } { }
            assign $2\binary_out[3:0] 4'1001
          attribute \src "asicworld/verilog/code_hdl_models_encoder_using_case.v:0.0-0.0"
          case 16'0000010000000000
            assign { } { }
            assign $2\binary_out[3:0] 4'1010
          attribute \src "asicworld/verilog/code_hdl_models_encoder_using_case.v:0.0-0.0"
          case 16'0000100000000000
            assign { } { }
            assign $2\binary_out[3:0] 4'1011
          attribute \src "asicworld/verilog/code_hdl_models_encoder_using_case.v:0.0-0.0"
          case 16'0001000000000000
            assign { } { }
            assign $2\binary_out[3:0] 4'1100
          attribute \src "asicworld/verilog/code_hdl_models_encoder_using_case.v:0.0-0.0"
          case 16'0010000000000000
            assign { } { }
            assign $2\binary_out[3:0] 4'1101
          attribute \src "asicworld/verilog/code_hdl_models_encoder_using_case.v:0.0-0.0"
          case 16'0100000000000000
            assign { } { }
            assign $2\binary_out[3:0] 4'1110
          attribute \src "asicworld/verilog/code_hdl_models_encoder_using_case.v:0.0-0.0"
          case 16'1000000000000000
            assign { } { }
            assign $2\binary_out[3:0] 4'1111
          case 
            assign $2\binary_out[3:0] 4'0000
        end
      case 
        assign $1\binary_out[3:0] 4'0000
    end
    sync always
      update \binary_out $0\binary_out[3:0]
  end
end
