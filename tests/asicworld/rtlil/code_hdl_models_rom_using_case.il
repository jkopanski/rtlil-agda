autoidx 2
attribute \cells_not_processed 1
attribute \src "asicworld/verilog/code_hdl_models_rom_using_case.v:7.1-42.10"
module \rom_using_case
  attribute \src "asicworld/verilog/code_hdl_models_rom_using_case.v:20.1-40.4"
  wire width 8 $0\data[7:0]
  attribute \src "asicworld/verilog/code_hdl_models_rom_using_case.v:20.1-40.4"
  wire width 8 $1\data[7:0]
  attribute \src "asicworld/verilog/code_hdl_models_rom_using_case.v:13.13-13.20"
  wire width 4 input 1 \address
  attribute \src "asicworld/verilog/code_hdl_models_rom_using_case.v:16.7-16.9"
  wire input 4 \ce
  attribute \src "asicworld/verilog/code_hdl_models_rom_using_case.v:14.14-14.18"
  wire width 8 output 2 \data
  attribute \src "asicworld/verilog/code_hdl_models_rom_using_case.v:15.7-15.14"
  wire input 3 \read_en
  attribute \src "asicworld/verilog/code_hdl_models_rom_using_case.v:20.1-40.4"
  process $proc$asicworld/verilog/code_hdl_models_rom_using_case.v:20$1
    assign { } { }
    assign $0\data[7:0] $1\data[7:0]
    attribute \src "asicworld/verilog/code_hdl_models_rom_using_case.v:22.3-39.10"
    switch { 28'0000000000000000000000000000 \address }
      attribute \src "asicworld/verilog/code_hdl_models_rom_using_case.v:0.0-0.0"
      case 0
        assign { } { }
        assign $1\data[7:0] 8'00001010
      attribute \src "asicworld/verilog/code_hdl_models_rom_using_case.v:0.0-0.0"
      case 1
        assign { } { }
        assign $1\data[7:0] 8'00110111
      attribute \src "asicworld/verilog/code_hdl_models_rom_using_case.v:0.0-0.0"
      case 2
        assign { } { }
        assign $1\data[7:0] 8'11110100
      attribute \src "asicworld/verilog/code_hdl_models_rom_using_case.v:0.0-0.0"
      case 3
        assign { } { }
        assign $1\data[7:0] 8'00000000
      attribute \src "asicworld/verilog/code_hdl_models_rom_using_case.v:0.0-0.0"
      case 4
        assign { } { }
        assign $1\data[7:0] 8'00000001
      attribute \src "asicworld/verilog/code_hdl_models_rom_using_case.v:0.0-0.0"
      case 5
        assign { } { }
        assign $1\data[7:0] 8'11111111
      attribute \src "asicworld/verilog/code_hdl_models_rom_using_case.v:0.0-0.0"
      case 6
        assign { } { }
        assign $1\data[7:0] 8'00010001
      attribute \src "asicworld/verilog/code_hdl_models_rom_using_case.v:0.0-0.0"
      case 7
        assign { } { }
        assign $1\data[7:0] 8'00000001
      attribute \src "asicworld/verilog/code_hdl_models_rom_using_case.v:0.0-0.0"
      case 8
        assign { } { }
        assign $1\data[7:0] 8'00010000
      attribute \src "asicworld/verilog/code_hdl_models_rom_using_case.v:0.0-0.0"
      case 9
        assign { } { }
        assign $1\data[7:0] 8'00000000
      attribute \src "asicworld/verilog/code_hdl_models_rom_using_case.v:0.0-0.0"
      case 10
        assign { } { }
        assign $1\data[7:0] 8'00010000
      attribute \src "asicworld/verilog/code_hdl_models_rom_using_case.v:0.0-0.0"
      case 11
        assign { } { }
        assign $1\data[7:0] 8'00010101
      attribute \src "asicworld/verilog/code_hdl_models_rom_using_case.v:0.0-0.0"
      case 12
        assign { } { }
        assign $1\data[7:0] 8'01100000
      attribute \src "asicworld/verilog/code_hdl_models_rom_using_case.v:0.0-0.0"
      case 13
        assign { } { }
        assign $1\data[7:0] 8'10010000
      attribute \src "asicworld/verilog/code_hdl_models_rom_using_case.v:0.0-0.0"
      case 14
        assign { } { }
        assign $1\data[7:0] 8'01110000
      attribute \src "asicworld/verilog/code_hdl_models_rom_using_case.v:0.0-0.0"
      case 15
        assign { } { }
        assign $1\data[7:0] 8'10010000
      case 
        assign $1\data[7:0] \data
    end
    sync always
      update \data $0\data[7:0]
  end
end
