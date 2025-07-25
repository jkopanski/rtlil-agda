autoidx 4
attribute \cells_not_processed 1
attribute \src "asicworld/verilog/code_verilog_tutorial_v2k_reg.v:1.1-24.10"
module \v2k_reg
  attribute \src "asicworld/verilog/code_verilog_tutorial_v2k_reg.v:4.5-4.10"
  wire $0\a[0:0]
  attribute \src "asicworld/verilog/code_verilog_tutorial_v2k_reg.v:7.11-7.16"
  wire $0\d[0:0]
  attribute \src "asicworld/verilog/code_verilog_tutorial_v2k_reg.v:10.18-10.31"
  wire width 8 $0\data[7:0]
  attribute \src "asicworld/verilog/code_verilog_tutorial_v2k_reg.v:4.5-4.6"
  wire \a
  attribute \src "asicworld/verilog/code_verilog_tutorial_v2k_reg.v:7.5-7.6"
  wire \b
  attribute \src "asicworld/verilog/code_verilog_tutorial_v2k_reg.v:7.8-7.9"
  wire \c
  attribute \src "asicworld/verilog/code_verilog_tutorial_v2k_reg.v:7.11-7.12"
  wire \d
  attribute \src "asicworld/verilog/code_verilog_tutorial_v2k_reg.v:10.18-10.22"
  wire width 8 signed \data
  attribute \src "asicworld/verilog/code_verilog_tutorial_v2k_reg.v:10.18-10.31"
  process $proc$asicworld/verilog/code_verilog_tutorial_v2k_reg.v:10$3
    assign { } { }
    assign $0\data[7:0] 8'11110000
    sync always
      update \data $0\data[7:0]
  end
  attribute \src "asicworld/verilog/code_verilog_tutorial_v2k_reg.v:4.5-4.10"
  process $proc$asicworld/verilog/code_verilog_tutorial_v2k_reg.v:4$1
    assign { } { }
    assign $0\a[0:0] 1'0
    sync always
      update \a $0\a[0:0]
  end
  attribute \src "asicworld/verilog/code_verilog_tutorial_v2k_reg.v:7.11-7.16"
  process $proc$asicworld/verilog/code_verilog_tutorial_v2k_reg.v:7$2
    assign { } { }
    assign $0\d[0:0] 1'0
    sync always
      update \d $0\d[0:0]
  end
end
