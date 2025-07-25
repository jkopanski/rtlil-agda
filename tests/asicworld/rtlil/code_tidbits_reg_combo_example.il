autoidx 3
attribute \cells_not_processed 1
attribute \src "asicworld/verilog/code_tidbits_reg_combo_example.v:1.1-13.10"
module \reg_combo_example
  attribute \src "asicworld/verilog/code_tidbits_reg_combo_example.v:8.1-11.4"
  wire $0\y[0:0]
  attribute \src "asicworld/verilog/code_tidbits_reg_combo_example.v:10.7-10.12"
  wire $and$asicworld/verilog/code_tidbits_reg_combo_example.v:10$2_Y
  attribute \src "asicworld/verilog/code_tidbits_reg_combo_example.v:2.7-2.8"
  wire input 1 \a
  attribute \src "asicworld/verilog/code_tidbits_reg_combo_example.v:2.10-2.11"
  wire input 2 \b
  attribute \src "asicworld/verilog/code_tidbits_reg_combo_example.v:3.8-3.9"
  wire output 3 \y
  attribute \src "asicworld/verilog/code_tidbits_reg_combo_example.v:10.7-10.12"
  cell $and $and$asicworld/verilog/code_tidbits_reg_combo_example.v:10$2
    parameter \A_SIGNED 0
    parameter \A_WIDTH 1
    parameter \B_SIGNED 0
    parameter \B_WIDTH 1
    parameter \Y_WIDTH 1
    connect \A \a
    connect \B \b
    connect \Y $and$asicworld/verilog/code_tidbits_reg_combo_example.v:10$2_Y
  end
  attribute \src "asicworld/verilog/code_tidbits_reg_combo_example.v:8.1-11.4"
  process $proc$asicworld/verilog/code_tidbits_reg_combo_example.v:8$1
    assign { } { }
    assign $0\y[0:0] $and$asicworld/verilog/code_tidbits_reg_combo_example.v:10$2_Y
    sync always
      update \y $0\y[0:0]
  end
end
