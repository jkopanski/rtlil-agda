autoidx 2
attribute \cells_not_processed 1
attribute \src "asicworld/verilog/code_hdl_models_parity_using_bitwise.v:7.1-16.10"
module \parity_using_bitwise
  attribute \src "asicworld/verilog/code_hdl_models_parity_using_bitwise.v:14.21-14.29"
  wire $reduce_xor$asicworld/verilog/code_hdl_models_parity_using_bitwise.v:14$1_Y
  attribute \src "asicworld/verilog/code_hdl_models_parity_using_bitwise.v:12.13-12.20"
  wire width 8 input 1 \data_in
  attribute \src "asicworld/verilog/code_hdl_models_parity_using_bitwise.v:11.9-11.19"
  wire output 2 \parity_out
  attribute \src "asicworld/verilog/code_hdl_models_parity_using_bitwise.v:14.21-14.29"
  cell $reduce_xor $reduce_xor$asicworld/verilog/code_hdl_models_parity_using_bitwise.v:14$1
    parameter \A_SIGNED 0
    parameter \A_WIDTH 8
    parameter \Y_WIDTH 1
    connect \A \data_in
    connect \Y $reduce_xor$asicworld/verilog/code_hdl_models_parity_using_bitwise.v:14$1_Y
  end
  connect \parity_out $reduce_xor$asicworld/verilog/code_hdl_models_parity_using_bitwise.v:14$1_Y
end
