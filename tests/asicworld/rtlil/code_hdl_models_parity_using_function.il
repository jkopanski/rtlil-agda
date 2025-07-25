autoidx 14
attribute \cells_not_processed 1
attribute \src "asicworld/verilog/code_hdl_models_parity_using_function.v:7.1-29.10"
module \parity_using_function
  attribute \src "asicworld/verilog/code_hdl_models_parity_using_function.v:0.0-0.0"
  wire $0\parity$func$asicworld/verilog/code_hdl_models_parity_using_function.v:27$1.$result[0:0]$4
  attribute \src "asicworld/verilog/code_hdl_models_parity_using_function.v:0.0-0.0"
  wire $0\parity$func$asicworld/verilog/code_hdl_models_parity_using_function.v:27$2.$result[0:0]$5
  attribute \src "asicworld/verilog/code_hdl_models_parity_using_function.v:0.0-0.0"
  wire width 32 $0\parity$func$asicworld/verilog/code_hdl_models_parity_using_function.v:27$2.data[31:0]$6
  attribute \src "asicworld/verilog/code_hdl_models_parity_using_function.v:19.15-21.40"
  wire $xor$asicworld/verilog/code_hdl_models_parity_using_function.v:19$11_Y
  attribute \src "asicworld/verilog/code_hdl_models_parity_using_function.v:19.15-22.40"
  wire $xor$asicworld/verilog/code_hdl_models_parity_using_function.v:19$13_Y
  attribute \src "asicworld/verilog/code_hdl_models_parity_using_function.v:19.16-19.39"
  wire $xor$asicworld/verilog/code_hdl_models_parity_using_function.v:19$7_Y
  attribute \src "asicworld/verilog/code_hdl_models_parity_using_function.v:19.15-20.40"
  wire $xor$asicworld/verilog/code_hdl_models_parity_using_function.v:19$9_Y
  attribute \src "asicworld/verilog/code_hdl_models_parity_using_function.v:20.16-20.39"
  wire $xor$asicworld/verilog/code_hdl_models_parity_using_function.v:20$8_Y
  attribute \src "asicworld/verilog/code_hdl_models_parity_using_function.v:21.16-21.39"
  wire $xor$asicworld/verilog/code_hdl_models_parity_using_function.v:21$10_Y
  attribute \src "asicworld/verilog/code_hdl_models_parity_using_function.v:22.16-22.39"
  wire $xor$asicworld/verilog/code_hdl_models_parity_using_function.v:22$12_Y
  attribute \src "asicworld/verilog/code_hdl_models_parity_using_function.v:12.13-12.20"
  wire width 8 input 1 \data_in
  attribute \src "asicworld/verilog/code_hdl_models_parity_using_function.v:0.0-0.0"
  wire \parity$func$asicworld/verilog/code_hdl_models_parity_using_function.v:27$1.$result
  attribute \nosync 1
  attribute \src "asicworld/verilog/code_hdl_models_parity_using_function.v:0.0-0.0"
  wire \parity$func$asicworld/verilog/code_hdl_models_parity_using_function.v:27$2.$result
  attribute \nosync 1
  attribute \src "asicworld/verilog/code_hdl_models_parity_using_function.v:17.16-17.20"
  wire width 32 \parity$func$asicworld/verilog/code_hdl_models_parity_using_function.v:27$2.data
  attribute \src "asicworld/verilog/code_hdl_models_parity_using_function.v:11.9-11.19"
  wire output 2 \parity_out
  attribute \src "asicworld/verilog/code_hdl_models_parity_using_function.v:19.15-21.40"
  cell $xor $xor$asicworld/verilog/code_hdl_models_parity_using_function.v:19$11
    parameter \A_SIGNED 0
    parameter \A_WIDTH 1
    parameter \B_SIGNED 0
    parameter \B_WIDTH 1
    parameter \Y_WIDTH 1
    connect \A $xor$asicworld/verilog/code_hdl_models_parity_using_function.v:19$9_Y
    connect \B $xor$asicworld/verilog/code_hdl_models_parity_using_function.v:21$10_Y
    connect \Y $xor$asicworld/verilog/code_hdl_models_parity_using_function.v:19$11_Y
  end
  attribute \src "asicworld/verilog/code_hdl_models_parity_using_function.v:19.15-22.40"
  cell $xor $xor$asicworld/verilog/code_hdl_models_parity_using_function.v:19$13
    parameter \A_SIGNED 0
    parameter \A_WIDTH 1
    parameter \B_SIGNED 0
    parameter \B_WIDTH 1
    parameter \Y_WIDTH 1
    connect \A $xor$asicworld/verilog/code_hdl_models_parity_using_function.v:19$11_Y
    connect \B $xor$asicworld/verilog/code_hdl_models_parity_using_function.v:22$12_Y
    connect \Y $xor$asicworld/verilog/code_hdl_models_parity_using_function.v:19$13_Y
  end
  attribute \src "asicworld/verilog/code_hdl_models_parity_using_function.v:19.16-19.39"
  cell $xor $xor$asicworld/verilog/code_hdl_models_parity_using_function.v:19$7
    parameter \A_SIGNED 0
    parameter \A_WIDTH 1
    parameter \B_SIGNED 0
    parameter \B_WIDTH 1
    parameter \Y_WIDTH 1
    connect \A \data_in [0]
    connect \B \data_in [1]
    connect \Y $xor$asicworld/verilog/code_hdl_models_parity_using_function.v:19$7_Y
  end
  attribute \src "asicworld/verilog/code_hdl_models_parity_using_function.v:19.15-20.40"
  cell $xor $xor$asicworld/verilog/code_hdl_models_parity_using_function.v:19$9
    parameter \A_SIGNED 0
    parameter \A_WIDTH 1
    parameter \B_SIGNED 0
    parameter \B_WIDTH 1
    parameter \Y_WIDTH 1
    connect \A $xor$asicworld/verilog/code_hdl_models_parity_using_function.v:19$7_Y
    connect \B $xor$asicworld/verilog/code_hdl_models_parity_using_function.v:20$8_Y
    connect \Y $xor$asicworld/verilog/code_hdl_models_parity_using_function.v:19$9_Y
  end
  attribute \src "asicworld/verilog/code_hdl_models_parity_using_function.v:20.16-20.39"
  cell $xor $xor$asicworld/verilog/code_hdl_models_parity_using_function.v:20$8
    parameter \A_SIGNED 0
    parameter \A_WIDTH 1
    parameter \B_SIGNED 0
    parameter \B_WIDTH 1
    parameter \Y_WIDTH 1
    connect \A \data_in [2]
    connect \B \data_in [3]
    connect \Y $xor$asicworld/verilog/code_hdl_models_parity_using_function.v:20$8_Y
  end
  attribute \src "asicworld/verilog/code_hdl_models_parity_using_function.v:21.16-21.39"
  cell $xor $xor$asicworld/verilog/code_hdl_models_parity_using_function.v:21$10
    parameter \A_SIGNED 0
    parameter \A_WIDTH 1
    parameter \B_SIGNED 0
    parameter \B_WIDTH 1
    parameter \Y_WIDTH 1
    connect \A \data_in [4]
    connect \B \data_in [5]
    connect \Y $xor$asicworld/verilog/code_hdl_models_parity_using_function.v:21$10_Y
  end
  attribute \src "asicworld/verilog/code_hdl_models_parity_using_function.v:22.16-22.39"
  cell $xor $xor$asicworld/verilog/code_hdl_models_parity_using_function.v:22$12
    parameter \A_SIGNED 0
    parameter \A_WIDTH 1
    parameter \B_SIGNED 0
    parameter \B_WIDTH 1
    parameter \Y_WIDTH 1
    connect \A \data_in [6]
    connect \B \data_in [7]
    connect \Y $xor$asicworld/verilog/code_hdl_models_parity_using_function.v:22$12_Y
  end
  attribute \src "asicworld/verilog/code_hdl_models_parity_using_function.v:0.0-0.0"
  process $proc$asicworld/verilog/code_hdl_models_parity_using_function.v:0$3
    assign { } { }
    assign { } { }
    assign { } { }
    assign $0\parity$func$asicworld/verilog/code_hdl_models_parity_using_function.v:27$2.data[31:0]$6 { 24'000000000000000000000000 \data_in }
    assign $0\parity$func$asicworld/verilog/code_hdl_models_parity_using_function.v:27$2.$result[0:0]$5 $xor$asicworld/verilog/code_hdl_models_parity_using_function.v:19$13_Y
    assign $0\parity$func$asicworld/verilog/code_hdl_models_parity_using_function.v:27$1.$result[0:0]$4 $xor$asicworld/verilog/code_hdl_models_parity_using_function.v:19$13_Y
    sync always
      update \parity$func$asicworld/verilog/code_hdl_models_parity_using_function.v:27$1.$result $0\parity$func$asicworld/verilog/code_hdl_models_parity_using_function.v:27$1.$result[0:0]$4
      update \parity$func$asicworld/verilog/code_hdl_models_parity_using_function.v:27$2.$result 1'x
      update \parity$func$asicworld/verilog/code_hdl_models_parity_using_function.v:27$2.data 32'x
  end
  connect \parity_out \parity$func$asicworld/verilog/code_hdl_models_parity_using_function.v:27$1.$result
end
