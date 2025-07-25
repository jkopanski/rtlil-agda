autoidx 5
attribute \cells_not_processed 1
attribute \src "asicworld/verilog/code_hdl_models_mux_2to1_gates.v:7.1-18.10"
module \mux_2to1_gates
  attribute \src "asicworld/verilog/code_hdl_models_mux_2to1_gates.v:14.5-14.28"
  wire $and$asicworld/verilog/code_hdl_models_mux_2to1_gates.v:14$1_Y
  attribute \src "asicworld/verilog/code_hdl_models_mux_2to1_gates.v:15.5-15.24"
  wire $and$asicworld/verilog/code_hdl_models_mux_2to1_gates.v:15$2_Y
  attribute \src "asicworld/verilog/code_hdl_models_mux_2to1_gates.v:0.0-0.0"
  wire $not$asicworld/verilog/code_hdl_models_mux_2to1_gates.v:0$4_Y
  attribute \src "asicworld/verilog/code_hdl_models_mux_2to1_gates.v:16.4-16.22"
  wire $or$asicworld/verilog/code_hdl_models_mux_2to1_gates.v:16$3_Y
  attribute \src "asicworld/verilog/code_hdl_models_mux_2to1_gates.v:8.7-8.8"
  wire input 1 \a
  attribute \src "asicworld/verilog/code_hdl_models_mux_2to1_gates.v:11.10-11.15"
  wire \a_sel
  attribute \src "asicworld/verilog/code_hdl_models_mux_2to1_gates.v:14.13-14.17"
  wire \asel
  attribute \src "asicworld/verilog/code_hdl_models_mux_2to1_gates.v:8.9-8.10"
  wire input 2 \b
  attribute \src "asicworld/verilog/code_hdl_models_mux_2to1_gates.v:11.16-11.21"
  wire \b_sel
  attribute \src "asicworld/verilog/code_hdl_models_mux_2to1_gates.v:15.13-15.17"
  wire \bsel
  attribute \src "asicworld/verilog/code_hdl_models_mux_2to1_gates.v:14.20-14.27"
  wire \inv_sel
  attribute \src "asicworld/verilog/code_hdl_models_mux_2to1_gates.v:8.11-8.14"
  wire input 3 \sel
  attribute \src "asicworld/verilog/code_hdl_models_mux_2to1_gates.v:9.8-9.9"
  wire output 4 \y
  attribute \src "asicworld/verilog/code_hdl_models_mux_2to1_gates.v:14.5-14.28"
  cell $and $and$asicworld/verilog/code_hdl_models_mux_2to1_gates.v:14$1
    parameter \A_SIGNED 0
    parameter \A_WIDTH 1
    parameter \B_SIGNED 0
    parameter \B_WIDTH 1
    parameter \Y_WIDTH 1
    connect \A \a
    connect \B \inv_sel
    connect \Y $and$asicworld/verilog/code_hdl_models_mux_2to1_gates.v:14$1_Y
  end
  attribute \src "asicworld/verilog/code_hdl_models_mux_2to1_gates.v:15.5-15.24"
  cell $and $and$asicworld/verilog/code_hdl_models_mux_2to1_gates.v:15$2
    parameter \A_SIGNED 0
    parameter \A_WIDTH 1
    parameter \B_SIGNED 0
    parameter \B_WIDTH 1
    parameter \Y_WIDTH 1
    connect \A \b
    connect \B \sel
    connect \Y $and$asicworld/verilog/code_hdl_models_mux_2to1_gates.v:15$2_Y
  end
  attribute \src "asicworld/verilog/code_hdl_models_mux_2to1_gates.v:0.0-0.0"
  cell $not $not$asicworld/verilog/code_hdl_models_mux_2to1_gates.v:0$4
    parameter \A_SIGNED 0
    parameter \A_WIDTH 1
    parameter \Y_WIDTH 1
    connect \A \sel
    connect \Y $not$asicworld/verilog/code_hdl_models_mux_2to1_gates.v:0$4_Y
  end
  attribute \src "asicworld/verilog/code_hdl_models_mux_2to1_gates.v:16.4-16.22"
  cell $or $or$asicworld/verilog/code_hdl_models_mux_2to1_gates.v:16$3
    parameter \A_SIGNED 0
    parameter \A_WIDTH 1
    parameter \B_SIGNED 0
    parameter \B_WIDTH 1
    parameter \Y_WIDTH 1
    connect \A \asel
    connect \B \bsel
    connect \Y $or$asicworld/verilog/code_hdl_models_mux_2to1_gates.v:16$3_Y
  end
  connect \asel $and$asicworld/verilog/code_hdl_models_mux_2to1_gates.v:14$1_Y
  connect \bsel $and$asicworld/verilog/code_hdl_models_mux_2to1_gates.v:15$2_Y
  connect \y $or$asicworld/verilog/code_hdl_models_mux_2to1_gates.v:16$3_Y
  connect \inv_sel $not$asicworld/verilog/code_hdl_models_mux_2to1_gates.v:0$4_Y
end
