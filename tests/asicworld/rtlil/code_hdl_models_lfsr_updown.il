autoidx 11
attribute \cells_not_processed 1
attribute \src "asicworld/verilog/code_hdl_models_lfsr_updown.v:2.1-35.10"
module \lfsr_updown
  attribute \src "asicworld/verilog/code_hdl_models_lfsr_updown.v:24.2-33.5"
  wire width 8 $0\count[7:0]
  attribute \src "asicworld/verilog/code_hdl_models_lfsr_updown.v:29.21-29.41"
  wire width 8 $and$asicworld/verilog/code_hdl_models_lfsr_updown.v:29$5_Y
  attribute \src "asicworld/verilog/code_hdl_models_lfsr_updown.v:31.35-31.56"
  wire width 8 $and$asicworld/verilog/code_hdl_models_lfsr_updown.v:31$8_Y
  attribute \src "asicworld/verilog/code_hdl_models_lfsr_updown.v:21.33-21.62"
  wire $eq$asicworld/verilog/code_hdl_models_lfsr_updown.v:21$1_Y
  attribute \src "asicworld/verilog/code_hdl_models_lfsr_updown.v:22.33-22.62"
  wire $eq$asicworld/verilog/code_hdl_models_lfsr_updown.v:22$2_Y
  attribute \src "asicworld/verilog/code_hdl_models_lfsr_updown.v:29.17-29.43"
  wire $not$asicworld/verilog/code_hdl_models_lfsr_updown.v:29$7_Y
  attribute \src "asicworld/verilog/code_hdl_models_lfsr_updown.v:31.31-31.58"
  wire $not$asicworld/verilog/code_hdl_models_lfsr_updown.v:31$10_Y
  attribute \src "asicworld/verilog/code_hdl_models_lfsr_updown.v:29.19-29.42"
  wire $reduce_xor$asicworld/verilog/code_hdl_models_lfsr_updown.v:29$6_Y
  attribute \src "asicworld/verilog/code_hdl_models_lfsr_updown.v:31.33-31.57"
  wire $reduce_xor$asicworld/verilog/code_hdl_models_lfsr_updown.v:31$9_Y
  attribute \src "asicworld/verilog/code_hdl_models_lfsr_updown.v:21.20-22.63"
  wire $ternary$asicworld/verilog/code_hdl_models_lfsr_updown.v:21$3_Y
  attribute \src "asicworld/verilog/code_hdl_models_lfsr_updown.v:11.8-11.11"
  wire input 1 \clk
  attribute \src "asicworld/verilog/code_hdl_models_lfsr_updown.v:16.20-16.25"
  wire width 8 output 5 \count
  attribute \src "asicworld/verilog/code_hdl_models_lfsr_updown.v:13.8-13.14"
  wire input 3 \enable
  attribute \src "asicworld/verilog/code_hdl_models_lfsr_updown.v:17.9-17.17"
  wire output 6 \overflow
  attribute \src "asicworld/verilog/code_hdl_models_lfsr_updown.v:12.8-12.13"
  wire input 2 \reset
  attribute \src "asicworld/verilog/code_hdl_models_lfsr_updown.v:14.8-14.15"
  wire input 4 \up_down
  attribute \src "asicworld/verilog/code_hdl_models_lfsr_updown.v:29.21-29.41"
  cell $and $and$asicworld/verilog/code_hdl_models_lfsr_updown.v:29$5
    parameter \A_SIGNED 0
    parameter \A_WIDTH 8
    parameter \B_SIGNED 0
    parameter \B_WIDTH 8
    parameter \Y_WIDTH 8
    connect \A \count
    connect \B 8'01100011
    connect \Y $and$asicworld/verilog/code_hdl_models_lfsr_updown.v:29$5_Y
  end
  attribute \src "asicworld/verilog/code_hdl_models_lfsr_updown.v:31.35-31.56"
  cell $and $and$asicworld/verilog/code_hdl_models_lfsr_updown.v:31$8
    parameter \A_SIGNED 0
    parameter \A_WIDTH 8
    parameter \B_SIGNED 0
    parameter \B_WIDTH 8
    parameter \Y_WIDTH 8
    connect \A \count
    connect \B 8'10110001
    connect \Y $and$asicworld/verilog/code_hdl_models_lfsr_updown.v:31$8_Y
  end
  attribute \src "asicworld/verilog/code_hdl_models_lfsr_updown.v:21.33-21.62"
  cell $eq $eq$asicworld/verilog/code_hdl_models_lfsr_updown.v:21$1
    parameter \A_SIGNED 0
    parameter \A_WIDTH 8
    parameter \B_SIGNED 0
    parameter \B_WIDTH 8
    parameter \Y_WIDTH 1
    connect \A \count
    connect \B 8'00000001
    connect \Y $eq$asicworld/verilog/code_hdl_models_lfsr_updown.v:21$1_Y
  end
  attribute \src "asicworld/verilog/code_hdl_models_lfsr_updown.v:22.33-22.62"
  cell $eq $eq$asicworld/verilog/code_hdl_models_lfsr_updown.v:22$2
    parameter \A_SIGNED 0
    parameter \A_WIDTH 8
    parameter \B_SIGNED 0
    parameter \B_WIDTH 8
    parameter \Y_WIDTH 1
    connect \A \count
    connect \B 8'10000000
    connect \Y $eq$asicworld/verilog/code_hdl_models_lfsr_updown.v:22$2_Y
  end
  attribute \src "asicworld/verilog/code_hdl_models_lfsr_updown.v:29.17-29.43"
  cell $not $not$asicworld/verilog/code_hdl_models_lfsr_updown.v:29$7
    parameter \A_SIGNED 0
    parameter \A_WIDTH 1
    parameter \Y_WIDTH 1
    connect \A $reduce_xor$asicworld/verilog/code_hdl_models_lfsr_updown.v:29$6_Y
    connect \Y $not$asicworld/verilog/code_hdl_models_lfsr_updown.v:29$7_Y
  end
  attribute \src "asicworld/verilog/code_hdl_models_lfsr_updown.v:31.31-31.58"
  cell $not $not$asicworld/verilog/code_hdl_models_lfsr_updown.v:31$10
    parameter \A_SIGNED 0
    parameter \A_WIDTH 1
    parameter \Y_WIDTH 1
    connect \A $reduce_xor$asicworld/verilog/code_hdl_models_lfsr_updown.v:31$9_Y
    connect \Y $not$asicworld/verilog/code_hdl_models_lfsr_updown.v:31$10_Y
  end
  attribute \src "asicworld/verilog/code_hdl_models_lfsr_updown.v:29.19-29.42"
  cell $reduce_xor $reduce_xor$asicworld/verilog/code_hdl_models_lfsr_updown.v:29$6
    parameter \A_SIGNED 0
    parameter \A_WIDTH 8
    parameter \Y_WIDTH 1
    connect \A $and$asicworld/verilog/code_hdl_models_lfsr_updown.v:29$5_Y
    connect \Y $reduce_xor$asicworld/verilog/code_hdl_models_lfsr_updown.v:29$6_Y
  end
  attribute \src "asicworld/verilog/code_hdl_models_lfsr_updown.v:31.33-31.57"
  cell $reduce_xor $reduce_xor$asicworld/verilog/code_hdl_models_lfsr_updown.v:31$9
    parameter \A_SIGNED 0
    parameter \A_WIDTH 8
    parameter \Y_WIDTH 1
    connect \A $and$asicworld/verilog/code_hdl_models_lfsr_updown.v:31$8_Y
    connect \Y $reduce_xor$asicworld/verilog/code_hdl_models_lfsr_updown.v:31$9_Y
  end
  attribute \src "asicworld/verilog/code_hdl_models_lfsr_updown.v:21.20-22.63"
  cell $mux $ternary$asicworld/verilog/code_hdl_models_lfsr_updown.v:21$3
    parameter \WIDTH 1
    connect \A $eq$asicworld/verilog/code_hdl_models_lfsr_updown.v:22$2_Y
    connect \B $eq$asicworld/verilog/code_hdl_models_lfsr_updown.v:21$1_Y
    connect \S \up_down
    connect \Y $ternary$asicworld/verilog/code_hdl_models_lfsr_updown.v:21$3_Y
  end
  attribute \src "asicworld/verilog/code_hdl_models_lfsr_updown.v:24.2-33.5"
  process $proc$asicworld/verilog/code_hdl_models_lfsr_updown.v:24$4
    assign $0\count[7:0] \count
    attribute \src "asicworld/verilog/code_hdl_models_lfsr_updown.v:25.2-33.5"
    switch \reset
      attribute \src "asicworld/verilog/code_hdl_models_lfsr_updown.v:25.6-25.11"
      case 1'1
        assign $0\count[7:0] 8'00000000
      attribute \src "asicworld/verilog/code_hdl_models_lfsr_updown.v:27.2-27.6"
      case 
        attribute \src "asicworld/verilog/code_hdl_models_lfsr_updown.v:27.7-33.5"
        switch \enable
          attribute \src "asicworld/verilog/code_hdl_models_lfsr_updown.v:27.11-27.17"
          case 1'1
            attribute \src "asicworld/verilog/code_hdl_models_lfsr_updown.v:28.5-32.8"
            switch \up_down
              attribute \src "asicworld/verilog/code_hdl_models_lfsr_updown.v:28.9-28.16"
              case 1'1
                assign $0\count[7:0] { $not$asicworld/verilog/code_hdl_models_lfsr_updown.v:29$7_Y \count [7:1] }
              attribute \src "asicworld/verilog/code_hdl_models_lfsr_updown.v:30.9-30.13"
              case 
                assign $0\count[7:0] { \count [6:0] $not$asicworld/verilog/code_hdl_models_lfsr_updown.v:31$10_Y }
            end
          case 
        end
    end
    sync posedge \clk
      update \count $0\count[7:0]
  end
  connect \overflow $ternary$asicworld/verilog/code_hdl_models_lfsr_updown.v:21$3_Y
end
