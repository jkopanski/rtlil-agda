autoidx 6
module \dut
  wire width 5 $$RTLIL$internaladd$0$output$1
  wire width 5 $$RTLIL$internaladd$2$output$3
  wire width 6 $$RTLIL$internaladd$4$output$5
  wire width 16 input 1 \INPUT
  wire width 6 output 2 \OUTPUT
  cell $add $$RTLIL$internaladd$0
    parameter \A_SIGNED 0
    parameter \A_WIDTH 4
    parameter \B_SIGNED 0
    parameter \B_WIDTH 4
    parameter \Y_WIDTH 5
    connect \A \INPUT [15 : 8] [7 : 4]
    connect \B \INPUT [15 : 8] [3 : 0]
    connect \Y $$RTLIL$internaladd$0$output$1
  end
  cell $add $$RTLIL$internaladd$2
    parameter \A_SIGNED 0
    parameter \A_WIDTH 4
    parameter \B_SIGNED 0
    parameter \B_WIDTH 4
    parameter \Y_WIDTH 5
    connect \A \INPUT [7 : 0] [7 : 4]
    connect \B \INPUT [7 : 0] [3 : 0]
    connect \Y $$RTLIL$internaladd$2$output$3
  end
  cell $add $$RTLIL$internaladd$4
    parameter \A_SIGNED 0
    parameter \A_WIDTH 5
    parameter \B_SIGNED 0
    parameter \B_WIDTH 5
    parameter \Y_WIDTH 6
    connect \A { $$RTLIL$internaladd$0$output$1 $$RTLIL$internaladd$2$output$3 } [9 : 5]
    connect \B { $$RTLIL$internaladd$0$output$1 $$RTLIL$internaladd$2$output$3 } [4 : 0]
    connect \Y $$RTLIL$internaladd$4$output$5
  end
  connect \OUTPUT $$RTLIL$internaladd$4$output$5
end
