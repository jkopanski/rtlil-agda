autoidx 2
module \dut
  wire width 5 $$RTLIL$internaladd$0$output$1
  wire width 8 input 1 \INPUT
  wire width 5 output 2 \OUTPUT
  cell $add $$RTLIL$internaladd$0
    parameter \A_SIGNED 0
    parameter \A_WIDTH 4
    parameter \B_SIGNED 0
    parameter \B_WIDTH 4
    parameter \Y_WIDTH 5
    connect \A \INPUT [7 : 4]
    connect \B \INPUT [3 : 0]
    connect \Y $$RTLIL$internaladd$0$output$1
  end
  connect \OUTPUT $$RTLIL$internaladd$0$output$1
end
