autoidx 2
module \dut
  wire width 4 $$RTLIL$internalnot$0$output$1
  wire width 4 input 1 \INPUT
  wire width 4 output 2 \OUTPUT
  cell $not $$RTLIL$internalnot$0
    parameter \A_SIGNED 0
    parameter \A_WIDTH 4
    parameter \Y_WIDTH 4
    connect \A \INPUT
    connect \Y $$RTLIL$internalnot$0$output$1
  end
  connect \OUTPUT $$RTLIL$internalnot$0$output$1
end
