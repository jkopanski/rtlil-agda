autoidx 2
module \dut
  wire $$RTLIL$internallogic_not$0$output$1
  wire width 4 input 1 \INPUT
  wire output 2 \OUTPUT
  cell $logic_not $$RTLIL$internallogic_not$0
    parameter \A_SIGNED 0
    parameter \A_WIDTH 4
    parameter \Y_WIDTH 1
    connect \A \INPUT
    connect \Y $$RTLIL$internallogic_not$0$output$1
  end
  connect \OUTPUT $$RTLIL$internallogic_not$0$output$1
end
