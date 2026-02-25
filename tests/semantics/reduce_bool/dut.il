autoidx 2
module \dut
  wire $$RTLIL$internalreduce_bool$0$output$1
  wire width 4 input 1 \INPUT
  wire output 2 \OUTPUT
  cell $reduce_bool $$RTLIL$internalreduce_bool$0
    parameter \A_SIGNED 1
    parameter \A_WIDTH 4
    parameter \Y_WIDTH 1
    connect \A \INPUT
    connect \Y $$RTLIL$internalreduce_bool$0$output$1
  end
  connect \OUTPUT $$RTLIL$internalreduce_bool$0$output$1
end
