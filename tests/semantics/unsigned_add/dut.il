module $RTLIL$Library$Unsigned$add
  wire width 4 input 1 \M
  wire width 4 input 2 \N
  wire width 5 output 3 \OUT
  cell $add $internal$unsigned$add
    parameter \A_SIGNED 0
    parameter \A_WIDTH 4
    parameter \B_SIGNED 0
    parameter \B_WIDTH 4
    parameter \Y_WIDTH 5
    connect \A \M
    connect \B \N
    connect \Y \OUT
  end
end
