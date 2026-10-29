import DominantFiveBody.SmoothOrderedSliceConnection

/-! Theorem 1.1, with all Section 7 physical inputs instantiated. -/

namespace DominantFiveBody

theorem main_uniform : MainUniformStatement :=
  main_of_orderedSlice_connection orderedSlice_connection

end DominantFiveBody
