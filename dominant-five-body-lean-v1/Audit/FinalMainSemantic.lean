import DominantFiveBody.Main

open scoped BigOperators
namespace DominantFiveBody.Audit

#check main_uniform
#print main_uniform
#print axioms main_uniform
#print axioms orderedSlice_connection
#print axioms orderedSlice_smooth_connection
#print axioms orderedSlice_smooth_connection_explicit
#print axioms fixedAngleDeletedJacobian_isInvertible_iff_shape
#print axioms coorbital_compact_physical_continuation
#print axioms orderedSlice_fixedParameterLocalExistence
#print axioms orderedSlice_localContinuationUniqueness
#print axioms orderedSlice_uniqueness_to_geometric
#print axioms orderedSlice_nondegeneracy_to_geometric
#print axioms geometric_nondegeneracy_of_gauged_normalized
#print axioms finrank_shapeSpace
#print axioms physicalHessian_comp_at_normalizedCC

theorem quarter_ratio_positive : PositiveRatio (fun _ : Satellite => (1/4 : ℝ)) := by
  constructor
  · intro i
    norm_num
  · norm_num [Fin.sum_univ_four]

/-- The conclusion actually supplies a positive parameter and a complete
five-point strictly convex geometric central configuration. -/
theorem main_semantic_positive_parameter_witness :
    ∃ eps : ℝ,0<eps ∧ ∃ x : Configuration,
      StrictConvexCentralConfiguration (masses eps (fun _ => (1/4 : ℝ))) standardHullOrder x := by
  obtain ⟨d,hd,hall⟩ := main_uniform
  obtain ⟨x,hx,_,_⟩ := hall (fun _ => (1/4 : ℝ)) quarter_ratio_positive (d/2)
    (by positivity) (by linarith) standardHullOrder
  exact ⟨d/2,by positivity,x,hx⟩

#print axioms main_semantic_positive_parameter_witness

end DominantFiveBody.Audit
