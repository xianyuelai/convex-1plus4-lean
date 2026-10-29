import DominantFiveBody

/-! Specification and proof-interface audit. `main_uniform` instantiates
the actual connection property. Generic conditional assembly theorems
remain visible here so their input types can be compared with the actual
implementations. Whole-paper coverage is checked separately.
-/

set_option pp.proofs false

#print DominantFiveBody.MainUniformStatement
#print DominantFiveBody.ShapeHessianNondegenerate
#print DominantFiveBody.physicalHessian
#print DominantFiveBody.StrictConvexInOrder
#print DominantFiveBody.OrientedSimilar
example : DominantFiveBody.MainUniformStatement := DominantFiveBody.main_uniform
#check @DominantFiveBody.main_uniform
#print axioms DominantFiveBody.main_uniform
#check @DominantFiveBody.finrank_shapeSpace
#check @DominantFiveBody.Coorbital.positiveRemainder_pos
#check @DominantFiveBody.Coorbital.coorbitalKappaForm_pos_on_rotation_slice
#check @DominantFiveBody.coorbital_recover_positive_mass_row
#check @DominantFiveBody.main_of_chart_facts
#check @DominantFiveBody.main_of_no_bad_physical_sequences
#print DominantFiveBody.main_of_chart_facts
#print DominantFiveBody.main_of_no_bad_physical_sequences

#print axioms DominantFiveBody.finrank_shapeSpace
#print axioms DominantFiveBody.normalized_of_primary_differences
#print axioms DominantFiveBody.orientedSimilar_equivalence
#print axioms DominantFiveBody.Coorbital.positiveRemainder_pos
#print axioms DominantFiveBody.Coorbital.coorbitalKappaForm_pos_on_rotation_slice
#print axioms DominantFiveBody.coorbital_recover_positive_mass_row
#print axioms DominantFiveBody.uniformBelow_iff_no_badSequence
#print axioms DominantFiveBody.branches_eq_on_connectionInterval
#print axioms DominantFiveBody.main_of_chart_facts
#print axioms DominantFiveBody.main_of_no_bad_physical_sequences
