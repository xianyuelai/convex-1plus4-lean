import DominantFiveBody.ResidualEquivalence

/-! Exact solution-level identities in the last paragraph before Lemma 3.1.
The field, angular and tangential residuals retain their physical definitions.
-/

noncomputable section
open scoped BigOperators

namespace DominantFiveBody

/-- TeX §3 line 272: the actual weighted vector equation recovers
`Y = (1 + eps)⁻¹ X`, without an additional mass lower bound. -/
theorem relativeField_eq_scaledAverage_of_vectorRoot (eps : ℝ) (mu : MassRatio)
    (hsum : ∑ i, mu i = 1) (hden : 1 + eps ≠ 0) (q : SatelliteConfiguration)
    (hroot : ∀ i, vectorResidual eps mu q i = 0) :
    relativeField mu q = (1 + eps)⁻¹ • relativeAverage mu q := by
  have h := vectorResidual_weighted_sum eps mu hsum q
  simp only [hroot, smul_zero, Finset.sum_const_zero] at h
  have hX : relativeAverage mu q = (1 + eps) • relativeField mu q :=
    sub_eq_zero.mp h.symm
  rw [hX, smul_smul, inv_mul_cancel₀ hden, one_smul]

/-- TeX §3 lines 272–273 on an actual multiplier-one configuration:
the true primary field is recovered, and `T_i = rho_i Q_i` for every row. -/
theorem sectionThree_solution_field_and_tangential_identity
    (eps : ℝ) (mu : MassRatio) (x : Configuration)
    (hx : NormalizedCentralConfiguration (masses eps mu) x)
    (hm : PositiveRatio mu) (heps : 0 < eps) (r theta : Satellite → ℝ)
    (hr : ∀ i, 0 < r i) (hpolar : satellitesRelative x = polarSatellites r theta) :
    relativeField mu (polarSatellites r theta) =
      (1 + eps)⁻¹ • relativeAverage mu (polarSatellites r theta) ∧
    ∀ i, angularResidual eps mu r theta i = r i * tangentialResidual mu r theta i := by
  have hroot : ∀ i, vectorResidual eps mu (polarSatellites r theta) i = 0 := by
    rw [← hpolar]
    exact vectorResidual_zero_of_normalized eps mu x hx
  constructor
  · exact relativeField_eq_scaledAverage_of_vectorRoot eps mu hm.2
      (by positivity) _ hroot
  · have hangular := (polarResiduals_zero_of_normalized eps mu x hx hm heps r theta hr hpolar).2
    have htangential := tangentialResidual_zero_of_normalized eps mu x hx
      (ne_of_gt heps) r theta hr hpolar
    intro i
    rw [hangular i, htangential i, mul_zero]

end DominantFiveBody
