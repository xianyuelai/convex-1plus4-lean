import DominantFiveBody.NestedRecovery

/-! # Actual zero-epsilon nested roots on every signed scale face

Both radial differences vanish by positive coefficients. No division by
t, eta, alpha or 1-alpha occurs; endpoints and negative extension scales
are therefore included. This is used for derivatives along the full root.
-/

noncomputable section
open scoped BigOperators
namespace DominantFiveBody
set_option maxHeartbeats 800000

theorem nestedRadialInnerDifference_zero_eps (t eta alpha : ℝ) (y : NestedChartVariables) :
    nestedRadialInnerDifference 0 t eta alpha y = y 3*
      (1+(nestedChartRadii t eta alpha y 0+nestedChartRadii t eta alpha y 1)/
        (nestedChartRadii t eta alpha y 0^2*nestedChartRadii t eta alpha y 1^2)) := by
  simp [nestedRadialInnerDifference,nestedRadialExteriorDifference,
    nestedInternalRadialInnerDifference,pairInternalRadialDifference,
    nestedEdgeRadialGap,nestedEdgeSource,nestedEdgeTarget]

theorem nestedRadialOuterDifference_zero_eps_of_inner_zero (t eta alpha : ℝ)
    (y : NestedChartVariables) (hu : y 3=0) :
    nestedRadialOuterDifference 0 t eta alpha y = y 2*
      (1+(nestedChartRadii t eta alpha y 0+nestedChartRadii t eta alpha y 2)/
        (nestedChartRadii t eta alpha y 0^2*nestedChartRadii t eta alpha y 2^2)) := by
  have hr : nestedChartRadii t eta alpha y 1=nestedChartRadii t eta alpha y 0 := by
    simp [nestedChartRadii,nestedCoordinates,hu]
  simp only [nestedRadialOuterDifference,nestedRadialExteriorDifference,
    nestedInternalRadialOuterDifference,nestedInnerJOverT,zero_mul,neg_zero,sub_zero,
    add_zero]
  simp only [nestedEdgeRadialGap,nestedEdgeSource,nestedEdgeTarget,
    Matrix.cons_val_zero,Matrix.cons_val_one,nestedOuterRadialGaps,hu,mul_zero,add_zero,
    sub_zero,hr]
  ring

theorem nestedChart_zero_eps_all_scale_faces (t eta alpha : ℝ) (y : NestedChartVariables)
    (hr : ∀ i, 0<nestedChartRadii t eta alpha y i)
    (hroot : nestedChartExtendedRows 0 t eta alpha y=0) :
    (∀ i,nestedChartRadii t eta alpha y i=1) ∧ y 2=0 ∧ y 3=0 ∧ y 0=1 ∧ y 1=1 := by
  have hu2 : y 3=0 := by
    have hrow : nestedRadialInnerDifference 0 t eta alpha y=0 := congrFun hroot 3
    rw [nestedRadialInnerDifference_zero_eps] at hrow
    have hpos : 0<(1+(nestedChartRadii t eta alpha y 0+nestedChartRadii t eta alpha y 1)/
        (nestedChartRadii t eta alpha y 0^2*nestedChartRadii t eta alpha y 1^2)) := by
      have ha := hr 0
      have hb := hr 1
      positivity
    exact (mul_eq_zero.mp hrow).resolve_right hpos.ne'
  have hu1 : y 2=0 := by
    have hrow : nestedRadialOuterDifference 0 t eta alpha y=0 := congrFun hroot 2
    rw [nestedRadialOuterDifference_zero_eps_of_inner_zero t eta alpha y hu2] at hrow
    have hpos : 0<(1+(nestedChartRadii t eta alpha y 0+nestedChartRadii t eta alpha y 2)/
        (nestedChartRadii t eta alpha y 0^2*nestedChartRadii t eta alpha y 2^2)) := by
      have ha := hr 0
      have hb := hr 2
      positivity
    exact (mul_eq_zero.mp hrow).resolve_right hpos.ne'
  have hRadii (i : Fin 3) : nestedChartRadii t eta alpha y i.castSucc=y 1 := by
    fin_cases i <;> simp [nestedChartRadii,nestedCoordinates,hu1,hu2]
  have hp : y 0=1 := by
    apply positive_radial_zero_eq_one
    · exact hr 3
    · have hrow : radialResidual 0 (nestedChartMass t eta alpha)
          (nestedChartRadii t eta alpha y) (nestedChartAngles t eta alpha y) 3=0 := congrFun hroot 0
      simpa [radialResidual_at_zero,nestedChartRadii] using hrow
  have hR : y 1=1 := by
    apply positive_radial_zero_eq_one
    · exact (hRadii 0) ▸ hr 0
    · have hmean : nestedRadialMean 0 t eta alpha y=0 := congrFun hroot 1
      have h0 := hRadii 0
      have h1 := hRadii 1
      have h2 := hRadii 2
      change nestedChartRadii t eta alpha y 0=y 1 at h0
      change nestedChartRadii t eta alpha y 1=y 1 at h1
      change nestedChartRadii t eta alpha y 2=y 1 at h2
      simp only [nestedRadialMean,nestedRowAverage,nestedPairAverage,nestedRadialExterior,
        nestedInternalRadialMean,nestedInnerJ,pairInternalRadialMean,
        zero_mul,neg_zero,mul_zero,add_zero,h0,h1,h2] at hmean
      linear_combination hmean
  refine ⟨?_,hu1,hu2,hp,hR⟩
  intro i
  fin_cases i
  · exact (hRadii 0).trans hR
  · exact (hRadii 1).trans hR
  · exact (hRadii 2).trans hR
  · exact hp

end DominantFiveBody
