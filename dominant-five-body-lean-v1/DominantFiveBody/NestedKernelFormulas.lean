import DominantFiveBody.NestedKernelDifferences

/-! # Scalar formulas for the actual two-scale Newton fields

These identify the vector implementation with the manuscript's N, O, L
and M. In particular the η quotients proved in NestedKernelDifferences
are quotients of the actual displayed scalar kernels.
-/

noncomputable section
open scoped BigOperators ContDiff

namespace DominantFiveBody

set_option maxHeartbeats 800000

theorem pairPointDirection_radial_left (t alpha : ℝ) (y : PairChartVariables) :
    inner ℝ (pairPointDirection t alpha y) (polarPoint 1 (pairChartAngles t alpha y 0))=
      y 3-pairChartRadii t alpha y 1*singleScaleChi t (y 6) := by
  by_cases ht : t=0
  · subst t
    simp only [pairPointDirection,pairUnitDirection,pairChartRadii,pairChartAngles,singleScaleChi]
    simp
    simp only [inner_add_left,real_inner_smul_left,polarPoint_inner_same]
    rw [← real_inner_comm (quarterTurn (polarPoint 1 (y 5))),quarterTurn_inner_self]
    ring
  · apply mul_left_cancel₀ ht
    rw [← real_inner_smul_left,← pairPointDirection_identity]
    simp only [inner_sub_left,polarPoint_inner_radial,sub_self,Real.cos_zero,mul_one,pairChart_angle_gap]
    have hc := singleScaleChi_identity t (y 6)
    have hr := pairChart_radius_gap t alpha y
    nlinarith [congrArg (fun a : ℝ => pairChartRadii t alpha y 1*a) hc]

theorem pairPointDirection_radial_right (t alpha : ℝ) (y : PairChartVariables) :
    inner ℝ (pairPointDirection t alpha y) (polarPoint 1 (pairChartAngles t alpha y 1))=
      y 3+pairChartRadii t alpha y 0*singleScaleChi t (y 6) := by
  by_cases ht : t=0
  · subst t
    simp only [pairPointDirection,pairUnitDirection,pairChartRadii,pairChartAngles,singleScaleChi]
    simp
    simp only [inner_add_left,real_inner_smul_left,polarPoint_inner_same]
    rw [← real_inner_comm (quarterTurn (polarPoint 1 (y 5))),quarterTurn_inner_self]
    ring
  · apply mul_left_cancel₀ ht
    rw [← real_inner_smul_left,← pairPointDirection_identity]
    simp only [inner_sub_left,polarPoint_inner_radial,sub_self,Real.cos_zero,mul_one]
    rw [show pairChartAngles t alpha y 0-pairChartAngles t alpha y 1=
      -(pairChartAngles t alpha y 1-pairChartAngles t alpha y 0) by ring,Real.cos_neg,pairChart_angle_gap]
    have hc := singleScaleChi_identity t (y 6)
    have hr := pairChart_radius_gap t alpha y
    nlinarith [congrArg (fun a : ℝ => pairChartRadii t alpha y 0*a) hc]

theorem pairPointDirection_angular_left (t alpha : ℝ) (y : PairChartVariables) :
    inner ℝ (pairPointDirection t alpha y)
      (quarterTurn (polarPoint (pairChartRadii t alpha y 0) (pairChartAngles t alpha y 0)))=
      pairChartRadii t alpha y 0*pairChartRadii t alpha y 1*y 6*Real.sinc (t*y 6) := by
  by_cases ht : t=0
  · subst t
    simp only [pairPointDirection,pairUnitDirection,pairChartRadii,pairChartAngles]
    simp
    rw [polarPoint_rotation_smul (y 2) (y 5)]
    simp only [inner_add_left,real_inner_smul_left,real_inner_smul_right,
      quarterTurn_inner_self,quarterTurn_inner_quarterTurn,polarPoint_inner_same]
    ring
  · apply mul_left_cancel₀ ht
    rw [← real_inner_smul_left,← pairPointDirection_identity]
    simp only [inner_sub_left,polarPoint_inner_rotation,sub_self,Real.sin_zero,mul_zero,sub_zero]
    rw [pairChart_angle_gap,← sinc_mul_argument (t*y 6)]
    ring

theorem nestedOuterN_formula (t eta alpha : ℝ) (y : NestedChartVariables) (i : Fin 2) :
    nestedOuterN t eta alpha y i=
      (nestedOuterRadialGaps eta alpha y i-nestedChartRadii t eta alpha y 2*
        singleScaleChi t (nestedOuterAngularGaps eta alpha y i))*(nestedOuterW t eta alpha y i^3)⁻¹ := by
  have h := pairPointDirection_radial_left t 1 (nestedOuterVariables t eta alpha y i)
  obtain ⟨hra,hrb,haa,hab⟩ := nestedOuter_coordinates t eta alpha y i
  rw [hrb,haa] at h
  unfold nestedOuterN nestedOuterNewton scaledNewtonField
  rw [real_inner_smul_left,nestedOuterDirection_norm]
  change (nestedOuterW t eta alpha y i^3)⁻¹*
    inner ℝ (pairPointDirection t 1 (nestedOuterVariables t eta alpha y i))
      (polarPoint 1 (nestedChartAngles t eta alpha y (i.castAdd 2)))=_
  rw [h]
  exact mul_comm _ _

theorem nestedOuterO_formula (t eta alpha : ℝ) (y : NestedChartVariables) (i : Fin 2) :
    nestedOuterO t eta alpha y i=
      (nestedOuterRadialGaps eta alpha y i+nestedChartRadii t eta alpha y (i.castAdd 2)*
        singleScaleChi t (nestedOuterAngularGaps eta alpha y i))*(nestedOuterW t eta alpha y i^3)⁻¹ := by
  have h := pairPointDirection_radial_right t 1 (nestedOuterVariables t eta alpha y i)
  obtain ⟨hra,hrb,haa,hab⟩ := nestedOuter_coordinates t eta alpha y i
  rw [hra,hab] at h
  unfold nestedOuterO nestedOuterNewton scaledNewtonField
  rw [real_inner_smul_left,nestedOuterDirection_norm]
  change (nestedOuterW t eta alpha y i^3)⁻¹*
    inner ℝ (pairPointDirection t 1 (nestedOuterVariables t eta alpha y i))
      (polarPoint 1 (nestedChartAngles t eta alpha y 2))=_
  rw [h]
  exact mul_comm _ _

theorem nestedOuterL_formula (eps t eta alpha : ℝ) (y : NestedChartVariables) (i : Fin 2) :
    nestedOuterL eps t eta alpha y i=
      nestedChartRadii t eta alpha y (i.castAdd 2)*nestedChartRadii t eta alpha y 2*
        nestedOuterAngularGaps eta alpha y i*Real.sinc (t*nestedOuterAngularGaps eta alpha y i)*
          ((nestedOuterW t eta alpha y i^3)⁻¹-t^3/(1+eps)) := by
  have h := pairPointDirection_angular_left t 1 (nestedOuterVariables t eta alpha y i)
  obtain ⟨hra,hrb,haa,hab⟩ := nestedOuter_coordinates t eta alpha y i
  rw [hra,hrb,haa] at h
  unfold nestedOuterL nestedOuterAngularField nestedOuterNewton scaledNewtonField
  rw [inner_sub_left,real_inner_smul_left,real_inner_smul_left,nestedOuterDirection_norm]
  change (nestedOuterW t eta alpha y i^3)⁻¹*inner ℝ (pairPointDirection t 1 (nestedOuterVariables t eta alpha y i))
    (quarterTurn (polarPoint (nestedChartRadii t eta alpha y (i.castAdd 2)) (nestedChartAngles t eta alpha y (i.castAdd 2))))-
    t^3/(1+eps)*inner ℝ (pairPointDirection t 1 (nestedOuterVariables t eta alpha y i))
    (quarterTurn (polarPoint (nestedChartRadii t eta alpha y (i.castAdd 2)) (nestedChartAngles t eta alpha y (i.castAdd 2))))=_
  rw [h]
  change _=nestedChartRadii t eta alpha y (i.castAdd 2)*nestedChartRadii t eta alpha y 2*
    nestedOuterVariables t eta alpha y i 6*Real.sinc (t*nestedOuterVariables t eta alpha y i 6)*_
  ring

end DominantFiveBody
