import DominantFiveBody.NestedInternal

/-! # Positive-scale equality of each outer Newtonian summand

The coefficient w can vanish. Only the actual scale and actual distance
are divided out. These identities are used to reconstruct the original
mass-divided radial and angular equations.
-/

noncomputable section
open scoped BigOperators ContDiff

namespace DominantFiveBody

set_option maxHeartbeats 800000

theorem nestedOuter_gaps (t eta alpha : ℝ) (y : NestedChartVariables) (i : Fin 2) :
    nestedChartRadii t eta alpha y 2-nestedChartRadii t eta alpha y (i.castAdd 2)=
      t*nestedOuterRadialGaps eta alpha y i ∧
    nestedChartAngles t eta alpha y 2-nestedChartAngles t eta alpha y (i.castAdd 2)=
      t*nestedOuterAngularGaps eta alpha y i := by
  constructor <;> fin_cases i <;>
    dsimp [nestedChartRadii,nestedChartAngles,nestedCoordinates,nestedOuterRadialGaps,nestedOuterAngularGaps] <;> ring

theorem nestedOuter_radial_summand (eps t eta alpha w : ℝ) (y : NestedChartVariables) (i : Fin 2)
    (ht : 0<t) (hV : 0<nestedOuterWSq t eta alpha y i) :
    -eps*(t^3*w)*(nestedChartRadii t eta alpha y (i.castAdd 2)-nestedChartRadii t eta alpha y 2*
      Real.cos (nestedChartAngles t eta alpha y 2-nestedChartAngles t eta alpha y (i.castAdd 2)))/
      satelliteDistance (nestedChartPoints t eta alpha y) (i.castAdd 2) 2^3=
      eps*t*w*nestedOuterN t eta alpha y i := by
  rw [(nestedOuter_gaps t eta alpha y i).2,nestedOuter_distance t eta alpha y i ht hV,nestedOuterN_formula]
  have hnum : nestedChartRadii t eta alpha y (i.castAdd 2)-nestedChartRadii t eta alpha y 2*
      Real.cos (t*nestedOuterAngularGaps eta alpha y i)=
      -t*(nestedOuterRadialGaps eta alpha y i-nestedChartRadii t eta alpha y 2*
        singleScaleChi t (nestedOuterAngularGaps eta alpha y i)) := by
    have hc := singleScaleChi_identity t (nestedOuterAngularGaps eta alpha y i)
    have hr := (nestedOuter_gaps t eta alpha y i).1
    nlinarith [congrArg (fun a : ℝ => nestedChartRadii t eta alpha y 2*a) hc]
  rw [hnum]
  have hn : nestedOuterW t eta alpha y i≠0 := (Real.sqrt_pos.mpr hV).ne'
  field_simp [ht.ne',hn]

theorem nestedOuter_radial_reverse_summand (eps t eta alpha w : ℝ) (y : NestedChartVariables) (i : Fin 2)
    (ht : 0<t) (hV : 0<nestedOuterWSq t eta alpha y i) :
    -eps*(t^3*w)*(nestedChartRadii t eta alpha y 2-nestedChartRadii t eta alpha y (i.castAdd 2)*
      Real.cos (nestedChartAngles t eta alpha y (i.castAdd 2)-nestedChartAngles t eta alpha y 2))/
      satelliteDistance (nestedChartPoints t eta alpha y) 2 (i.castAdd 2)^3=
      -eps*t*w*nestedOuterO t eta alpha y i := by
  have ha : nestedChartAngles t eta alpha y (i.castAdd 2)-nestedChartAngles t eta alpha y 2=
      -(t*nestedOuterAngularGaps eta alpha y i) := by linarith [(nestedOuter_gaps t eta alpha y i).2]
  have hd : satelliteDistance (nestedChartPoints t eta alpha y) 2 (i.castAdd 2)=t*nestedOuterW t eta alpha y i := by
    rw [satelliteDistance,norm_sub_rev]
    exact nestedOuter_distance t eta alpha y i ht hV
  rw [ha,Real.cos_neg,hd,nestedOuterO_formula]
  have hnum : nestedChartRadii t eta alpha y 2-nestedChartRadii t eta alpha y (i.castAdd 2)*
      Real.cos (t*nestedOuterAngularGaps eta alpha y i)=
      t*(nestedOuterRadialGaps eta alpha y i+nestedChartRadii t eta alpha y (i.castAdd 2)*
        singleScaleChi t (nestedOuterAngularGaps eta alpha y i)) := by
    have hc := singleScaleChi_identity t (nestedOuterAngularGaps eta alpha y i)
    have hr := (nestedOuter_gaps t eta alpha y i).1
    nlinarith [congrArg (fun a : ℝ => nestedChartRadii t eta alpha y (i.castAdd 2)*a) hc]
  rw [hnum]
  have hn : nestedOuterW t eta alpha y i≠0 := (Real.sqrt_pos.mpr hV).ne'
  field_simp [ht.ne',hn]

theorem nestedOuter_angular_summand (eps t eta alpha w : ℝ) (y : NestedChartVariables) (i : Fin 2)
    (ht : 0<t) (hV : 0<nestedOuterWSq t eta alpha y i) (heps : 1+eps≠0) :
    (t^3*w)*nestedChartRadii t eta alpha y (i.castAdd 2)*nestedChartRadii t eta alpha y 2*
      Real.sin (nestedChartAngles t eta alpha y 2-nestedChartAngles t eta alpha y (i.castAdd 2))*
        ((satelliteDistance (nestedChartPoints t eta alpha y) (i.castAdd 2) 2^3)⁻¹-(1+eps)⁻¹)=
      t*w*nestedOuterL eps t eta alpha y i := by
  rw [(nestedOuter_gaps t eta alpha y i).2,nestedOuter_distance t eta alpha y i ht hV,nestedOuterL_formula,
    ← sinc_mul_argument (t*nestedOuterAngularGaps eta alpha y i)]
  have hn : nestedOuterW t eta alpha y i≠0 := (Real.sqrt_pos.mpr hV).ne'
  field_simp [ht.ne',hn,heps]

theorem nestedOuter_angular_reverse_summand (eps t eta alpha w : ℝ) (y : NestedChartVariables) (i : Fin 2)
    (ht : 0<t) (hV : 0<nestedOuterWSq t eta alpha y i) (heps : 1+eps≠0) :
    (t^3*w)*nestedChartRadii t eta alpha y 2*nestedChartRadii t eta alpha y (i.castAdd 2)*
      Real.sin (nestedChartAngles t eta alpha y (i.castAdd 2)-nestedChartAngles t eta alpha y 2)*
        ((satelliteDistance (nestedChartPoints t eta alpha y) 2 (i.castAdd 2)^3)⁻¹-(1+eps)⁻¹)=
      -t*w*nestedOuterL eps t eta alpha y i := by
  have ha : nestedChartAngles t eta alpha y (i.castAdd 2)-nestedChartAngles t eta alpha y 2=
      -(t*nestedOuterAngularGaps eta alpha y i) := by linarith [(nestedOuter_gaps t eta alpha y i).2]
  have hd : satelliteDistance (nestedChartPoints t eta alpha y) 2 (i.castAdd 2)=t*nestedOuterW t eta alpha y i := by
    rw [satelliteDistance,norm_sub_rev]
    exact nestedOuter_distance t eta alpha y i ht hV
  rw [ha,Real.sin_neg,hd,nestedOuterL_formula,← sinc_mul_argument (t*nestedOuterAngularGaps eta alpha y i)]
  have hn : nestedOuterW t eta alpha y i≠0 := (Real.sqrt_pos.mpr hV).ne'
  field_simp [ht.ne',hn,heps]

end DominantFiveBody

