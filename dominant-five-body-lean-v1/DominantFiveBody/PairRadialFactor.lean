import DominantFiveBody.PairPhysicalContinuation

/-! # Exact ε factor in the radial split, with uniform compact bounds

This identity is evaluated along the actual root: all unknown-dependent
terms remain in the factor, including the implicit root dependence.
-/

noncomputable section
open scoped BigOperators ContDiff
open Filter Set Topology

namespace DominantFiveBody

def pairRadialLeadingCoefficient (t alpha : ℝ) (y : PairChartVariables) : ℝ :=
  1+(pairChartRadii t alpha y 0+pairChartRadii t alpha y 1)/
    (pairChartRadii t alpha y 0^2*pairChartRadii t alpha y 1^2)

def pairRadialEpsCoefficient (eps t p alpha : ℝ) (y : PairChartVariables) : ℝ :=
  inner ℝ (pairExteriorNewtonDifference t p alpha y) (polarPoint 1 (pairChartAngles t alpha y 1))+
    inner ℝ (pairExteriorRadialField eps t p alpha y (pairChartPoints t alpha y 0))
      (pairUnitDirection t alpha y)-
    (y 3+(alpha*pairChartRadii t alpha y 0-(1-alpha)*pairChartRadii t alpha y 1)*singleScaleChi t (y 6))*
      (pairChartW t alpha y^3)⁻¹

def pairRadialRootQuotient (v : PairJointVariables) : ℝ :=
  -pairRadialEpsCoefficient (v.1 0) (v.1 1) (v.1 2) (v.1 3) v.2/
    pairRadialLeadingCoefficient (v.1 1) (v.1 3) v.2

theorem pairRadialDifference_eps_identity (eps t p alpha : ℝ) (y : PairChartVariables) :
    pairRadialDifference eps t p alpha y=y 3*pairRadialLeadingCoefficient t alpha y+
      eps*pairRadialEpsCoefficient eps t p alpha y := by
  unfold pairRadialDifference pairRadialLeadingCoefficient pairRadialEpsCoefficient pairInternalRadialDifference
  ring

theorem pairRadialLeadingCoefficient_pos (t alpha : ℝ) (y : PairChartVariables)
    (hr : ∀ i, 0<pairChartRadii t alpha y i) : 0<pairRadialLeadingCoefficient t alpha y := by
  unfold pairRadialLeadingCoefficient
  have ha := hr 0
  have hb := hr 1
  positivity

theorem pairRadial_root_exact_factor (eps t p alpha : ℝ) (keepD : Bool) (y : PairChartVariables)
    (hr : ∀ i, 0<pairChartRadii t alpha y i)
    (hroot : pairChartExtendedRows eps t p alpha keepD y=0) :
    y 3=eps*pairRadialRootQuotient ((![eps,t,p,alpha] : PairChartParameters),y) := by
  have hrow : pairRadialDifference eps t p alpha y=0 := congrFun hroot 3
  rw [pairRadialDifference_eps_identity] at hrow
  change y 3=eps*(-pairRadialEpsCoefficient eps t p alpha y/pairRadialLeadingCoefficient t alpha y)
  have hn := (pairRadialLeadingCoefficient_pos t alpha y hr).ne'
  field_simp
  linear_combination hrow

theorem pairRadialRootQuotient_contDiffAt (n : ℕ∞ω) (v : PairJointVariables)
    (hreg : PairChartRegular (v.1 0) (v.1 1) (v.1 3) v.2)
    (hr : ∀ i, 0<pairChartRadii (v.1 1) (v.1 3) v.2 i) :
    ContDiffAt ℝ n pairRadialRootQuotient v := by
  have hsep := pairChartRegular_external_pair _ _ _ _ hreg
  have hra := (pairChartRadii_joint_contDiff n 0).contDiffAt (x := v)
  have hrb := (pairChartRadii_joint_contDiff n 1).contDiffAt (x := v)
  have hone : ContDiffAt ℝ n (fun _ : PairJointVariables => (1 : ℝ)) v := contDiffAt_const
  have ht : ContDiffAt ℝ n (fun w : PairJointVariables => w.1 1) v := by fun_prop
  have ha : ContDiffAt ℝ n (fun w : PairJointVariables => w.1 3) v := by fun_prop
  have hu : ContDiffAt ℝ n (fun w : PairJointVariables => w.2 3) v := by fun_prop
  have hz : ContDiffAt ℝ n (fun w : PairJointVariables => w.2 6) v := by fun_prop
  have hlead : ContDiffAt ℝ n (fun w : PairJointVariables => pairRadialLeadingCoefficient (w.1 1) (w.1 3) w.2) v :=
    contDiffAt_const.add ((hra.add hrb).div ((hra.pow 2).mul (hrb.pow 2))
      (mul_ne_zero (pow_ne_zero 2 (hreg.2.1 0)) (pow_ne_zero 2 (hreg.2.1 1))))
  have hW := pairChartW_joint_contDiffAt n v hreg.2.2.1
  have hChi : ContDiffAt ℝ n (fun w : PairJointVariables => singleScaleChi (w.1 1) (w.2 6)) v := by
    exact (singleScaleChi_contDiff n).contDiffAt.comp v (ht.prodMk hz)
  have hrem := (hu.add (((ha.mul hra).sub ((hone.sub ha).mul hrb)).mul hChi)).mul
    ((hW.pow 3).inv (pow_ne_zero 3 (ne_of_gt (Real.sqrt_pos.mpr hreg.2.2.1))))
  have hB : ContDiffAt ℝ n (fun w : PairJointVariables =>
      pairRadialEpsCoefficient (w.1 0) (w.1 1) (w.1 2) (w.1 3) w.2) v :=
    (((pairExteriorNewtonDifference_joint_contDiffAt n v hsep).inner ℝ (pairUnit_joint_contDiff n 1).contDiffAt).add
      ((pairExteriorRadialField_joint_contDiffAt n v 0 hreg.1 (fun j hj => (hsep j hj).1)).inner ℝ
        (pairUnitDirection_joint_contDiff n).contDiffAt)).sub hrem
  exact hB.neg.div hlead (pairRadialLeadingCoefficient_pos _ _ _ hr).ne'

/-- A single O(ε) constant and ambient neighborhood cover any compact
regular root graph with positive radii; zero scales and α endpoints are
allowed.  The factor uses the actual unknowns, so branch dependence is
fully included. -/
theorem pairRadial_root_compact_uniform_bound (K : Set PairJointVariables) (hK : IsCompact K)
    (hdata : ∀ v∈K, PairChartRegular (v.1 0) (v.1 1) (v.1 3) v.2 ∧
      ∀ i, 0<pairChartRadii (v.1 1) (v.1 3) v.2 i) :
    ∃ C : ℝ, 0<C ∧ ∃ U : Set PairJointVariables, IsOpen U ∧ K⊆U ∧
      ∀ v∈U, ∀ keepD : Bool,
        pairChartExtendedRows (v.1 0) (v.1 1) (v.1 2) (v.1 3) keepD v.2=0 →
        |v.2 3|≤C*|v.1 0| := by
  have hc : ContinuousOn pairRadialRootQuotient K := fun v hv =>
    (pairRadialRootQuotient_contDiffAt 0 v (hdata v hv).1 (hdata v hv).2).continuousAt.continuousWithinAt
  obtain ⟨B,hB⟩ := hK.bddAbove_image hc.norm
  let C := |B|+1
  let U : Set PairJointVariables := interior {v | (∀ i, 0<pairChartRadii (v.1 1) (v.1 3) v.2 i) ∧
    |pairRadialRootQuotient v|<C}
  refine ⟨C,by dsimp [C]; positivity,U,isOpen_interior,?_,?_⟩
  · intro v hv
    apply mem_interior_iff_mem_nhds.mpr
    have hb : |pairRadialRootQuotient v|<C := by
      have he := hB (Set.mem_image_of_mem _ hv)
      simp only [Real.norm_eq_abs] at he
      dsimp [C]
      linarith [le_abs_self B]
    have hnorm := (pairRadialRootQuotient_contDiffAt 0 v (hdata v hv).1 (hdata v hv).2).continuousAt.abs
      |>.eventually (Iio_mem_nhds hb)
    have hrad := pairChartPositiveRadii_isOpen.mem_nhds (hdata v hv).2
    exact Filter.Eventually.and hrad hnorm
  · intro v hv keepD hroot
    have hU := interior_subset hv
    have he := pairRadial_root_exact_factor (v.1 0) (v.1 1) (v.1 2) (v.1 3) keepD v.2 hU.1 hroot
    have hq : ((![v.1 0,v.1 1,v.1 2,v.1 3] : PairChartParameters),v.2)=v := by
      apply Prod.ext
      · funext i; fin_cases i <;> rfl
      · rfl
    rw [hq] at he
    rw [he,abs_mul,mul_comm C]
    exact mul_le_mul_of_nonneg_left hU.2.le (abs_nonneg _)

/-- The exact ε factor also handles signed scale and mass-fraction faces.
No division by t, α, or 1−α enters this assertion. -/
theorem pairChart_zero_eps_all_scale_faces (t p alpha : ℝ) (keepD : Bool)
    (y : PairChartVariables) (hr : ∀ i, 0<pairChartRadii t alpha y i)
    (hroot : pairChartExtendedRows 0 t p alpha keepD y=0) :
    (∀ i, pairChartRadii t alpha y i=1) ∧ y 3=0 := by
  have hu : y 3=0 := by
    simpa only [zero_mul] using pairRadial_root_exact_factor 0 t p alpha keepD y hr hroot
  have hra : pairChartRadii t alpha y 0=y 2 := by simp [pairChartRadii,hu]
  have hrb : pairChartRadii t alpha y 1=y 2 := by simp [pairChartRadii,hu]
  have hmean : pairRadialMean 0 t p alpha y=0 := congrFun hroot 2
  have hg : y 2-(y 2^2)⁻¹=0 := by
    simp only [pairRadialMean,pairRadialExterior,pairInternalRadialMean,
      zero_mul,neg_zero,add_zero,hra,hrb] at hmean
    linear_combination hmean
  have hR : y 2=1 := positive_radial_zero_eq_one _ (hra ▸ hr 0) hg
  refine ⟨?_,hu⟩
  intro i
  fin_cases i
  · exact hra.trans hR
  · exact hrb.trans hR
  · apply positive_radial_zero_eq_one _ (hr 2)
    have h : radialResidual 0 (pairChartMass t p alpha) (pairChartRadii t alpha y)
        (pairChartAngles t alpha y) 2=0 := congrFun hroot 0
    simpa only [radialResidual_at_zero] using h
  · apply positive_radial_zero_eq_one _ (hr 3)
    have h : radialResidual 0 (pairChartMass t p alpha) (pairChartRadii t alpha y)
        (pairChartAngles t alpha y) 3=0 := congrFun hroot 1
    simpa only [radialResidual_at_zero] using h

end DominantFiveBody
