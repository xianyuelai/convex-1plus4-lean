import DominantFiveBody.PairRegularization

/-! # Joint smoothness of the seven genuine pair-chart rows

The open conditions allow t=0, α=0, and α=1. No relation is imposed
between ε and t. External sources remain separated from the cluster.
-/

noncomputable section
open Set Topology
open scoped BigOperators ContDiff

namespace DominantFiveBody

def PairChartRegular (eps t alpha : ℝ) (y : PairChartVariables) : Prop :=
  1+eps≠0 ∧ (∀ i, pairChartRadii t alpha y i≠0) ∧ 0<pairChartWSq t alpha y ∧
    ∀ i ∈ ({2,3} : Finset Satellite), ∀ j, i≠j → pairChartPoints t alpha y i≠pairChartPoints t alpha y j

theorem pairChartRegular_external_pair (eps t alpha : ℝ) (y : PairChartVariables)
    (hreg : PairChartRegular eps t alpha y) :
    ∀ i ∈ ({2,3} : Finset Satellite),
      pairChartPoints t alpha y i≠pairChartPoints t alpha y 0 ∧
      pairChartPoints t alpha y i≠pairChartPoints t alpha y 1 := by
  intro i hi
  have hi0 : i≠0 := by simp only [Finset.mem_insert,Finset.mem_singleton] at hi; rcases hi with rfl | rfl <;> decide
  have hi1 : i≠1 := by simp only [Finset.mem_insert,Finset.mem_singleton] at hi; rcases hi with rfl | rfl <;> decide
  exact ⟨hreg.2.2.2 i hi 0 hi0,hreg.2.2.2 i hi 1 hi1⟩

theorem pairChartDistance_joint_contDiffAt (n : ℕ∞ω) (v : PairJointVariables)
    (i j : Satellite) (hsep : pairChartPoints (v.1 1) (v.1 3) v.2 i≠
      pairChartPoints (v.1 1) (v.1 3) v.2 j) :
    ContDiffAt ℝ n (fun w : PairJointVariables =>
      satelliteDistance (pairChartPoints (w.1 1) (w.1 3) w.2) i j) v :=
  ((pairChartPoints_joint_contDiff n i).sub (pairChartPoints_joint_contDiff n j)).contDiffAt.norm ℝ
    (sub_ne_zero.mpr hsep)

theorem pairPhysicalRadialExterior_joint_contDiffAt (n : ℕ∞ω) (v : PairJointVariables)
    (hreg : PairChartRegular (v.1 0) (v.1 1) (v.1 3) v.2)
    (i : Satellite) (hi : i∈({2,3} : Finset Satellite)) :
    ContDiffAt ℝ n (fun w : PairJointVariables =>
      radialResidual (w.1 0) (pairChartMass (w.1 1) (w.1 2) (w.1 3))
        (pairChartRadii (w.1 1) (w.1 3) w.2) (pairChartAngles (w.1 1) (w.1 3) w.2) i) v := by
  have hr (j : Satellite) := (pairChartRadii_joint_contDiff n j).contDiffAt (x := v)
  have htheta (j : Satellite) := (pairChartAngles_joint_contDiff n j).contDiffAt (x := v)
  have hmu (j : Satellite) := (pairChartMass_joint_contDiff n j).contDiffAt (x := v)
  have heps : ContDiffAt ℝ n (fun w : PairJointVariables => w.1 0) v := by fun_prop
  have hsum : ContDiffAt ℝ n (fun w : PairJointVariables =>
      ∑ j ∈ Finset.univ.erase i, pairChartMass (w.1 1) (w.1 2) (w.1 3) j*
        (pairChartRadii (w.1 1) (w.1 3) w.2 i-pairChartRadii (w.1 1) (w.1 3) w.2 j*
          Real.cos (pairChartAngles (w.1 1) (w.1 3) w.2 j-pairChartAngles (w.1 1) (w.1 3) w.2 i))/
        satelliteDistance (pairChartPoints (w.1 1) (w.1 3) w.2) i j^3) v := by
    apply ContDiffAt.sum
    intro j hj
    have hneq := hreg.2.2.2 i hi j (Ne.symm (Finset.mem_erase.mp hj).1)
    exact ((hmu j).mul ((hr i).sub ((hr j).mul (((htheta j).sub (htheta i)).cos)))).div
      ((pairChartDistance_joint_contDiffAt n v i j hneq).pow 3)
      (pow_ne_zero 3 (norm_ne_zero_iff.mpr (sub_ne_zero.mpr hneq)))
  have hg := (hr i).sub (((hr i).pow 2).inv (pow_ne_zero 2 (hreg.2.1 i)))
  exact (hg.sub (heps.mul hsum)).sub
    ((heps.div (contDiffAt_const.add heps) hreg.1).mul
      ((pairAverage_joint_contDiff n).contDiffAt.inner ℝ (pairUnit_joint_contDiff n i).contDiffAt))

theorem pairPhysicalAngularExterior_joint_contDiffAt (n : ℕ∞ω) (v : PairJointVariables)
    (hreg : PairChartRegular (v.1 0) (v.1 1) (v.1 3) v.2)
    (i : Satellite) (hi : i∈({2,3} : Finset Satellite)) :
    ContDiffAt ℝ n (fun w : PairJointVariables =>
      angularResidual (w.1 0) (pairChartMass (w.1 1) (w.1 2) (w.1 3))
        (pairChartRadii (w.1 1) (w.1 3) w.2) (pairChartAngles (w.1 1) (w.1 3) w.2) i) v := by
  have hr (j : Satellite) := (pairChartRadii_joint_contDiff n j).contDiffAt (x := v)
  have htheta (j : Satellite) := (pairChartAngles_joint_contDiff n j).contDiffAt (x := v)
  have hmu (j : Satellite) := (pairChartMass_joint_contDiff n j).contDiffAt (x := v)
  have hc : ContDiffAt ℝ n (fun w : PairJointVariables => (1+w.1 0)⁻¹) v := by
    exact (contDiffAt_const.add (by fun_prop)).inv hreg.1
  unfold angularResidual
  apply ContDiffAt.sum
  intro j hj
  have hneq := hreg.2.2.2 i hi j (Ne.symm (Finset.mem_erase.mp hj).1)
  exact ((((hmu j).mul (hr i)).mul (hr j)).mul (((htheta j).sub (htheta i)).sin)).mul
    ((((pairChartDistance_joint_contDiffAt n v i j hneq).pow 3).inv
      (pow_ne_zero 3 (norm_ne_zero_iff.mpr (sub_ne_zero.mpr hneq)))).sub hc)

theorem pairRadialExterior_joint_contDiffAt (n : ℕ∞ω) (v : PairJointVariables)
    (hreg : PairChartRegular (v.1 0) (v.1 1) (v.1 3) v.2)
    (i : Satellite) (hi : i=0 ∨ i=1) :
    ContDiffAt ℝ n (fun w : PairJointVariables =>
      pairRadialExterior (w.1 0) (w.1 1) (w.1 2) (w.1 3) w.2 i) v := by
  have hr := (pairChartRadii_joint_contDiff n i).contDiffAt (x := v)
  have heps : ContDiffAt ℝ n (fun w : PairJointVariables => w.1 0) v := by fun_prop
  have hsep : ∀ j ∈ ({2,3} : Finset Satellite),
      pairChartPoints (v.1 1) (v.1 3) v.2 j≠pairChartPoints (v.1 1) (v.1 3) v.2 i := by
    intro j hj
    have h := pairChartRegular_external_pair _ _ _ _ hreg j hj
    rcases hi with rfl | rfl
    · exact h.1
    · exact h.2
  exact (hr.sub ((hr.pow 2).inv (pow_ne_zero 2 (hreg.2.1 i)))).add
    (heps.mul ((pairExteriorRadialField_joint_contDiffAt n v i hreg.1 hsep).inner ℝ
      (pairUnit_joint_contDiff n i).contDiffAt))

theorem pairAngularExterior_joint_contDiffAt (n : ℕ∞ω) (v : PairJointVariables)
    (hreg : PairChartRegular (v.1 0) (v.1 1) (v.1 3) v.2)
    (i : Satellite) (hi : i=0 ∨ i=1) :
    ContDiffAt ℝ n (fun w : PairJointVariables =>
      pairAngularExterior (w.1 0) (w.1 1) (w.1 2) (w.1 3) w.2 i) v := by
  have hsep : ∀ j ∈ ({2,3} : Finset Satellite),
      pairChartPoints (v.1 1) (v.1 3) v.2 j≠pairChartPoints (v.1 1) (v.1 3) v.2 i := by
    intro j hj
    have h := pairChartRegular_external_pair _ _ _ _ hreg j hj
    rcases hi with rfl | rfl
    · exact h.1
    · exact h.2
  have hq : ContDiff ℝ n (fun w : PairJointVariables =>
      quarterTurn (pairChartPoints (w.1 1) (w.1 3) w.2 i)) :=
    quarterTurnLinear.toContinuousLinearMap.contDiff.comp (pairChartPoints_joint_contDiff n i)
  exact (pairExteriorAngularField_joint_contDiffAt n v i hreg.1 hsep).inner ℝ hq.contDiffAt

theorem pairRadialMean_joint_contDiffAt (n : ℕ∞ω) (v : PairJointVariables)
    (hreg : PairChartRegular (v.1 0) (v.1 1) (v.1 3) v.2) :
    ContDiffAt ℝ n (fun w : PairJointVariables =>
      pairRadialMean (w.1 0) (w.1 1) (w.1 2) (w.1 3) w.2) v := by
  have ha : ContDiffAt ℝ n (fun w : PairJointVariables => w.1 3) v := by fun_prop
  exact ((ha.mul (pairRadialExterior_joint_contDiffAt n v hreg 0 (Or.inl rfl))).add
    ((contDiffAt_const.sub ha).mul (pairRadialExterior_joint_contDiffAt n v hreg 1 (Or.inr rfl)))).add
      (pairInternalRadialMean_joint_contDiffAt n v hreg.2.2.1)

theorem pairAngularMean_joint_contDiffAt (n : ℕ∞ω) (v : PairJointVariables)
    (hreg : PairChartRegular (v.1 0) (v.1 1) (v.1 3) v.2) :
    ContDiffAt ℝ n (fun w : PairJointVariables =>
      pairAngularMean (w.1 0) (w.1 1) (w.1 2) (w.1 3) w.2) v := by
  have ha : ContDiffAt ℝ n (fun w : PairJointVariables => w.1 3) v := by fun_prop
  exact (ha.mul (pairAngularExterior_joint_contDiffAt n v hreg 0 (Or.inl rfl))).add
    ((contDiffAt_const.sub ha).mul (pairAngularExterior_joint_contDiffAt n v hreg 1 (Or.inr rfl)))

theorem pairRadialDifference_joint_contDiffAt (n : ℕ∞ω) (v : PairJointVariables)
    (hreg : PairChartRegular (v.1 0) (v.1 1) (v.1 3) v.2) :
    ContDiffAt ℝ n (fun w : PairJointVariables =>
      pairRadialDifference (w.1 0) (w.1 1) (w.1 2) (w.1 3) w.2) v := by
  have hsep := pairChartRegular_external_pair _ _ _ _ hreg
  have hra := (pairChartRadii_joint_contDiff n 0).contDiffAt (x := v)
  have hrb := (pairChartRadii_joint_contDiff n 1).contDiffAt (x := v)
  have hu : ContDiffAt ℝ n (fun w : PairJointVariables => w.2 3) v := by fun_prop
  have heps : ContDiffAt ℝ n (fun w : PairJointVariables => w.1 0) v := by fun_prop
  have hg : ContDiffAt ℝ n (fun w : PairJointVariables =>
      w.2 3*(1+(pairChartRadii (w.1 1) (w.1 3) w.2 0+pairChartRadii (w.1 1) (w.1 3) w.2 1)/
        (pairChartRadii (w.1 1) (w.1 3) w.2 0^2*pairChartRadii (w.1 1) (w.1 3) w.2 1^2))) v :=
    hu.mul (contDiffAt_const.add ((hra.add hrb).div ((hra.pow 2).mul (hrb.pow 2))
      (mul_ne_zero (pow_ne_zero 2 (hreg.2.1 0)) (pow_ne_zero 2 (hreg.2.1 1)))))
  have hd := pairExteriorNewtonDifference_joint_contDiffAt n v hsep
  have hfield := pairExteriorRadialField_joint_contDiffAt n v 0 hreg.1 (fun j hj => (hsep j hj).1)
  exact (hg.add (heps.mul ((hd.inner ℝ (pairUnit_joint_contDiff n 1).contDiffAt).add
    (hfield.inner ℝ (pairUnitDirection_joint_contDiff n).contDiffAt)))).add
      (pairInternalRadialDifference_joint_contDiffAt n v hreg.2.2.1)

theorem pairAngularDifference_joint_contDiffAt (n : ℕ∞ω) (v : PairJointVariables)
    (hreg : PairChartRegular (v.1 0) (v.1 1) (v.1 3) v.2) :
    ContDiffAt ℝ n (fun w : PairJointVariables =>
      pairAngularDifference (w.1 0) (w.1 1) (w.1 2) (w.1 3) w.2) v := by
  have hsep := pairChartRegular_external_pair _ _ _ _ hreg
  have hd := pairExteriorNewtonDifference_joint_contDiffAt n v hsep
  have hfield := pairExteriorAngularField_joint_contDiffAt n v 0 hreg.1 (fun j hj => (hsep j hj).1)
  have hq : ContDiff ℝ n (fun w : PairJointVariables =>
      quarterTurn (pairChartPoints (w.1 1) (w.1 3) w.2 1)) :=
    quarterTurnLinear.toContinuousLinearMap.contDiff.comp (pairChartPoints_joint_contDiff n 1)
  have hv : ContDiff ℝ n (fun w : PairJointVariables =>
      quarterTurn (pairPointDirection (w.1 1) (w.1 3) w.2)) :=
    quarterTurnLinear.toContinuousLinearMap.contDiff.comp (pairPointDirection_joint_contDiff n)
  exact ((hd.inner ℝ hq.contDiffAt).add (hfield.inner ℝ hv.contDiffAt)).add
    (pairInternalAngularDifference_joint_contDiffAt n v hreg.2.2.1 hreg.1)

/-- The complete seven-row extension is jointly C∞ on an independent open
parameter domain, including the zero scale and both fraction endpoints. -/
theorem pairChartExtendedRows_joint_contDiffAt (n : ℕ∞ω) (v : PairJointVariables)
    (hreg : PairChartRegular (v.1 0) (v.1 1) (v.1 3) v.2) (keepD : Bool) :
    ContDiffAt ℝ n (fun w : PairJointVariables =>
      pairChartExtendedRows (w.1 0) (w.1 1) (w.1 2) (w.1 3) keepD w.2) v := by
  apply contDiffAt_pi.mpr
  intro i
  fin_cases i
  · exact pairPhysicalRadialExterior_joint_contDiffAt n v hreg 2 (by simp)
  · exact pairPhysicalRadialExterior_joint_contDiffAt n v hreg 3 (by simp)
  · exact pairRadialMean_joint_contDiffAt n v hreg
  · exact pairRadialDifference_joint_contDiffAt n v hreg
  · exact pairPhysicalAngularExterior_joint_contDiffAt n v hreg (if keepD then 3 else 2) (by cases keepD <;> simp)
  · exact pairAngularMean_joint_contDiffAt n v hreg
  · exact pairAngularDifference_joint_contDiffAt n v hreg

theorem pairChartRegular_isOpen : IsOpen {v : PairJointVariables |
    PairChartRegular (v.1 0) (v.1 1) (v.1 3) v.2} := by
  have hden : IsOpen {v : PairJointVariables | 1+v.1 0≠0} :=
    (isClosed_eq (by fun_prop) continuous_const).isOpen_compl
  have hr : IsOpen {v : PairJointVariables | ∀ i, pairChartRadii (v.1 1) (v.1 3) v.2 i≠0} := by
    simp only [Set.ofPred_forall]
    apply isOpen_iInter_of_finite
    intro i
    exact (isClosed_eq (pairChartRadii_joint_contDiff 0 i).continuous continuous_const).isOpen_compl
  have hW : IsOpen {v : PairJointVariables | 0<pairChartWSq (v.1 1) (v.1 3) v.2} :=
    isOpen_lt continuous_const (pairChartWSq_joint_contDiff 0).continuous
  have hs : IsOpen {v : PairJointVariables | ∀ i ∈ ({2,3} : Finset Satellite), ∀ j, i≠j →
      pairChartPoints (v.1 1) (v.1 3) v.2 i≠pairChartPoints (v.1 1) (v.1 3) v.2 j} := by
    simp only [Set.ofPred_forall]
    apply isOpen_iInter_of_finite
    intro i
    apply isOpen_iInter_of_finite
    intro _
    apply isOpen_iInter_of_finite
    intro j
    apply isOpen_iInter_of_finite
    intro _
    exact (isClosed_eq (pairChartPoints_joint_contDiff 0 i).continuous
      (pairChartPoints_joint_contDiff 0 j).continuous).isOpen_compl
  exact hden.inter (hr.inter (hW.inter hs))

theorem pairChartExtendedRows_joint_contDiffOn (n : ℕ∞ω) (keepD : Bool) :
    ContDiffOn ℝ n (fun w : PairJointVariables =>
      pairChartExtendedRows (w.1 0) (w.1 1) (w.1 2) (w.1 3) keepD w.2)
      {v | PairChartRegular (v.1 0) (v.1 1) (v.1 3) v.2} := by
  intro v hv
  exact (pairChartExtendedRows_joint_contDiffAt n v hv keepD).contDiffWithinAt

end DominantFiveBody
