import DominantFiveBody.TripleRegularization

/-! # Joint smoothness on the independent regular-triple domain

The open domain includes zero t and zero α coordinates. It imposes
only nonzero physical radius denominators, positive rescaled cluster
distances, and actual exterior separation; no ε/t condition is used.
-/

noncomputable section
open Set Topology
open scoped BigOperators ContDiff

namespace DominantFiveBody
set_option maxHeartbeats 800000

def TripleChartRegular (eps t : ℝ) (alpha : TripleVector) (y : TripleChartVariables) : Prop :=
  1 + eps ≠ 0 ∧ (∀ i, tripleChartRadii t alpha y i ≠ 0) ∧
    (∀ i j, i ≠ j → 0 < tripleChartWSq t alpha y i j) ∧
    ∀ i : TripleLabel, tripleChartPoints t alpha y 3 ≠ tripleChartPoints t alpha y i.castSucc

theorem tripleAverage_joint_contDiff (n : ℕ∞ω) :
    ContDiff ℝ n (fun v : TripleJointVariables =>
      relativeAverage (tripleChartMass (v.1 1) (tripleJointAlpha v.1))
        (tripleChartPoints (v.1 1) (tripleJointAlpha v.1) v.2)) := by
  unfold relativeAverage
  apply ContDiff.sum
  intro i _
  exact (tripleChartMass_joint_contDiff n i).smul (tripleChartPoints_joint_contDiff n i)

theorem tripleChartDistance_joint_contDiffAt (n : ℕ∞ω) (v : TripleJointVariables)
    (i j : Satellite) (hsep : tripleChartPoints (v.1 1) (tripleJointAlpha v.1) v.2 i ≠
      tripleChartPoints (v.1 1) (tripleJointAlpha v.1) v.2 j) :
    ContDiffAt ℝ n (fun w : TripleJointVariables =>
      satelliteDistance (tripleChartPoints (w.1 1) (tripleJointAlpha w.1) w.2) i j) v :=
  ((tripleChartPoints_joint_contDiff n i).sub (tripleChartPoints_joint_contDiff n j)).contDiffAt.norm ℝ
    (sub_ne_zero.mpr hsep)

theorem tripleExteriorNewtonField_joint_contDiffAt (n : ℕ∞ω) (v : TripleJointVariables)
    (i : TripleLabel) (hsep : tripleChartPoints (v.1 1) (tripleJointAlpha v.1) v.2 3 ≠
      tripleChartPoints (v.1 1) (tripleJointAlpha v.1) v.2 i.castSucc) :
    ContDiffAt ℝ n (fun w : TripleJointVariables =>
      tripleExteriorNewtonField (w.1 1) (tripleJointAlpha w.1) w.2
        (tripleChartPoints (w.1 1) (tripleJointAlpha w.1) w.2 i.castSucc)) v := by
  have hf := (newtonTargetField_joint_contDiffAt n
    (tripleChartPoints (v.1 1) (tripleJointAlpha v.1) v.2 3,
      tripleChartPoints (v.1 1) (tripleJointAlpha v.1) v.2 i.castSucc) hsep).comp v
    (((tripleChartPoints_joint_contDiff n 3).prodMk
      (tripleChartPoints_joint_contDiff n i.castSucc)).contDiffAt)
  exact (tripleChartMass_joint_contDiff n 3).contDiffAt.smul hf

theorem tripleExteriorNewtonDifference_joint_contDiffAt (n : ℕ∞ω) (v : TripleJointVariables)
    (i j : TripleLabel)
    (hi : tripleChartPoints (v.1 1) (tripleJointAlpha v.1) v.2 3 ≠
      tripleChartPoints (v.1 1) (tripleJointAlpha v.1) v.2 i.castSucc)
    (hj : tripleChartPoints (v.1 1) (tripleJointAlpha v.1) v.2 3 ≠
      tripleChartPoints (v.1 1) (tripleJointAlpha v.1) v.2 j.castSucc) :
    ContDiffAt ℝ n (fun w : TripleJointVariables =>
      tripleExteriorNewtonDifference (w.1 1) (tripleJointAlpha w.1) w.2 i j) v := by
  have hf := (dividedNewtonTargetField_joint_contDiffAt n
    ((tripleChartPoints (v.1 1) (tripleJointAlpha v.1) v.2 3,
       tripleChartPoints (v.1 1) (tripleJointAlpha v.1) v.2 i.castSucc),
      (tripleChartPoints (v.1 1) (tripleJointAlpha v.1) v.2 j.castSucc,
       triplePointDirection (v.1 1) (tripleJointAlpha v.1) v.2 i j)) hi hj).comp v
    ((((tripleChartPoints_joint_contDiff n 3).prodMk (tripleChartPoints_joint_contDiff n i.castSucc)).prodMk
      ((tripleChartPoints_joint_contDiff n j.castSucc).prodMk
        (triplePointDirection_joint_contDiff n i j))).contDiffAt)
  exact (tripleChartMass_joint_contDiff n 3).contDiffAt.smul hf

theorem tripleExteriorRadialField_joint_contDiffAt (n : ℕ∞ω) (v : TripleJointVariables)
    (i : TripleLabel) (heps : 1 + v.1 0 ≠ 0)
    (hsep : tripleChartPoints (v.1 1) (tripleJointAlpha v.1) v.2 3 ≠
      tripleChartPoints (v.1 1) (tripleJointAlpha v.1) v.2 i.castSucc) :
    ContDiffAt ℝ n (fun w : TripleJointVariables =>
      tripleExteriorRadialField (w.1 0) (w.1 1) (tripleJointAlpha w.1) w.2
        (tripleChartPoints (w.1 1) (tripleJointAlpha w.1) w.2 i.castSucc)) v := by
  have hc : ContDiffAt ℝ n (fun w : TripleJointVariables => (1 + w.1 0)⁻¹) v := by fun_prop
  exact (tripleExteriorNewtonField_joint_contDiffAt n v i hsep).sub
    (hc.smul (tripleAverage_joint_contDiff n).contDiffAt)

theorem tripleExteriorAngularField_joint_contDiffAt (n : ℕ∞ω) (v : TripleJointVariables)
    (i : TripleLabel) (heps : 1 + v.1 0 ≠ 0)
    (hsep : tripleChartPoints (v.1 1) (tripleJointAlpha v.1) v.2 3 ≠
      tripleChartPoints (v.1 1) (tripleJointAlpha v.1) v.2 i.castSucc) :
    ContDiffAt ℝ n (fun w : TripleJointVariables =>
      tripleExteriorAngularField (w.1 0) (w.1 1) (tripleJointAlpha w.1) w.2
        (tripleChartPoints (w.1 1) (tripleJointAlpha w.1) w.2 i.castSucc)) v := by
  have hc : ContDiffAt ℝ n (fun w : TripleJointVariables => (1 + w.1 0)⁻¹) v := by fun_prop
  exact (tripleExteriorNewtonField_joint_contDiffAt n v i hsep).sub
    (hc.smul ((tripleChartMass_joint_contDiff n 3).smul (tripleChartPoints_joint_contDiff n 3)).contDiffAt)

theorem tripleRadialExterior_joint_contDiffAt (n : ℕ∞ω) (v : TripleJointVariables)
    (hreg : TripleChartRegular (v.1 0) (v.1 1) (tripleJointAlpha v.1) v.2) (i : TripleLabel) :
    ContDiffAt ℝ n (fun w : TripleJointVariables =>
      tripleRadialExterior (w.1 0) (w.1 1) (tripleJointAlpha w.1) w.2 i) v := by
  have hr := (tripleChartRadii_joint_contDiff n i.castSucc).contDiffAt (x := v)
  exact (hr.sub ((hr.pow 2).inv (pow_ne_zero 2 (hreg.2.1 i.castSucc)))).add
    ((by fun_prop : ContDiffAt ℝ n (fun w : TripleJointVariables => w.1 0) v).mul
      ((tripleExteriorRadialField_joint_contDiffAt n v i hreg.1 (hreg.2.2.2 i)).inner ℝ
        (tripleUnit_joint_contDiff n i.castSucc).contDiffAt))

theorem tripleAngularExterior_joint_contDiffAt (n : ℕ∞ω) (v : TripleJointVariables)
    (hreg : TripleChartRegular (v.1 0) (v.1 1) (tripleJointAlpha v.1) v.2) (i : TripleLabel) :
    ContDiffAt ℝ n (fun w : TripleJointVariables =>
      tripleAngularExterior (w.1 0) (w.1 1) (tripleJointAlpha w.1) w.2 i) v :=
  (tripleExteriorAngularField_joint_contDiffAt n v i hreg.1 (hreg.2.2.2 i)).inner ℝ
    (quarterTurnLinear.toContinuousLinearMap.contDiff.comp (tripleChartPoints_joint_contDiff n i.castSucc)).contDiffAt

theorem tripleRadialMean_joint_contDiffAt (n : ℕ∞ω) (v : TripleJointVariables)
    (hreg : TripleChartRegular (v.1 0) (v.1 1) (tripleJointAlpha v.1) v.2) :
    ContDiffAt ℝ n (fun w : TripleJointVariables =>
      tripleRadialMean (w.1 0) (w.1 1) (tripleJointAlpha w.1) w.2) v := by
  unfold tripleRadialMean tripleInternalRadialMean
  apply ContDiffAt.add
  · apply ContDiffAt.sum
    intro i _
    exact (tripleJointAlpha_contDiff n i).contDiffAt.mul (tripleRadialExterior_joint_contDiffAt n v hreg i)
  · apply ContDiffAt.sum
    intro i _
    exact (tripleJointAlpha_contDiff n i).contDiffAt.mul
      (tripleInternalRadial_joint_contDiffAt n v i (fun j hj => hreg.2.2.1 i j hj.symm))

theorem tripleAngularMean_joint_contDiffAt (n : ℕ∞ω) (v : TripleJointVariables)
    (hreg : TripleChartRegular (v.1 0) (v.1 1) (tripleJointAlpha v.1) v.2) :
    ContDiffAt ℝ n (fun w : TripleJointVariables =>
      tripleAngularMean (w.1 0) (w.1 1) (tripleJointAlpha w.1) w.2) v := by
  unfold tripleAngularMean tripleInternalAngularMean
  apply ContDiffAt.add
  · apply ContDiffAt.sum
    intro i _
    exact (tripleJointAlpha_contDiff n i).contDiffAt.mul (tripleAngularExterior_joint_contDiffAt n v hreg i)
  · apply ContDiffAt.sum
    intro i _
    exact (tripleJointAlpha_contDiff n i).contDiffAt.mul
      (tripleInternalAngular_joint_contDiffAt n v i hreg.1 (fun j hj => hreg.2.2.1 i j hj.symm))

theorem tripleRadialExteriorDifference_joint_contDiffAt (n : ℕ∞ω) (v : TripleJointVariables)
    (hreg : TripleChartRegular (v.1 0) (v.1 1) (tripleJointAlpha v.1) v.2) (i j : TripleLabel) :
    ContDiffAt ℝ n (fun w : TripleJointVariables =>
      tripleRadialExteriorDifference (w.1 0) (w.1 1) (tripleJointAlpha w.1) w.2 i j) v := by
  have hri := (tripleChartRadii_joint_contDiff n i.castSucc).contDiffAt (x := v)
  have hrj := (tripleChartRadii_joint_contDiff n j.castSucc).contDiffAt (x := v)
  have hw := ((tripleChartRadialPositions_joint_contDiff n j).sub
    (tripleChartRadialPositions_joint_contDiff n i)).contDiffAt (x := v)
  have hconst : ContDiffAt ℝ n (fun _ : TripleJointVariables => (1 : ℝ)) v := contDiffAt_const
  have hg := hw.mul (hconst.add ((hri.add hrj).div ((hri.pow 2).mul (hrj.pow 2))
    (mul_ne_zero (pow_ne_zero 2 (hreg.2.1 i.castSucc)) (pow_ne_zero 2 (hreg.2.1 j.castSucc)))))
  have hd := tripleExteriorNewtonDifference_joint_contDiffAt n v i j (hreg.2.2.2 i) (hreg.2.2.2 j)
  exact hg.add ((by fun_prop : ContDiffAt ℝ n (fun w : TripleJointVariables => w.1 0) v).mul
    ((hd.inner ℝ (tripleUnit_joint_contDiff n j.castSucc).contDiffAt).add
      ((tripleExteriorRadialField_joint_contDiffAt n v i hreg.1 (hreg.2.2.2 i)).inner ℝ
        (tripleUnitDirection_joint_contDiff n i j).contDiffAt)))

theorem tripleAngularExteriorDifference_joint_contDiffAt (n : ℕ∞ω) (v : TripleJointVariables)
    (hreg : TripleChartRegular (v.1 0) (v.1 1) (tripleJointAlpha v.1) v.2) (i j : TripleLabel) :
    ContDiffAt ℝ n (fun w : TripleJointVariables =>
      tripleAngularExteriorDifference (w.1 0) (w.1 1) (tripleJointAlpha w.1) w.2 i j) v :=
  ((tripleExteriorNewtonDifference_joint_contDiffAt n v i j (hreg.2.2.2 i) (hreg.2.2.2 j)).inner ℝ
    (quarterTurnLinear.toContinuousLinearMap.contDiff.comp (tripleChartPoints_joint_contDiff n j.castSucc)).contDiffAt).add
    ((tripleExteriorAngularField_joint_contDiffAt n v i hreg.1 (hreg.2.2.2 i)).inner ℝ
      (quarterTurnLinear.toContinuousLinearMap.contDiff.comp (triplePointDirection_joint_contDiff n i j)).contDiffAt)

theorem tripleRadialDifference_joint_contDiffAt (n : ℕ∞ω) (v : TripleJointVariables)
    (hreg : TripleChartRegular (v.1 0) (v.1 1) (tripleJointAlpha v.1) v.2) (k : Fin 2) :
    ContDiffAt ℝ n (fun w : TripleJointVariables =>
      tripleRadialDifference (w.1 0) (w.1 1) (tripleJointAlpha w.1) w.2 k) v := by
  unfold tripleRadialDifference
  apply (tripleRadialExteriorDifference_joint_contDiffAt n v hreg k.castSucc k.succ).add
  simp only [tripleInternalRadialDifference, tripleGapMatrix_mulVec_entry]
  exact (tripleInternalRadialReduced_joint_contDiffAt n v k.succ
    (fun j hj => hreg.2.2.1 _ j hj.symm)).sub
    (tripleInternalRadialReduced_joint_contDiffAt n v k.castSucc (fun j hj => hreg.2.2.1 _ j hj.symm))

theorem tripleAngularDifference_joint_contDiffAt (n : ℕ∞ω) (v : TripleJointVariables)
    (hreg : TripleChartRegular (v.1 0) (v.1 1) (tripleJointAlpha v.1) v.2) (k : Fin 2) :
    ContDiffAt ℝ n (fun w : TripleJointVariables =>
      tripleAngularDifference (w.1 0) (w.1 1) (tripleJointAlpha w.1) w.2 k) v := by
  unfold tripleAngularDifference
  apply (tripleAngularExteriorDifference_joint_contDiffAt n v hreg k.castSucc k.succ).add
  simp only [tripleInternalAngularDifference, tripleGapMatrix_mulVec_entry]
  exact (tripleInternalAngularReduced_joint_contDiffAt n v k.succ hreg.1
    (fun j hj => hreg.2.2.1 _ j hj.symm)).sub
    (tripleInternalAngularReduced_joint_contDiffAt n v k.castSucc hreg.1
      (fun j hj => hreg.2.2.1 _ j hj.symm))

theorem tripleChartRegular_exterior_distinct (eps t : ℝ) (alpha : TripleVector)
    (y : TripleChartVariables) (hreg : TripleChartRegular eps t alpha y)
    (j : Satellite) (hj : j ≠ 3) : tripleChartPoints t alpha y 3 ≠ tripleChartPoints t alpha y j := by
  fin_cases j
  · exact hreg.2.2.2 0
  · exact hreg.2.2.2 1
  · exact hreg.2.2.2 2
  · exact False.elim (hj rfl)

theorem triplePhysicalRadialExterior_joint_contDiffAt (n : ℕ∞ω) (v : TripleJointVariables)
    (hreg : TripleChartRegular (v.1 0) (v.1 1) (tripleJointAlpha v.1) v.2) :
    ContDiffAt ℝ n (fun w : TripleJointVariables =>
      radialResidual (w.1 0) (tripleChartMass (w.1 1) (tripleJointAlpha w.1))
        (tripleChartRadii (w.1 1) (tripleJointAlpha w.1) w.2)
        (tripleChartAngles (w.1 1) (tripleJointAlpha w.1) w.2) 3) v := by
  have hr (j : Satellite) := (tripleChartRadii_joint_contDiff n j).contDiffAt (x := v)
  have htheta (j : Satellite) := (tripleChartAngles_joint_contDiff n j).contDiffAt (x := v)
  have hmu (j : Satellite) := (tripleChartMass_joint_contDiff n j).contDiffAt (x := v)
  have heps : ContDiffAt ℝ n (fun w : TripleJointVariables => w.1 0) v := by fun_prop
  have hsum : ContDiffAt ℝ n (fun w : TripleJointVariables =>
      ∑ j ∈ Finset.univ.erase 3, tripleChartMass (w.1 1) (tripleJointAlpha w.1) j *
        (tripleChartRadii (w.1 1) (tripleJointAlpha w.1) w.2 3 -
          tripleChartRadii (w.1 1) (tripleJointAlpha w.1) w.2 j *
          Real.cos (tripleChartAngles (w.1 1) (tripleJointAlpha w.1) w.2 j -
            tripleChartAngles (w.1 1) (tripleJointAlpha w.1) w.2 3)) /
        satelliteDistance (tripleChartPoints (w.1 1) (tripleJointAlpha w.1) w.2) 3 j ^ 3) v := by
    apply ContDiffAt.sum
    intro j hj
    have hneq := tripleChartRegular_exterior_distinct _ _ _ _ hreg j (Finset.mem_erase.mp hj).1
    exact ((hmu j).mul ((hr 3).sub ((hr j).mul (((htheta j).sub (htheta 3)).cos)))).div
      ((tripleChartDistance_joint_contDiffAt n v 3 j hneq).pow 3)
      (pow_ne_zero 3 (norm_ne_zero_iff.mpr (sub_ne_zero.mpr hneq)))
  exact (((hr 3).sub (((hr 3).pow 2).inv (pow_ne_zero 2 (hreg.2.1 3)))).sub
    (heps.mul hsum)).sub ((heps.div (contDiffAt_const.add heps) hreg.1).mul
      ((tripleAverage_joint_contDiff n).contDiffAt.inner ℝ (tripleUnit_joint_contDiff n 3).contDiffAt))

/-- Every row is jointly C∞ in the independent source parameters and all
seven unknowns, including zero scale and zero-weight endpoints. -/
theorem tripleChartExtendedRows_joint_contDiffAt (n : ℕ∞ω) (v : TripleJointVariables)
    (hreg : TripleChartRegular (v.1 0) (v.1 1) (tripleJointAlpha v.1) v.2) :
    ContDiffAt ℝ n (fun w : TripleJointVariables =>
      tripleChartExtendedRows (w.1 0) (w.1 1) (tripleJointAlpha w.1) w.2) v := by
  apply contDiffAt_pi.mpr
  intro i
  fin_cases i
  · exact triplePhysicalRadialExterior_joint_contDiffAt n v hreg
  · exact tripleRadialMean_joint_contDiffAt n v hreg
  · exact tripleRadialDifference_joint_contDiffAt n v hreg 0
  · exact tripleRadialDifference_joint_contDiffAt n v hreg 1
  · exact tripleAngularMean_joint_contDiffAt n v hreg
  · exact tripleAngularDifference_joint_contDiffAt n v hreg 0
  · exact tripleAngularDifference_joint_contDiffAt n v hreg 1

theorem tripleChartRegular_isOpen : IsOpen {v : TripleJointVariables |
    TripleChartRegular (v.1 0) (v.1 1) (tripleJointAlpha v.1) v.2} := by
  have heps : IsOpen {v : TripleJointVariables | 1 + v.1 0 ≠ 0} :=
    (isClosed_eq (by fun_prop) continuous_const).isOpen_compl
  have hr : IsOpen {v : TripleJointVariables | ∀ i,
      tripleChartRadii (v.1 1) (tripleJointAlpha v.1) v.2 i ≠ 0} := by
    simp only [Set.ofPred_forall]
    apply isOpen_iInter_of_finite
    intro i
    exact (isClosed_eq (tripleChartRadii_joint_contDiff 0 i).continuous continuous_const).isOpen_compl
  have hW : IsOpen {v : TripleJointVariables | ∀ i j, i ≠ j →
      0 < tripleChartWSq (v.1 1) (tripleJointAlpha v.1) v.2 i j} := by
    simp only [Set.ofPred_forall]
    apply isOpen_iInter_of_finite
    intro i
    apply isOpen_iInter_of_finite
    intro j
    apply isOpen_iInter_of_finite
    intro _
    exact isOpen_lt continuous_const (tripleChartWSq_joint_contDiff 0 i j).continuous
  have hs : IsOpen {v : TripleJointVariables | ∀ i : TripleLabel,
      tripleChartPoints (v.1 1) (tripleJointAlpha v.1) v.2 3 ≠
        tripleChartPoints (v.1 1) (tripleJointAlpha v.1) v.2 i.castSucc} := by
    simp only [Set.ofPred_forall]
    apply isOpen_iInter_of_finite
    intro i
    exact (isClosed_eq (tripleChartPoints_joint_contDiff 0 3).continuous
      (tripleChartPoints_joint_contDiff 0 i.castSucc).continuous).isOpen_compl
  exact heps.inter (hr.inter (hW.inter hs))

theorem tripleChartExtendedRows_joint_contDiffOn (n : ℕ∞ω) :
    ContDiffOn ℝ n (fun w : TripleJointVariables =>
      tripleChartExtendedRows (w.1 0) (w.1 1) (tripleJointAlpha w.1) w.2)
      {v | TripleChartRegular (v.1 0) (v.1 1) (tripleJointAlpha v.1) v.2} := by
  intro v hv
  exact (tripleChartExtendedRows_joint_contDiffAt n v hv).contDiffWithinAt

end DominantFiveBody
