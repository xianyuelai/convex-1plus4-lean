import DominantFiveBody.TripleBoundary

/-! # The actual regular-triple boundary Jacobian

All derivatives are of the seven-row extension. The radial block is
`3I₄`; the remaining diagonal blocks are D₀ and the proved `LJBα`.
-/

noncomputable section
open scoped BigOperators Matrix ContDiff
open Filter Set Topology

namespace DominantFiveBody
open Coorbital
set_option maxHeartbeats 800000

def tripleChartJacobian (eps t : ℝ) (alpha : TripleVector) (y : TripleChartVariables) :
    TripleChartVariables →L[ℝ] TripleChartVariables :=
  fderiv ℝ (tripleChartExtendedRows eps t alpha) y

theorem tripleChartExtendedRows_hasFDerivAt (eps t : ℝ) (alpha : TripleVector)
    (y : TripleChartVariables) (hreg : TripleChartRegular eps t alpha y) :
    HasFDerivAt (tripleChartExtendedRows eps t alpha) (tripleChartJacobian eps t alpha y) y := by
  let p : Fin 5 → ℝ := ![eps, t, alpha 0, alpha 1, alpha 2]
  have hp : tripleJointAlpha p = alpha := by ext i; fin_cases i <;> rfl
  have hc : ContDiff ℝ 1 (fun w : TripleChartVariables => (p, w)) := contDiff_const.prodMk contDiff_id
  have hregp : TripleChartRegular (p 0) (p 1) (tripleJointAlpha p) y := by
    simpa only [hp, show p 0 = eps from rfl, show p 1 = t from rfl] using hreg
  have hd := (tripleChartExtendedRows_joint_contDiffAt 1 (p, y) hregp).comp y hc.contDiffAt
  have hf : ContDiffAt ℝ 1 (tripleChartExtendedRows eps t alpha) y := by
    simpa only [Function.comp_def, hp, show p 0 = eps from rfl, show p 1 = t from rfl] using hd
  exact (hf.differentiableAt (by norm_num)).hasFDerivAt

theorem tripleChartJacobian_apply_of_hasDerivAt (eps t : ℝ) (alpha : TripleVector)
    (y v : TripleChartVariables) (hreg : TripleChartRegular eps t alpha y)
    (i : Fin 7) (a : ℝ)
    (ha : HasDerivAt (fun s : ℝ => tripleChartExtendedRows eps t alpha (y + s • v) i) a 0) :
    tripleChartJacobian eps t alpha y v i = a := by
  have hp : HasDerivAt (fun s : ℝ => y + s • v) v 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const v).const_add y
  have hf : HasFDerivAt (tripleChartExtendedRows eps t alpha)
      (tripleChartJacobian eps t alpha y) (y + (0 : ℝ) • v) := by
    simpa using tripleChartExtendedRows_hasFDerivAt eps t alpha y hreg
  have hd := hf.comp_hasDerivAt 0 hp
  have hi := (ContinuousLinearMap.proj i : TripleChartVariables →L[ℝ] ℝ).hasFDerivAt.comp_hasDerivAt 0 hd
  exact hi.unique ha

theorem tripleChart_boundary_radial (alpha : TripleVector) (ha : ∑ i, alpha i = 1)
    (y : TripleChartVariables) (i : Fin 2) :
    tripleChartExtendedRows 0 0 alpha y i.castSucc.castSucc.castSucc.castSucc.castSucc =
      y i.castSucc.castSucc.castSucc.castSucc.castSucc -
        (y i.castSucc.castSucc.castSucc.castSucc.castSucc ^ 2)⁻¹ := by
  fin_cases i
  · simp [tripleChartExtendedRows, radialResidual, tripleChartRadii]
  · exact tripleRadialMean_at_boundary alpha y ha

theorem tripleChartJacobian_unit_radial (alpha : TripleVector) (ha : ∑ i, alpha i = 1)
    (psi : ℝ) (g : TripleGaps) (hreg : TripleChartRegular 0 0 alpha (tripleUnitPoint psi g))
    (v : TripleChartVariables) (i : Fin 2) :
    tripleChartJacobian 0 0 alpha (tripleUnitPoint psi g) v
      i.castSucc.castSucc.castSucc.castSucc.castSucc =
        3 * v i.castSucc.castSucc.castSucc.castSucc.castSucc := by
  let j : Fin 7 := i.castSucc.castSucc.castSucc.castSucc.castSucc
  have hy : tripleUnitPoint psi g j = 1 := by fin_cases i <;> simp [j, tripleUnitPoint]
  apply tripleChartJacobian_apply_of_hasDerivAt _ _ _ _ _ hreg
  have hL : HasDerivAt (fun s : ℝ => (tripleUnitPoint psi g + s • v) j) (v j) 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).mul_const (v j)).const_add (tripleUnitPoint psi g j)
  have hn : (tripleUnitPoint psi g + (0 : ℝ) • v) j ^ 2 ≠ 0 := by simp [hy]
  have hd := hL.sub ((hasDerivAt_inv hn).comp 0 (hL.pow 2))
  convert! hd using 1
  · funext s
    exact tripleChart_boundary_radial alpha ha _ i
  · simp [hy]
    ring

theorem tripleChartJacobian_unit_radial_difference (alpha : TripleVector)
    (ha : ∑ i, alpha i = 1) (psi : ℝ) (g : TripleGaps)
    (hreg : TripleChartRegular 0 0 alpha (tripleUnitPoint psi g))
    (v : TripleChartVariables) (k : Fin 2) :
    tripleChartJacobian 0 0 alpha (tripleUnitPoint psi g) v
      k.castSucc.castSucc.castSucc.succ.succ =
        3 * v k.castSucc.castSucc.castSucc.succ.succ := by
  let j : Fin 7 := k.castSucc.castSucc.castSucc.succ.succ
  have hR : HasDerivAt (fun s : ℝ => (tripleUnitPoint psi g + s • v) 1) (v 1) 0 := by
    simpa [tripleUnitPoint] using ((hasDerivAt_id (0 : ℝ)).mul_const (v 1)).const_add 1
  have hu : HasDerivAt (fun s : ℝ => tripleChartRadialGaps (tripleUnitPoint psi g + s • v) k) (v j) 0 := by
    fin_cases k <;> simpa [tripleChartRadialGaps, tripleUnitPoint, j] using
      ((hasDerivAt_id (0 : ℝ)).mul_const (v j))
  have hn : (tripleUnitPoint psi g + (0 : ℝ) • v) 1 ^ 2 *
      (tripleUnitPoint psi g + (0 : ℝ) • v) 1 ^ 2 ≠ 0 := by
    simp [tripleUnitPoint]
  have hd := hu.mul ((hasDerivAt_const (0 : ℝ) 1).add
    ((hR.const_mul 2).div ((hR.pow 2).mul (hR.pow 2)) hn))
  apply tripleChartJacobian_apply_of_hasDerivAt _ _ _ _ _ hreg
  convert! hd using 1
  · funext s
    fin_cases k <;> exact tripleRadialDifference_at_boundary alpha _ ha _
  · fin_cases k <;> simp [tripleUnitPoint, tripleChartRadialGaps, j] <;> ring

theorem tripleAngularDifference_unit_boundary (alpha : TripleVector)
    (psi : ℝ) (g : TripleGaps) (hpsi : psi ≠ 0) (hpi : |psi| < Real.pi) (k : Fin 2) :
    tripleAngularDifference 0 0 alpha (tripleUnitPoint psi g) k =
      kappa |psi| * ((tripleCenteringMatrix alpha *ᵥ g) k.succ -
        (tripleCenteringMatrix alpha *ᵥ g) k.castSucc) +
      tripleInternalAngularReduced 0 0 alpha (tripleUnitPoint psi g) k.succ -
      tripleInternalAngularReduced 0 0 alpha (tripleUnitPoint psi g) k.castSucc := by
  have hsep : polarPoint 1 0 ≠ polarPoint 1 psi :=
    polarUnit_ne_of_angle_ne 0 psi hpsi.symm (by simpa using hpi)
  unfold tripleAngularDifference
  rw [tripleAngularExteriorDifference_at_boundary alpha _ _ _ hsep,
    tripleUnitPoint_radialPositions, tripleUnitPoint_angularPositions,
    tripleInternalAngularDifference, tripleGapMatrix_mulVec_entry]
  simp only [Pi.zero_apply, sub_self]
  change (fderiv ℝ (twoSourcePolarAngular 1 1 1 0) (1, psi))
    (0, (tripleCenteringMatrix alpha *ᵥ g) k.succ - (tripleCenteringMatrix alpha *ᵥ g) k.castSucc) + _ = _
  have hv : ((0 : ℝ), (tripleCenteringMatrix alpha *ᵥ g) k.succ -
      (tripleCenteringMatrix alpha *ᵥ g) k.castSucc) =
      ((tripleCenteringMatrix alpha *ᵥ g) k.succ - (tripleCenteringMatrix alpha *ᵥ g) k.castSucc) •
        ((0 : ℝ), 1) := by ext <;> simp
  rw [hv, map_smul, twoSourcePolarAngular_unit_partial 1 0 psi hpsi hpsi hpi (by simpa using hpi)]
  simp only [one_mul, sub_self, zero_mul, add_zero, smul_eq_mul]
  ring

theorem tripleAngularDifference_unit_scalar (alpha : TripleVector) (psi : ℝ)
    (g : TripleGaps) (hpsi : psi ≠ 0) (hpi : |psi| < Real.pi)
    (hD : kappa |psi| = tripleD0) :
    tripleAngularDifference 0 0 alpha (tripleUnitPoint psi g) =
      tripleGapMatrix *ᵥ (fun i => tripleScalarResidual alpha (tripleCenteringMatrix alpha *ᵥ g) i) := by
  ext k
  rw [tripleAngularDifference_unit_boundary alpha psi g hpsi hpi k,
    tripleInternalAngularReduced_unit_boundary, tripleInternalAngularReduced_unit_boundary,
    tripleGapMatrix_mulVec_entry, hD]
  unfold tripleScalarResidual
  ring

theorem tripleUnitPoint_line (psi s : ℝ) (g : TripleGaps) (v : TripleChartVariables)
    (hv0 : v 0 = 0) (hv1 : v 1 = 0) (hv2 : v 2 = 0) (hv3 : v 3 = 0) :
    tripleUnitPoint psi g + s • v = tripleUnitPoint (psi + s * v 4)
      (g + s • ![v 5, v 6]) := by
  ext i
  fin_cases i <;> simp [tripleUnitPoint, hv0, hv1, hv2, hv3]

theorem tripleChartJacobian_unit_mean (alpha : TripleVector) (ha : ∑ i, alpha i = 1)
    (psi : ℝ) (g : TripleGaps) (hreg : TripleChartRegular 0 0 alpha (tripleUnitPoint psi g))
    (hpsi : psi ≠ 0) (hpi : |psi| < Real.pi) (v : TripleChartVariables)
    (hv0 : v 0 = 0) (hv1 : v 1 = 0) (hv2 : v 2 = 0) (hv3 : v 3 = 0) :
    tripleChartJacobian 0 0 alpha (tripleUnitPoint psi g) v 4 = kappa |psi| * v 4 := by
  apply tripleChartJacobian_apply_of_hasDerivAt _ _ _ _ _ hreg
  have hshift : HasDerivAt (fun s : ℝ => psi + s * v 4) (v 4) 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).mul_const (v 4)).const_add psi
  have hd := (twoSourcePolarAngular_unit_hasDerivAt 1 0 psi hpsi hpsi hpi
    (by simpa using hpi)).comp_of_eq 0 hshift (by simp)
  convert! hd using 1
  · funext s
    rw [tripleUnitPoint_line _ _ _ _ hv0 hv1 hv2 hv3]
    exact tripleAngularMean_at_boundary alpha _ ha
  · simp

theorem tripleReducedResidual_hasFDerivAt (alpha : TripleVector) (g : TripleGaps)
    (hdist : ∀ i j, i ≠ j → (tripleCenteringMatrix alpha *ᵥ g) i ≠
      (tripleCenteringMatrix alpha *ᵥ g) j) :
    HasFDerivAt (fun v : TripleGaps => tripleGapMatrix *ᵥ
      (fun i => tripleScalarResidual alpha (tripleCenteringMatrix alpha *ᵥ v) i))
      (tripleReducedDifferential alpha (tripleCenteringMatrix alpha *ᵥ g)) g := by
  have hG := (tripleScalarResidual_hasFDerivAt alpha (tripleCenteringMatrix alpha *ᵥ g) hdist).comp g
    (tripleCenteringLinear alpha).hasFDerivAt
  convert! tripleGapLinear.hasFDerivAt.comp g hG using 1

theorem tripleChartExtendedRows_angularDifference (eps t : ℝ) (alpha : TripleVector)
    (y : TripleChartVariables) (k : Fin 2) :
    tripleChartExtendedRows eps t alpha y k.succ.succ.succ.succ.succ =
      tripleAngularDifference eps t alpha y k := by fin_cases k <;> rfl

theorem tripleChartJacobian_unit_difference (alpha : TripleVector) (psi : ℝ)
    (g : TripleGaps) (hreg : TripleChartRegular 0 0 alpha (tripleUnitPoint psi g))
    (hpsi : psi ≠ 0) (hpi : |psi| < Real.pi) (hD : kappa |psi| = tripleD0)
    (hdist : ∀ i j, i ≠ j → (tripleCenteringMatrix alpha *ᵥ g) i ≠
      (tripleCenteringMatrix alpha *ᵥ g) j) (v : TripleChartVariables)
    (hv0 : v 0 = 0) (hv1 : v 1 = 0) (hv2 : v 2 = 0) (hv3 : v 3 = 0) (hv4 : v 4 = 0)
    (k : Fin 2) :
    tripleChartJacobian 0 0 alpha (tripleUnitPoint psi g) v k.succ.succ.succ.succ.succ =
      tripleReducedDifferential alpha (tripleCenteringMatrix alpha *ᵥ g) ![v 5, v 6] k := by
  let vg : TripleGaps := ![v 5, v 6]
  have hp : HasDerivAt (fun s : ℝ => g + s • vg) vg 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const vg).const_add g
  have hf : HasFDerivAt (fun q : TripleGaps => tripleGapMatrix *ᵥ
      (fun i => tripleScalarResidual alpha (tripleCenteringMatrix alpha *ᵥ q) i))
      (tripleReducedDifferential alpha (tripleCenteringMatrix alpha *ᵥ g)) (g + (0 : ℝ) • vg) := by
    simpa using tripleReducedResidual_hasFDerivAt alpha g hdist
  have hd := hf.comp_hasDerivAt 0 hp
  have hi := (ContinuousLinearMap.proj k : TripleGaps →L[ℝ] ℝ).hasFDerivAt.comp_hasDerivAt 0 hd
  apply tripleChartJacobian_apply_of_hasDerivAt _ _ _ _ _ hreg
  convert! hi using 1
  funext s
  rw [tripleUnitPoint_line _ _ _ _ hv0 hv1 hv2 hv3]
  simp only [hv4, mul_zero, add_zero]
  rw [tripleChartExtendedRows_angularDifference]
  change tripleAngularDifference 0 0 alpha (tripleUnitPoint psi (g + s • vg)) k = _
  rw [tripleAngularDifference_unit_scalar alpha psi (g + s • vg) hpsi hpi hD]
  rfl

theorem tripleBoundaryAngle_facts (psi : ℝ) (hangle : |psi| = h) :
    psi ≠ 0 ∧ |psi| < Real.pi ∧ coorbitalKernel psi = 0 ∧ kappa |psi| = tripleD0 := by
  have hh : 0 < h := by unfold h; positivity
  have hp : h < Real.pi := by unfold h; linarith [Real.pi_pos]
  have hzero : coorbitalKernel h = 0 := by
    rw [coorbitalKernel_eq_positive_formula _ hh.le, kernelF_h]
  have hcases : psi = h ∨ psi = -h :=
    abs_eq_abs.mp (hangle.trans (abs_of_pos hh).symm)
  refine ⟨?_, by rwa [hangle], ?_, ?_⟩
  · intro hpsi
    rw [hpsi, abs_zero] at hangle
    linarith
  · rcases hcases with rfl | rfl
    · exact hzero
    · rw [coorbitalKernel_neg, hzero, neg_zero]
  · rw [hangle, kappa_h]
    rfl

/-- The actual boundary seven-row derivative is invertible. Zero weights
are allowed; distinct scaled positions are the only cluster separation input. -/
theorem tripleChartJacobian_boundary_isInvertible (alpha : TripleVector)
    (ha : TripleWeights alpha) (psi : ℝ) (hangle : |psi| = h) (g : TripleGaps)
    (hdist : ∀ i j, i ≠ j → (tripleCenteringMatrix alpha *ᵥ g) i ≠
      (tripleCenteringMatrix alpha *ᵥ g) j) :
    (tripleChartJacobian 0 0 alpha (tripleUnitPoint psi g)).IsInvertible := by
  obtain ⟨hpsi, hpi, _, hD⟩ := tripleBoundaryAngle_facts psi hangle
  have hreg := tripleUnitPoint_regular alpha psi g hpsi hpi hdist
  apply euclidean_clm_isInvertible_of_injective
  apply (LinearMap.ker_eq_bot).mp
  apply LinearMap.ker_eq_bot'.mpr
  intro v hv
  change tripleChartJacobian 0 0 alpha (tripleUnitPoint psi g) v = 0 at hv
  have hv0 : v 0 = 0 := by
    have he := tripleChartJacobian_unit_radial alpha ha.2 psi g hreg v 0
    rw [hv] at he
    change 0 = 3 * v 0 at he
    linarith
  have hv1 : v 1 = 0 := by
    have he := tripleChartJacobian_unit_radial alpha ha.2 psi g hreg v 1
    rw [hv] at he
    change 0 = 3 * v 1 at he
    linarith
  have hv2 : v 2 = 0 := by
    have he := tripleChartJacobian_unit_radial_difference alpha ha.2 psi g hreg v 0
    rw [hv] at he
    change 0 = 3 * v 2 at he
    linarith
  have hv3 : v 3 = 0 := by
    have he := tripleChartJacobian_unit_radial_difference alpha ha.2 psi g hreg v 1
    rw [hv] at he
    change 0 = 3 * v 3 at he
    linarith
  have hv4 : v 4 = 0 := by
    have he := tripleChartJacobian_unit_mean alpha ha.2 psi g hreg hpsi hpi v hv0 hv1 hv2 hv3
    rw [hv, hD] at he
    exact (mul_eq_zero.mp he.symm).resolve_left (ne_of_gt tripleD0_pos)
  have hgap : tripleReducedJacobian alpha (tripleCenteringMatrix alpha *ᵥ g) *ᵥ ![v 5, v 6] = 0 := by
    ext k
    have he := tripleChartJacobian_unit_difference alpha psi g hreg hpsi hpi hD hdist v
      hv0 hv1 hv2 hv3 hv4 k
    rw [hv, tripleReducedDifferential_matrix] at he
    exact he.symm
  have hvg : (![v 5, v 6] : TripleGaps) = 0 := by
    apply Matrix.mulVec_injective_of_det_ne_zero
      (tripleReducedJacobian_det_ne_zero alpha (tripleCenteringMatrix alpha *ᵥ g) ha)
    simpa only [Matrix.mulVec_zero] using hgap
  have hv5 : v 5 = 0 := congrFun hvg 0
  have hv6 : v 6 = 0 := congrFun hvg 1
  ext i
  fin_cases i <;> assumption

theorem tripleChartExtendedRows_unit_root (alpha : TripleVector) (ha : ∑ i, alpha i = 1)
    (psi : ℝ) (hangle : |psi| = h) (g : TripleGaps)
    (hroot : ∀ i, tripleScalarResidual alpha (tripleCenteringMatrix alpha *ᵥ g) i = 0) :
    tripleChartExtendedRows 0 0 alpha (tripleUnitPoint psi g) = 0 := by
  obtain ⟨hpsi, hpi, hkernel, hD⟩ := tripleBoundaryAngle_facts psi hangle
  have hzero : (fun i => tripleScalarResidual alpha (tripleCenteringMatrix alpha *ᵥ g) i) = 0 :=
    funext hroot
  ext i
  fin_cases i
  · simp [tripleChartExtendedRows, radialResidual, tripleChartRadii, tripleUnitPoint]
  · change tripleRadialMean 0 0 alpha (tripleUnitPoint psi g) = 0
    rw [tripleRadialMean_at_boundary alpha _ ha]
    norm_num [tripleUnitPoint]
  · change tripleRadialDifference 0 0 alpha (tripleUnitPoint psi g) 0 = 0
    rw [tripleRadialDifference_at_boundary alpha _ ha]
    simp [tripleChartRadialGaps, tripleUnitPoint]
  · change tripleRadialDifference 0 0 alpha (tripleUnitPoint psi g) 1 = 0
    rw [tripleRadialDifference_at_boundary alpha _ ha]
    simp [tripleChartRadialGaps, tripleUnitPoint]
  · change tripleAngularMean 0 0 alpha (tripleUnitPoint psi g) = 0
    rw [tripleAngularMean_at_boundary alpha _ ha]
    change twoSourcePolarAngular 1 1 1 0 (1, psi) = 0
    rw [twoSourcePolarAngular_unit 1 0 psi hpsi hpsi hpi (by simpa using hpi)]
    simp [hkernel]
  · change tripleAngularDifference 0 0 alpha (tripleUnitPoint psi g) 0 = 0
    rw [tripleAngularDifference_unit_scalar alpha psi g hpsi hpi hD]
    rw [hzero, Matrix.mulVec_zero]
    rfl
  · change tripleAngularDifference 0 0 alpha (tripleUnitPoint psi g) 1 = 0
    rw [tripleAngularDifference_unit_scalar alpha psi g hpsi hpi hD]
    rw [hzero, Matrix.mulVec_zero]
    rfl

end DominantFiveBody
