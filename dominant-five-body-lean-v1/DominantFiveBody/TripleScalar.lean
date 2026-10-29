import DominantFiveBody.LocalContinuation
import Mathlib.LinearAlgebra.Matrix.Gershgorin
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.Calculus.Deriv.Abs
import Mathlib.Analysis.Calculus.Deriv.MeanValue

/-! # The actual scalar three-body boundary seed

Source §5.3, equations `internal`, `internal-J`, `LB`, and `Kreg`.
Zero coefficients remain in all three divided equations, including probe rows.
Boundary existence is asserted only for collision-free limits actually
obtained by capture. Not every nonnegative weight vector admits a distinct
ordered root: a sole leftmost source makes the two right probe roots coincide.
-/

noncomputable section
open scoped BigOperators Matrix ContDiff
open Filter Set Topology

namespace DominantFiveBody
set_option maxHeartbeats 800000

abbrev TripleLabel := Fin 3
abbrev TripleVector := TripleLabel → ℝ
abbrev TripleGaps := Fin 2 → ℝ

def tripleD0 : ℝ := 9 / 4

theorem tripleD0_pos : 0 < tripleD0 := by norm_num [tripleD0]

def TripleWeights (alpha : TripleVector) : Prop :=
  (∀ i, 0 ≤ alpha i) ∧ ∑ i, alpha i = 1

def TripleOrdered (z : TripleVector) : Prop := ∀ i j, i < j → z i < z j

def tripleScalarForce (x : ℝ) : ℝ := x / |x| ^ 3

def tripleScalarResidual (alpha z : TripleVector) (i : TripleLabel) : ℝ :=
  tripleD0 * z i - ∑ j ∈ Finset.univ.erase i, alpha j * tripleScalarForce (z i - z j)

def tripleScalarJacobian (alpha z : TripleVector) : Matrix TripleLabel TripleLabel ℝ :=
  fun i j => if i = j then
    tripleD0 + 2 * ∑ k ∈ Finset.univ.erase i, alpha k / |z i - z k| ^ 3
  else -2 * alpha j / |z i - z j| ^ 3

def tripleGapMatrix : Matrix (Fin 2) TripleLabel ℝ := !![-1, 1, 0; 0, -1, 1]

def tripleCenteringMatrix (alpha : TripleVector) : Matrix TripleLabel (Fin 2) ℝ :=
  !![-(alpha 1 + alpha 2), -alpha 2;
     alpha 0, -alpha 2;
     alpha 0, alpha 0 + alpha 1]

def tripleReducedJacobian (alpha z : TripleVector) : Matrix (Fin 2) (Fin 2) ℝ :=
  tripleGapMatrix * tripleScalarJacobian alpha z * tripleCenteringMatrix alpha

theorem tripleScalarForce_hasDerivAt {x : ℝ} (hx : x ≠ 0) :
    HasDerivAt tripleScalarForce (-2 / |x| ^ 3) x := by
  rcases lt_or_gt_of_ne hx with hneg | hpos
  · have hd := (hasDerivAt_id x).div ((hasDerivAt_abs_neg hneg).pow 3)
      (pow_ne_zero 3 (abs_ne_zero.mpr hx))
    convert! hd using 1
    simp only [Pi.pow_apply, id_eq]
    rw [abs_of_neg hneg]
    field_simp
    ring
  · have hd := (hasDerivAt_id x).div ((hasDerivAt_abs_pos hpos).pow 3)
      (pow_ne_zero 3 (abs_ne_zero.mpr hx))
    convert! hd using 1
    simp only [Pi.pow_apply, id_eq]
    rw [abs_of_pos hpos]
    field_simp
    ring

theorem tripleScalarForce_contDiffAt (n : ℕ∞) {x : ℝ} (hx : x ≠ 0) :
    ContDiffAt ℝ n tripleScalarForce x := by
  unfold tripleScalarForce
  exact contDiffAt_id.div ((contDiffAt_id.abs hx).pow 3) (pow_ne_zero 3 (abs_ne_zero.mpr hx))

theorem tripleScalarForce_strictAntiOn_pos : StrictAntiOn tripleScalarForce (Ioi 0) := by
  apply strictAntiOn_of_deriv_neg (convex_Ioi 0)
  · intro x hx
    exact (tripleScalarForce_hasDerivAt (ne_of_gt hx)).continuousAt.continuousWithinAt
  · intro x hx
    rw [interior_Ioi] at hx
    rw [(tripleScalarForce_hasDerivAt (ne_of_gt hx)).deriv]
    exact div_neg_of_neg_of_pos (by norm_num) (pow_pos (abs_pos.mpr (ne_of_gt hx)) 3)

theorem tripleScalarForce_strictAntiOn_neg : StrictAntiOn tripleScalarForce (Iio 0) := by
  apply strictAntiOn_of_deriv_neg (convex_Iio 0)
  · intro x hx
    exact (tripleScalarForce_hasDerivAt (ne_of_lt hx)).continuousAt.continuousWithinAt
  · intro x hx
    rw [interior_Iio] at hx
    rw [(tripleScalarForce_hasDerivAt (ne_of_lt hx)).deriv]
    exact div_neg_of_neg_of_pos (by norm_num) (pow_pos (abs_pos.mpr (ne_of_lt hx)) 3)

def tripleScalarDifferential (alpha z : TripleVector) : TripleVector →L[ℝ] TripleVector :=
  ContinuousLinearMap.pi (fun i =>
    tripleD0 • (ContinuousLinearMap.proj i : TripleVector →L[ℝ] ℝ) +
      ∑ j ∈ Finset.univ.erase i,
        (2 * alpha j / |z i - z j| ^ 3) •
          ((ContinuousLinearMap.proj i : TripleVector →L[ℝ] ℝ) - ContinuousLinearMap.proj j))

theorem tripleScalarResidual_hasFDerivAt (alpha z : TripleVector)
    (hz : ∀ i j, i ≠ j → z i ≠ z j) :
    HasFDerivAt (fun y i => tripleScalarResidual alpha y i)
      (tripleScalarDifferential alpha z) z := by
  classical
  apply hasFDerivAt_pi.mpr
  intro i
  unfold tripleScalarResidual
  have hsum : HasFDerivAt
      (fun y : TripleVector => ∑ j ∈ Finset.univ.erase i,
        alpha j * tripleScalarForce (y i - y j))
      (∑ j ∈ Finset.univ.erase i, (alpha j * (-2 / |z i - z j| ^ 3)) •
        ((ContinuousLinearMap.proj i : TripleVector →L[ℝ] ℝ) - ContinuousLinearMap.proj j)) z := by
    apply HasFDerivAt.fun_sum
    intro j hj
    have hneq := hz i j (Ne.symm (Finset.mem_erase.mp hj).1)
    simpa only [smul_smul, Function.comp_def, Pi.sub_apply] using
      ((tripleScalarForce_hasDerivAt (sub_ne_zero.mpr hneq)).comp_hasFDerivAt z
        ((hasFDerivAt_apply (𝕜 := ℝ) i z).sub (hasFDerivAt_apply (𝕜 := ℝ) j z))).const_mul (alpha j)
  convert! ((hasFDerivAt_apply (𝕜 := ℝ) i z).const_mul tripleD0).sub hsum using 1
  ext v
  simp only [add_apply, sub_apply, smul_apply,
    ContinuousLinearMap.proj_apply, smul_eq_mul, sum_apply]
  rw [sub_eq_add_neg, ← Finset.sum_neg_distrib]
  congr 1
  apply Finset.sum_congr rfl
  intro j _
  ring

theorem tripleGapMatrix_centeringMatrix (alpha : TripleVector) (ha : ∑ i, alpha i = 1) :
    tripleGapMatrix * tripleCenteringMatrix alpha = 1 := by
  rw [Fin.sum_univ_three] at ha
  ext i j
  fin_cases i <;> fin_cases j
  all_goals simp [tripleGapMatrix, tripleCenteringMatrix, Matrix.mul_apply, Fin.sum_univ_three]
  all_goals linarith

theorem tripleCenteringMatrix_weighted_center (alpha : TripleVector) (v : TripleGaps) :
    ∑ i, alpha i * (tripleCenteringMatrix alpha *ᵥ v) i = 0 := by
  simp [tripleCenteringMatrix, Matrix.mulVec, dotProduct, Fin.sum_univ_three, Fin.sum_univ_two]
  ring

theorem tripleScalarJacobian_diag_pos (alpha z : TripleVector)
    (ha : ∀ i, 0 ≤ alpha i) (i : TripleLabel) :
    0 < tripleScalarJacobian alpha z i i := by
  simp only [tripleScalarJacobian, if_true]
  have hs : 0 ≤ ∑ k ∈ Finset.univ.erase i, alpha k / |z i - z k| ^ 3 :=
    Finset.sum_nonneg (fun k _ => div_nonneg (ha k) (by positivity))
  linarith [tripleD0_pos]

theorem tripleScalarJacobian_strict_row_dominance (alpha z : TripleVector)
    (ha : ∀ i, 0 ≤ alpha i) (i : TripleLabel) :
    (∑ j ∈ Finset.univ.erase i, ‖tripleScalarJacobian alpha z i j‖) <
      ‖tripleScalarJacobian alpha z i i‖ := by
  rw [Real.norm_eq_abs, abs_of_pos (tripleScalarJacobian_diag_pos alpha z ha i)]
  have heq : (∑ j ∈ Finset.univ.erase i, ‖tripleScalarJacobian alpha z i j‖) =
      2 * ∑ j ∈ Finset.univ.erase i, alpha j / |z i - z j| ^ 3 := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j hj
    have hij : i ≠ j := Ne.symm (Finset.mem_erase.mp hj).1
    simp only [tripleScalarJacobian, if_neg hij, Real.norm_eq_abs]
    rw [abs_of_nonpos (div_nonpos_of_nonpos_of_nonneg (by linarith [ha j]) (by positivity))]
    ring
  rw [heq]
  simp only [tripleScalarJacobian, if_true]
  linarith [tripleD0_pos]

theorem tripleScalarJacobian_det_ne_zero (alpha z : TripleVector)
    (ha : ∀ i, 0 ≤ alpha i) : (tripleScalarJacobian alpha z).det ≠ 0 :=
  det_ne_zero_of_sum_row_lt_diag (tripleScalarJacobian_strict_row_dominance alpha z ha)

theorem tripleScalarJacobian_weighted_left (alpha z v : TripleVector) :
    (∑ i, alpha i * (tripleScalarJacobian alpha z *ᵥ v) i) =
      tripleD0 * ∑ i, alpha i * v i := by
  have hab (i j : TripleLabel) : |z i - z j| ^ 3 = |z j - z i| ^ 3 := by rw [abs_sub_comm]
  simp [Matrix.mulVec, dotProduct, Fin.sum_univ_three, tripleScalarJacobian,
    Finset.sum_erase_eq_sub]
  rw [hab 1 0, hab 2 0, hab 2 1]
  ring

theorem tripleGapMatrix_kernel_constant (w : TripleVector)
    (hw : tripleGapMatrix *ᵥ w = 0) : ∀ i, w i = w 0 := by
  have h0 := congrFun hw 0
  have h1 := congrFun hw 1
  simp only [tripleGapMatrix, Matrix.mulVec, dotProduct, Fin.sum_univ_three] at h0 h1
  dsimp at h0 h1
  intro i
  fin_cases i
  all_goals dsimp only
  · rfl
  · change w 1 = w 0; linarith
  · change w 2 = w 0; linarith

theorem tripleReducedJacobian_det_ne_zero (alpha z : TripleVector) (ha : TripleWeights alpha) :
    (tripleReducedJacobian alpha z).det ≠ 0 := by
  apply IsUnit.ne_zero
  apply (Matrix.isUnit_iff_isUnit_det _).mp
  apply Matrix.mulVec_injective_iff_isUnit.mp
  intro v w heq
  have hk : ∀ x : TripleGaps, tripleReducedJacobian alpha z *ᵥ x = 0 → x = 0 := by
    intro x hx
    let bx := tripleCenteringMatrix alpha *ᵥ x
    let jbx := tripleScalarJacobian alpha z *ᵥ bx
    have hgap : tripleGapMatrix *ᵥ jbx = 0 := by
      simpa [tripleReducedJacobian, Matrix.mulVec_mulVec, Matrix.mul_assoc, bx, jbx] using hx
    have hconstant := tripleGapMatrix_kernel_constant jbx hgap
    have hcenter := tripleCenteringMatrix_weighted_center alpha x
    have hweighted := tripleScalarJacobian_weighted_left alpha z bx
    have hzero : jbx 0 = 0 := by
      have hs : (∑ i, alpha i * jbx i) = jbx 0 := by
        simp_rw [hconstant]
        rw [← Finset.sum_mul, ha.2, one_mul]
      change (∑ i, alpha i * jbx i) = tripleD0 * ∑ i, alpha i * bx i at hweighted
      change ∑ i, alpha i * bx i = 0 at hcenter
      rw [hcenter, mul_zero, hs] at hweighted
      exact hweighted
    have hjzero : jbx = 0 := funext (fun i => by rw [hconstant i, hzero]; rfl)
    have hbxzero : bx = 0 := (Matrix.mulVec_injective_of_det_ne_zero
      (tripleScalarJacobian_det_ne_zero alpha z ha.1)) (by simpa [jbx] using hjzero)
    have hidentity : tripleGapMatrix *ᵥ bx = x := by
      change tripleGapMatrix *ᵥ (tripleCenteringMatrix alpha *ᵥ x) = x
      rw [Matrix.mulVec_mulVec, tripleGapMatrix_centeringMatrix alpha ha.2, Matrix.one_mulVec]
    rw [hbxzero, Matrix.mulVec_zero] at hidentity
    exact hidentity.symm
  have hsub : tripleReducedJacobian alpha z *ᵥ (v - w) = 0 := by
    rw [Matrix.mulVec_sub, heq, sub_self]
  exact sub_eq_zero.mp (hk (v - w) hsub)

theorem tripleScalarJacobian_mulVec (alpha z v : TripleVector) :
    tripleScalarJacobian alpha z *ᵥ v = tripleScalarDifferential alpha z v := by
  funext i
  fin_cases i
  all_goals simp [tripleScalarJacobian, tripleScalarDifferential, Matrix.mulVec, dotProduct,
    Fin.sum_univ_three, Finset.sum_erase_eq_sub]
  all_goals ring

theorem tripleOrdered_distinct {z : TripleVector} (hz : TripleOrdered z) :
    ∀ i j, i ≠ j → z i ≠ z j := by
  intro i j hij
  rcases lt_or_gt_of_ne hij with hlt | hgt
  · exact ne_of_lt (hz i j hlt)
  · exact ne_of_gt (hz j i hgt)

theorem tripleScalarForce_antitone_ordered_pairs (x y : TripleVector)
    (hx : TripleOrdered x) (hy : TripleOrdered y) (i j : TripleLabel) (hij : i ≠ j)
    (harg : x i - x j ≤ y i - y j) :
    tripleScalarForce (y i - y j) ≤ tripleScalarForce (x i - x j) := by
  rcases lt_or_gt_of_ne hij with hlt | hgt
  · exact tripleScalarForce_strictAntiOn_neg.antitoneOn
      (sub_neg.mpr (hx i j hlt)) (sub_neg.mpr (hy i j hlt)) harg
  · exact tripleScalarForce_strictAntiOn_pos.antitoneOn
      (sub_pos.mpr (hx j i hgt)) (sub_pos.mpr (hy j i hgt)) harg

theorem tripleScalarResidual_max_difference (alpha x y : TripleVector)
    (ha : ∀ i, 0 ≤ alpha i) (hx : TripleOrdered x) (hy : TripleOrdered y)
    (i : TripleLabel) (hi : ∀ j, x j - y j ≤ x i - y i) :
    tripleD0 * (x i - y i) ≤ tripleScalarResidual alpha x i - tripleScalarResidual alpha y i := by
  have hs : (∑ j ∈ Finset.univ.erase i, alpha j * tripleScalarForce (x i - x j)) ≤
      ∑ j ∈ Finset.univ.erase i, alpha j * tripleScalarForce (y i - y j) := by
    apply Finset.sum_le_sum
    intro j hj
    have hforce := tripleScalarForce_antitone_ordered_pairs y x hy hx i j
      (Ne.symm (Finset.mem_erase.mp hj).1) (by linarith [hi j])
    exact mul_le_mul_of_nonneg_left hforce (ha j)
  unfold tripleScalarResidual
  linarith

/-- Source §5.3 uniqueness also at nonnegative weights. Every zero-weight
probe equation is retained; no existence is asserted at arbitrary boundary weights. -/
theorem tripleScalar_root_unique (alpha x y : TripleVector)
    (ha : ∀ i, 0 ≤ alpha i) (hx : TripleOrdered x) (hy : TripleOrdered y)
    (hxr : ∀ i, tripleScalarResidual alpha x i = 0)
    (hyr : ∀ i, tripleScalarResidual alpha y i = 0) : x = y := by
  have hle : ∀ x y : TripleVector, TripleOrdered x → TripleOrdered y →
      (∀ i, tripleScalarResidual alpha x i = 0) →
      (∀ i, tripleScalarResidual alpha y i = 0) → ∀ j, x j ≤ y j := by
    intro x y hx hy hxr hyr
    obtain ⟨i, _, hi⟩ := Finset.exists_max_image Finset.univ (fun k => x k - y k)
      Finset.univ_nonempty
    have hbound := tripleScalarResidual_max_difference alpha x y ha hx hy i
      (fun j => hi j (Finset.mem_univ j))
    rw [hxr i, hyr i, sub_self] at hbound
    have hmax : x i - y i ≤ 0 := by unfold tripleD0 at hbound; linarith
    intro j
    have h := hi j (Finset.mem_univ j)
    linarith
  funext i
  exact le_antisymm (hle x y hx hy hxr hyr i) (hle y x hy hx hyr hxr i)

theorem tripleScalarResidual_weighted_sum (alpha z : TripleVector) :
    (∑ i, alpha i * tripleScalarResidual alpha z i) = tripleD0 * ∑ i, alpha i * z i := by
  have hab (i j : TripleLabel) : |z i - z j| ^ 3 = |z j - z i| ^ 3 := by rw [abs_sub_comm]
  simp [tripleScalarResidual, tripleScalarForce, Fin.sum_univ_three, Finset.sum_erase_eq_sub]
  rw [hab 1 0, hab 2 0, hab 2 1]
  ring

theorem tripleScalar_root_weighted_center (alpha z : TripleVector)
    (hr : ∀ i, tripleScalarResidual alpha z i = 0) : ∑ i, alpha i * z i = 0 := by
  have h := tripleScalarResidual_weighted_sum alpha z
  simp_rw [hr, mul_zero, Finset.sum_const_zero] at h
  exact (mul_eq_zero.mp h.symm).resolve_left (ne_of_gt tripleD0_pos)

theorem tripleScalar_centered_gap_root_recovery (alpha : TripleVector) (v : TripleGaps)
    (ha : TripleWeights alpha)
    (hr : tripleGapMatrix *ᵥ (fun i =>
      tripleScalarResidual alpha (tripleCenteringMatrix alpha *ᵥ v) i) = 0) :
    ∀ i, tripleScalarResidual alpha (tripleCenteringMatrix alpha *ᵥ v) i = 0 := by
  let G : TripleVector := fun i => tripleScalarResidual alpha (tripleCenteringMatrix alpha *ᵥ v) i
  have hconstant := tripleGapMatrix_kernel_constant G hr
  have hweighted := tripleScalarResidual_weighted_sum alpha (tripleCenteringMatrix alpha *ᵥ v)
  rw [tripleCenteringMatrix_weighted_center, mul_zero] at hweighted
  have hsum : (∑ i, alpha i * G i) = G 0 := by
    simp_rw [hconstant]
    rw [← Finset.sum_mul, ha.2, one_mul]
  have h0 : G 0 = 0 := hsum.symm.trans hweighted
  intro i
  exact (hconstant i).trans h0

theorem tripleScalarJacobian_lower_norm_bound (alpha z v : TripleVector)
    (ha : ∀ i, 0 ≤ alpha i) :
    tripleD0 * ‖v‖ ≤ ‖tripleScalarJacobian alpha z *ᵥ v‖ := by
  let J := tripleScalarJacobian alpha z
  obtain ⟨i, hi⟩ := (IsGreatest.pi_norm v).1
  have hiv : ‖v i‖ = ‖v‖ := hi
  have hmax (j : TripleLabel) : ‖v j‖ ≤ ‖v i‖ := by
    rw [hiv]; exact norm_le_pi_norm v j
  have hrow : J i i * v i = (J *ᵥ v) i - ∑ j ∈ Finset.univ.erase i, J i j * v j := by
    have hs := Finset.sum_erase_add Finset.univ (fun j => J i j * v j) (Finset.mem_univ i)
    change _ = ∑ j, J i j * v j at hs
    change _ = (J *ᵥ v) i at hs
    linarith
  have hcoeff : (∑ j ∈ Finset.univ.erase i, ‖J i j‖) = J i i - tripleD0 := by
    have hoff : (∑ j ∈ Finset.univ.erase i, ‖J i j‖) =
        2 * ∑ j ∈ Finset.univ.erase i, alpha j / |z i - z j| ^ 3 := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j hj
      have hij : i ≠ j := Ne.symm (Finset.mem_erase.mp hj).1
      simp only [J, tripleScalarJacobian, if_neg hij, Real.norm_eq_abs]
      rw [abs_of_nonpos (div_nonpos_of_nonpos_of_nonneg (by linarith [ha j]) (by positivity))]
      ring
    rw [hoff]
    simp [J, tripleScalarJacobian]
  have hsum : ‖∑ j ∈ Finset.univ.erase i, J i j * v j‖ ≤
      (J i i - tripleD0) * ‖v i‖ := by
    calc
      _ ≤ ∑ j ∈ Finset.univ.erase i, ‖J i j * v j‖ := norm_sum_le _ _
      _ = ∑ j ∈ Finset.univ.erase i, ‖J i j‖ * ‖v j‖ := by simp_rw [norm_mul]
      _ ≤ ∑ j ∈ Finset.univ.erase i, ‖J i j‖ * ‖v i‖ :=
        Finset.sum_le_sum (fun j _ => mul_le_mul_of_nonneg_left (hmax j) (norm_nonneg _))
      _ = (J i i - tripleD0) * ‖v i‖ := by rw [← Finset.sum_mul, hcoeff]
  have hnorm : J i i * ‖v i‖ ≤ ‖J *ᵥ v‖ + (J i i - tripleD0) * ‖v i‖ := by
    calc
      _ = ‖J i i * v i‖ := by
        rw [norm_mul]
        have hdiag : ‖J i i‖ = J i i :=
          Real.norm_of_nonneg (tripleScalarJacobian_diag_pos alpha z ha i).le
        rw [hdiag]
      _ ≤ ‖(J *ᵥ v) i‖ + ‖∑ j ∈ Finset.univ.erase i, J i j * v j‖ := by
        rw [hrow]; exact norm_sub_le _ _
      _ ≤ ‖J *ᵥ v‖ + (J i i - tripleD0) * ‖v i‖ :=
        add_le_add (norm_le_pi_norm _ i) hsum
  rw [hiv] at hnorm
  nlinarith

theorem tripleScalarResidual_joint_contDiffAt (n : ℕ∞) (alpha z : TripleVector)
    (hz : ∀ i j, i ≠ j → z i ≠ z j) :
    ContDiffAt ℝ n (fun p : TripleVector × TripleVector =>
      fun i => tripleScalarResidual p.1 p.2 i) (alpha, z) := by
  classical
  apply contDiffAt_pi.mpr
  intro i
  unfold tripleScalarResidual
  apply ContDiffAt.sub (by fun_prop)
  apply ContDiffAt.sum
  intro j hj
  have hneq := hz i j (Ne.symm (Finset.mem_erase.mp hj).1)
  have hf := (tripleScalarForce_contDiffAt n (sub_ne_zero.mpr hneq)).comp (alpha, z)
    (f := fun p : TripleVector × TripleVector => p.2 i - p.2 j) (by fun_prop)
  exact (by fun_prop : ContDiffAt ℝ n (fun p : TripleVector × TripleVector => p.1 j) (alpha, z)).mul hf

/-- The boundary seed required in §5.3 is an actual distinct ordered
limit of asymptotically vanishing divided scalar residuals. Weights may vanish;
there is no arbitrary-nonnegative-weight existence assertion. -/
theorem tripleScalar_root_of_residual_limit (alphaSeq zSeq : ℕ → TripleVector)
    (alpha z : TripleVector) (hz : TripleOrdered z)
    (haLim : Tendsto alphaSeq atTop (𝓝 alpha)) (hzLim : Tendsto zSeq atTop (𝓝 z))
    (hres : ∀ i, Tendsto (fun n => tripleScalarResidual (alphaSeq n) (zSeq n) i)
      atTop (𝓝 0)) : ∀ i, tripleScalarResidual alpha z i = 0 := by
  have hc := (tripleScalarResidual_joint_contDiffAt 0 alpha z (tripleOrdered_distinct hz)).continuousAt
  have hlim := hc.tendsto.comp (by simpa only [nhds_prod_eq] using haLim.prodMk hzLim)
  intro i
  have hi := (continuous_apply i).continuousAt.tendsto.comp hlim
  exact tendsto_nhds_unique hi (hres i)

def tripleGapLinear : TripleVector →L[ℝ] TripleGaps :=
  ContinuousLinearMap.pi (fun i => ∑ j, tripleGapMatrix i j •
    (ContinuousLinearMap.proj j : TripleVector →L[ℝ] ℝ))

def tripleCenteringLinear (alpha : TripleVector) : TripleGaps →L[ℝ] TripleVector :=
  ContinuousLinearMap.pi (fun i => ∑ j, tripleCenteringMatrix alpha i j •
    (ContinuousLinearMap.proj j : TripleGaps →L[ℝ] ℝ))

@[simp] theorem tripleGapLinear_apply (v : TripleVector) :
    tripleGapLinear v = tripleGapMatrix *ᵥ v := by
  ext i; simp [tripleGapLinear, Matrix.mulVec, dotProduct]

@[simp] theorem tripleCenteringLinear_apply (alpha : TripleVector) (v : TripleGaps) :
    tripleCenteringLinear alpha v = tripleCenteringMatrix alpha *ᵥ v := by
  ext i; simp [tripleCenteringLinear, Matrix.mulVec, dotProduct]

def tripleReducedDifferential (alpha z : TripleVector) : TripleGaps →L[ℝ] TripleGaps :=
  tripleGapLinear.comp ((tripleScalarDifferential alpha z).comp (tripleCenteringLinear alpha))

theorem tripleReducedDifferential_matrix (alpha z : TripleVector) (v : TripleGaps) :
    tripleReducedDifferential alpha z v = tripleReducedJacobian alpha z *ᵥ v := by
  simp only [tripleReducedDifferential, ContinuousLinearMap.comp_apply,
    tripleCenteringLinear_apply, tripleGapLinear_apply]
  rw [← tripleScalarJacobian_mulVec]
  simp [tripleReducedJacobian, Matrix.mulVec_mulVec, Matrix.mul_assoc]

theorem tripleScalarDifferential_isInvertible (alpha z : TripleVector)
    (ha : ∀ i, 0 ≤ alpha i) : (tripleScalarDifferential alpha z).IsInvertible := by
  apply euclidean_clm_isInvertible_of_injective
  intro v w h
  apply Matrix.mulVec_injective_of_det_ne_zero (tripleScalarJacobian_det_ne_zero alpha z ha)
  simpa only [tripleScalarJacobian_mulVec] using h

theorem tripleReducedDifferential_isInvertible (alpha z : TripleVector)
    (ha : TripleWeights alpha) : (tripleReducedDifferential alpha z).IsInvertible := by
  apply euclidean_clm_isInvertible_of_injective
  intro v w h
  apply Matrix.mulVec_injective_of_det_ne_zero (tripleReducedJacobian_det_ne_zero alpha z ha)
  simpa only [tripleReducedDifferential_matrix] using h

theorem tripleScalar_root_local_implicitFunction (alpha z : TripleVector)
    (ha : ∀ i, 0 ≤ alpha i) (hz : TripleOrdered z)
    (hr : ∀ i, tripleScalarResidual alpha z i = 0) :
    ∃ psi : TripleVector → TripleVector,
      psi alpha = z ∧ ContDiffAt ℝ ∞ psi alpha ∧
      (∀ᶠ a in 𝓝 alpha, ∀ i, tripleScalarResidual a (psi a) i = 0) ∧
      (∀ᶠ p : TripleVector × TripleVector in 𝓝 (alpha, z),
        (∀ i, tripleScalarResidual p.1 p.2 i = 0) ↔ psi p.1 = p.2) := by
  let cdf := tripleScalarResidual_joint_contDiffAt (⊤ : ℕ∞) alpha z (tripleOrdered_distinct hz)
  have hpartial : (fderiv ℝ (fun p : TripleVector × TripleVector =>
      fun i => tripleScalarResidual p.1 p.2 i) (alpha, z) ∘L
      ContinuousLinearMap.inr ℝ TripleVector TripleVector).IsInvertible := by
    have hd := (cdf.differentiableAt (by simp)).hasFDerivAt.comp z
      ((hasFDerivAt_const alpha z).prodMk (hasFDerivAt_id z))
    have heq := hd.unique (tripleScalarResidual_hasFDerivAt alpha z (tripleOrdered_distinct hz))
    change (fderiv ℝ (fun p : TripleVector × TripleVector =>
      fun i => tripleScalarResidual p.1 p.2 i) (alpha, z) ∘L
      ContinuousLinearMap.inr ℝ TripleVector TripleVector) = tripleScalarDifferential alpha z at heq
    rw [heq]
    exact tripleScalarDifferential_isInvertible alpha z ha
  have hroot : (fun i => tripleScalarResidual alpha z i) = 0 := funext hr
  let psi := cdf.implicitFunction (by simp) hpartial
  refine ⟨psi, cdf.implicitFunction_apply_self (by simp) hpartial,
    cdf.contDiffAt_implicitFunction (by simp) hpartial, ?_, ?_⟩
  · have h := cdf.eventually_apply_implicitFunction (by simp) hpartial
    filter_upwards [h] with a hroota
    have hzero : (fun i => tripleScalarResidual a (psi a) i) = 0 := hroota.trans hroot
    exact fun i => congrFun hzero i
  · have h := cdf.eventually_apply_eq_iff_implicitFunction (by simp) hpartial
    filter_upwards [h] with p hp
    simpa only [hroot, funext_iff, Pi.zero_apply] using hp

end DominantFiveBody
