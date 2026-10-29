import DominantFiveBody.TripleScalar
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv

/-! # The explicit slow spectrum of the equilateral background

Source §6.1, `eq:bg-matrix` and `eq:slow`.  All formulas use a signed
open epsilon neighborhood, so zero epsilon is an interior parameter.
-/

noncomputable section
open scoped Matrix ContDiff

namespace DominantFiveBody

def backgroundDelta (eps : ℝ) : ℝ := 1 - 3 * eps / (1 + eps) ^ 2
def backgroundSlowD (eps : ℝ) : ℝ :=
  9 / (2 * (1 + eps) ^ 2 * (1 + Real.sqrt (backgroundDelta eps)))
def backgroundSlowLambda (eps : ℝ) : ℝ := eps * backgroundSlowD eps
def backgroundMatrix (eps tau : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![3 / (1 + eps) * (1 + eps / 4), 3 / (1 + eps) * (tau * Real.sqrt 3 * eps / 4);
     3 / (1 + eps) * (tau * Real.sqrt 3 * eps / 4), 3 / (1 + eps) * (3 * eps / 4)]
def backgroundSlowK (eps tau : ℝ) : ℝ :=
  -backgroundMatrix eps tau 0 1 /
    (backgroundMatrix eps tau 0 0 - backgroundSlowLambda eps)
def backgroundRadius (eps : ℝ) : ℝ := Real.rpow (1 + eps) (1 / 3)
def backgroundSlowLength (eps : ℝ) : ℝ :=
  Real.rpow (tripleD0 / backgroundSlowD eps) (1 / 3)
def backgroundAngularScale (eps tau : ℝ) : ℝ :=
  backgroundSlowLength eps /
    (backgroundRadius eps * Real.sqrt (1 + backgroundSlowK eps tau ^ 2))

theorem backgroundDelta_pos (eps : ℝ) (he : 1 + eps ≠ 0) :
    0 < backgroundDelta eps := by
  have hp : 0 < (1 + eps) ^ 2 := sq_pos_of_ne_zero he
  have hnum : 0 < (1 + eps) ^ 2 - 3 * eps := by
    nlinarith [sq_nonneg (eps - 1 / 2)]
  have heq : backgroundDelta eps = ((1 + eps) ^ 2 - 3 * eps) / (1 + eps) ^ 2 := by
    unfold backgroundDelta
    field_simp
  rw [heq]
  exact div_pos hnum hp

theorem backgroundSlowD_pos (eps : ℝ) (he : 1 + eps ≠ 0) :
    0 < backgroundSlowD eps := by
  unfold backgroundSlowD
  exact div_pos (by norm_num) (mul_pos
    (mul_pos (by norm_num) (sq_pos_of_ne_zero he))
    (by positivity))

@[simp] theorem backgroundSlowD_zero : backgroundSlowD 0 = tripleD0 := by
  norm_num [backgroundSlowD, backgroundDelta, tripleD0]

@[simp] theorem backgroundSlowLambda_zero : backgroundSlowLambda 0 = 0 := by
  simp [backgroundSlowLambda]

theorem backgroundSlowLambda_eq (eps : ℝ) (he : 1 + eps ≠ 0) :
    backgroundSlowLambda eps = 3 / 2 * (1 - Real.sqrt (backgroundDelta eps)) := by
  have hsq := Real.sq_sqrt (backgroundDelta_pos eps he).le
  have hdelta : (1 + eps) ^ 2 * backgroundDelta eps = (1 + eps) ^ 2 - 3 * eps := by
    unfold backgroundDelta
    field_simp
  have hroot : (1 + eps) ^ 2 * Real.sqrt (backgroundDelta eps) ^ 2 =
      (1 + eps) ^ 2 - 3 * eps := by rw [hsq, hdelta]
  have hs : 1 + Real.sqrt (backgroundDelta eps) ≠ 0 := by positivity
  unfold backgroundSlowLambda backgroundSlowD
  field_simp
  nlinarith

theorem backgroundMatrix_trace (eps tau : ℝ) (he : 1 + eps ≠ 0) :
    Matrix.trace (backgroundMatrix eps tau) = 3 := by
  simp [Matrix.trace, backgroundMatrix, Fin.sum_univ_two]
  field_simp
  ring

theorem backgroundMatrix_det (eps tau : ℝ) (he : 1 + eps ≠ 0)
    (ht : tau ^ 2 = 1) :
    (backgroundMatrix eps tau).det = 27 * eps / (4 * (1 + eps) ^ 2) := by
  rw [Matrix.det_fin_two]
  simp only [backgroundMatrix, Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_fin_one]
  have hs : Real.sqrt 3 ^ 2 = (3 : ℝ) := Real.sq_sqrt (by norm_num)
  field_simp
  ring_nf
  rw [ht, hs]
  ring

theorem backgroundSlowLambda_characteristic (eps : ℝ) (he : 1 + eps ≠ 0) :
    backgroundSlowLambda eps ^ 2 - 3 * backgroundSlowLambda eps +
      27 * eps / (4 * (1 + eps) ^ 2) = 0 := by
  rw [backgroundSlowLambda_eq eps he]
  have hs := Real.sq_sqrt (backgroundDelta_pos eps he).le
  have hdelta : (1 + eps) ^ 2 * backgroundDelta eps = (1 + eps) ^ 2 - 3 * eps := by
    unfold backgroundDelta
    field_simp
  have hroot : (1 + eps) ^ 2 * Real.sqrt (backgroundDelta eps) ^ 2 =
      (1 + eps) ^ 2 - 3 * eps := by rw [hs, hdelta]
  field_simp
  nlinarith

theorem backgroundMatrix_characteristic_factor (eps tau x : ℝ) (he : 1 + eps ≠ 0)
    (ht : tau ^ 2 = 1) :
    (x • (1 : Matrix (Fin 2) (Fin 2) ℝ) - backgroundMatrix eps tau).det =
      (x - backgroundSlowLambda eps) * (x - (3 - backgroundSlowLambda eps)) := by
  have hdet := backgroundMatrix_det eps tau he ht
  rw [Matrix.det_fin_two] at hdet
  have htrace : backgroundMatrix eps tau 0 0 + backgroundMatrix eps tau 1 1 = 3 := by
    simpa [Matrix.trace, Fin.sum_univ_two] using backgroundMatrix_trace eps tau he
  have hchar := backgroundSlowLambda_characteristic eps he
  rw [Matrix.det_fin_two]
  norm_num [Matrix.sub_apply, Matrix.smul_apply, Matrix.one_apply]
  nlinarith [congrArg (fun y => x * y) htrace]

/-- The two roots of the actual characteristic polynomial are strictly
ordered; this makes the displayed branch the smaller eigenvalue. -/
theorem backgroundSlowLambda_lt_fast (eps : ℝ) (he : 1 + eps ≠ 0) :
    backgroundSlowLambda eps < 3 - backgroundSlowLambda eps := by
  rw [backgroundSlowLambda_eq eps he]
  have hs := Real.sqrt_pos.mpr (backgroundDelta_pos eps he)
  linarith

theorem backgroundSmall_one_add_pos (eps : ℝ) (he : |eps| < 1 / 4) :
    0 < 1 + eps := by
  have := (abs_lt.mp he).1
  linarith

theorem backgroundSlow_denominator_pos (eps tau : ℝ) (he : |eps| < 1 / 4) :
    0 < backgroundMatrix eps tau 0 0 - backgroundSlowLambda eps := by
  have hp := backgroundSmall_one_add_pos eps he
  have htop : 2 < backgroundMatrix eps tau 0 0 := by
    change 2 < 3 / (1 + eps) * (1 + eps / 4)
    rw [div_mul_eq_mul_div, lt_div_iff₀ hp]
    have := (abs_lt.mp he).2
    linarith
  have hslow : backgroundSlowLambda eps ≤ 3 / 2 := by
    rw [backgroundSlowLambda_eq eps (ne_of_gt hp)]
    nlinarith [Real.sqrt_nonneg (backgroundDelta eps)]
  linarith

theorem backgroundSlowK_eigenvector (eps tau : ℝ) (he : |eps| < 1 / 4)
    (ht : tau ^ 2 = 1) :
    backgroundMatrix eps tau *ᵥ ![backgroundSlowK eps tau, 1] =
      backgroundSlowLambda eps • ![backgroundSlowK eps tau, 1] := by
  have hn := ne_of_gt (backgroundSlow_denominator_pos eps tau he)
  have htr := backgroundMatrix_trace eps tau
    (ne_of_gt (backgroundSmall_one_add_pos eps he))
  have hdet := backgroundMatrix_det eps tau
    (ne_of_gt (backgroundSmall_one_add_pos eps he)) ht
  have hchar := backgroundSlowLambda_characteristic eps
    (ne_of_gt (backgroundSmall_one_add_pos eps he))
  rw [Matrix.det_fin_two] at hdet
  have hsym : backgroundMatrix eps tau 1 0 = backgroundMatrix eps tau 0 1 := rfl
  rw [hsym] at hdet
  have htrace : backgroundMatrix eps tau 0 0 + backgroundMatrix eps tau 1 1 = 3 := by
    simpa [Matrix.trace, Fin.sum_univ_two] using htr
  ext i
  fin_cases i
  · simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two]
    change backgroundMatrix eps tau 0 0 * backgroundSlowK eps tau +
      backgroundMatrix eps tau 0 1 = backgroundSlowLambda eps * backgroundSlowK eps tau
    unfold backgroundSlowK
    field_simp
    ring
  · simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two]
    change backgroundMatrix eps tau 1 0 * backgroundSlowK eps tau +
      backgroundMatrix eps tau 1 1 = backgroundSlowLambda eps
    unfold backgroundSlowK
    rw [hsym]
    field_simp
    nlinarith [congrArg (fun x => backgroundSlowLambda eps * x) htrace]

@[simp] theorem backgroundSlowK_zero (tau : ℝ) : backgroundSlowK 0 tau = 0 := by
  simp [backgroundSlowK, backgroundMatrix]

@[simp] theorem backgroundRadius_zero : backgroundRadius 0 = 1 := by
  simp [backgroundRadius]

@[simp] theorem backgroundSlowLength_zero : backgroundSlowLength 0 = 1 := by
  simp [backgroundSlowLength, ne_of_gt tripleD0_pos]

@[simp] theorem backgroundAngularScale_zero (tau : ℝ) : backgroundAngularScale 0 tau = 1 := by
  simp [backgroundAngularScale]

theorem backgroundRadius_pos (eps : ℝ) (he : 0 < 1 + eps) :
    0 < backgroundRadius eps := Real.rpow_pos_of_pos he _

theorem backgroundRadius_cube (eps : ℝ) (he : 0 ≤ 1 + eps) :
    backgroundRadius eps ^ 3 = 1 + eps := by
  simpa [backgroundRadius, one_div] using
    Real.rpow_inv_natCast_pow he (by decide : (3 : ℕ) ≠ 0)

theorem backgroundSlowLength_pos (eps : ℝ) (he : 1 + eps ≠ 0) :
    0 < backgroundSlowLength eps :=
  Real.rpow_pos_of_pos (div_pos tripleD0_pos (backgroundSlowD_pos eps he)) _

theorem backgroundSlowLength_cube (eps : ℝ) (he : 1 + eps ≠ 0) :
    backgroundSlowLength eps ^ 3 = tripleD0 / backgroundSlowD eps := by
  simpa [backgroundSlowLength, one_div] using Real.rpow_inv_natCast_pow
    (div_pos tripleD0_pos (backgroundSlowD_pos eps he)).le (by decide : (3 : ℕ) ≠ 0)

theorem backgroundSlow_scaling (eps : ℝ) (he : 1 + eps ≠ 0) :
    backgroundSlowD eps * backgroundSlowLength eps =
      tripleD0 / backgroundSlowLength eps ^ 2 := by
  have hl := ne_of_gt (backgroundSlowLength_pos eps he)
  have hd := ne_of_gt (backgroundSlowD_pos eps he)
  have hc := backgroundSlowLength_cube eps he
  field_simp at hc ⊢
  nlinarith

theorem backgroundRadius_contDiffAt (n : ℕ∞ω) (eps : ℝ) (he : 1 + eps ≠ 0) :
    ContDiffAt ℝ n backgroundRadius eps := by
  exact (contDiffAt_const.add contDiffAt_id).rpow_const_of_ne he

theorem backgroundDelta_contDiffAt (n : ℕ∞ω) (eps : ℝ) (he : 1 + eps ≠ 0) :
    ContDiffAt ℝ n backgroundDelta eps := by
  exact contDiffAt_const.sub ((contDiffAt_const.mul contDiffAt_id).div
    ((contDiffAt_const.add contDiffAt_id).pow 2) (pow_ne_zero 2 he))

theorem backgroundSlowD_contDiffAt (n : ℕ∞ω) (eps : ℝ) (he : 1 + eps ≠ 0) :
    ContDiffAt ℝ n backgroundSlowD eps := by
  have hroot := (backgroundDelta_contDiffAt n eps he).sqrt
    (ne_of_gt (backgroundDelta_pos eps he))
  exact contDiffAt_const.div
    ((contDiffAt_const.mul ((contDiffAt_const.add contDiffAt_id).pow 2)).mul
      (contDiffAt_const.add hroot)) (ne_of_gt (by
        exact mul_pos (mul_pos (by norm_num) (sq_pos_of_ne_zero he)) (by positivity)))

theorem backgroundSlowLambda_contDiffAt (n : ℕ∞ω) (eps : ℝ) (he : 1 + eps ≠ 0) :
    ContDiffAt ℝ n backgroundSlowLambda eps :=
  contDiffAt_id.mul (backgroundSlowD_contDiffAt n eps he)

theorem backgroundMatrix_contDiffAt (n : ℕ∞ω) (eps tau : ℝ) (he : 1 + eps ≠ 0)
    (i j : Fin 2) : ContDiffAt ℝ n (fun e => backgroundMatrix e tau i j) eps := by
  fin_cases i <;> fin_cases j
  all_goals simp [backgroundMatrix]
  all_goals fun_prop (disch := assumption)

theorem backgroundSlowK_contDiffAt (n : ℕ∞ω) (eps tau : ℝ) (he : |eps| < 1 / 4) :
    ContDiffAt ℝ n (fun e => backgroundSlowK e tau) eps := by
  have hn := ne_of_gt (backgroundSmall_one_add_pos eps he)
  exact (backgroundMatrix_contDiffAt n eps tau hn 0 1).neg.div
    ((backgroundMatrix_contDiffAt n eps tau hn 0 0).sub
      (backgroundSlowLambda_contDiffAt n eps hn))
    (ne_of_gt (backgroundSlow_denominator_pos eps tau he))

theorem backgroundSlowLength_contDiffAt (n : ℕ∞ω) (eps : ℝ) (he : 1 + eps ≠ 0) :
    ContDiffAt ℝ n backgroundSlowLength eps := by
  exact (contDiffAt_const.div (backgroundSlowD_contDiffAt n eps he)
    (ne_of_gt (backgroundSlowD_pos eps he))).rpow_const_of_ne
    (ne_of_gt (div_pos tripleD0_pos (backgroundSlowD_pos eps he)))

theorem backgroundAngularScale_contDiffAt (n : ℕ∞ω) (eps tau : ℝ) (he : |eps| < 1 / 4) :
    ContDiffAt ℝ n (fun e => backgroundAngularScale e tau) eps := by
  have hn := ne_of_gt (backgroundSmall_one_add_pos eps he)
  have hs : 0 < 1 + backgroundSlowK eps tau ^ 2 := by positivity
  exact (backgroundSlowLength_contDiffAt n eps hn).div
    ((backgroundRadius_contDiffAt n eps hn).mul
      ((contDiffAt_const.add ((backgroundSlowK_contDiffAt n eps tau he).pow 2)).sqrt
        (ne_of_gt hs)))
    (ne_of_gt (mul_pos (backgroundRadius_pos eps (backgroundSmall_one_add_pos eps he))
      (Real.sqrt_pos.mpr hs)))

end DominantFiveBody
