import DominantFiveBody.TripleScalar

/-! # Positive-weight existence for the scalar three-body seed

An explicit Euler gap polynomial proves the same source existence statement.
It is a derived equation of the actual divided residual, not an assumed root.
Arbitrary zero-weight boundary existence is not asserted.
-/

noncomputable section
open scoped BigOperators Matrix ContDiff
open Filter Set Topology

namespace DominantFiveBody
set_option maxHeartbeats 1000000

def tripleEulerPolynomial (alpha : TripleVector) (r : ℝ) : ℝ :=
  (alpha 0 + alpha 1) * r ^ 5 + (3 * alpha 0 + 2 * alpha 1) * r ^ 4 +
    (3 * alpha 0 + alpha 1) * r ^ 3 - (alpha 1 + 3 * alpha 2) * r ^ 2 -
    (2 * alpha 1 + 3 * alpha 2) * r - (alpha 1 + alpha 2)

theorem tripleEulerPolynomial_zero_neg (alpha : TripleVector) (ha : ∀ i, 0 < alpha i) :
    tripleEulerPolynomial alpha 0 < 0 := by
  simp only [tripleEulerPolynomial, zero_pow (by decide : 5 ≠ 0),
    zero_pow (by decide : 4 ≠ 0), zero_pow (by decide : 3 ≠ 0),
    zero_pow (by decide : 2 ≠ 0), mul_zero, add_zero, zero_sub, sub_zero]
  linarith [ha 1, ha 2]

theorem tripleEulerPolynomial_exists_pos_root (alpha : TripleVector) (ha : ∀ i, 0 < alpha i) :
    ∃ r : ℝ, 0 < r ∧ tripleEulerPolynomial alpha r = 0 := by
  let C : ℝ := 4 * alpha 1 + 7 * alpha 2
  let q : ℝ := alpha 0 + alpha 1
  let R : ℝ := C / q + 1
  have hC : 0 < C := by dsimp [C]; linarith [ha 1, ha 2]
  have hq : 0 < q := add_pos (ha 0) (ha 1)
  have hR : 1 < R := by dsimp [R]; linarith [div_pos hC hq]
  have hqR : C < q * R := by dsimp [R]; field_simp; nlinarith
  have hR2 : 1 ≤ R ^ 2 := by nlinarith
  have hRR2 : R ≤ R ^ 2 := by nlinarith
  have hR35 : R ^ 3 ≤ R ^ 5 := pow_le_pow_right₀ hR.le (by decide)
  have hdom : C * R ^ 2 < q * R ^ 5 := by
    have hmul := mul_lt_mul_of_pos_right hqR (sq_pos_of_pos (by linarith : 0 < R))
    have hpow := mul_le_mul_of_nonneg_left hR35 hq.le
    nlinarith
  have hpositive : 0 < tripleEulerPolynomial alpha R := by
    have h0 := ha 0
    have h1 := ha 1
    have h2 := ha 2
    have ht4 : 0 ≤ (3 * alpha 0 + 2 * alpha 1) * R ^ 4 := by positivity
    have ht3 : 0 ≤ (3 * alpha 0 + alpha 1) * R ^ 3 := by positivity
    have hneg1 := mul_le_mul_of_nonneg_left hRR2
      (show 0 ≤ 2 * alpha 1 + 3 * alpha 2 by linarith)
    have hneg0 := mul_le_mul_of_nonneg_left hR2
      (show 0 ≤ alpha 1 + alpha 2 by linarith)
    unfold tripleEulerPolynomial
    dsimp [q, C] at hdom
    nlinarith
  have hc : ContinuousOn (tripleEulerPolynomial alpha) (Icc 0 R) := by
    unfold tripleEulerPolynomial; fun_prop
  obtain ⟨r, hr, hz⟩ := intermediate_value_Icc (by linarith : 0 ≤ R) hc
    ⟨(tripleEulerPolynomial_zero_neg alpha ha).le, hpositive.le⟩
  refine ⟨r, lt_of_le_of_ne hr.1 ?_, hz⟩
  intro heq
  subst r
  linarith [tripleEulerPolynomial_zero_neg alpha ha]

def tripleFirstGapCoefficient (alpha : TripleVector) (r : ℝ) : ℝ :=
  alpha 0 + alpha 1 + alpha 2 / (1 + r) ^ 2 - alpha 2 / r ^ 2

def tripleSecondGapCoefficient (alpha : TripleVector) (r : ℝ) : ℝ :=
  (alpha 1 + alpha 2) / r ^ 2 + alpha 0 / (1 + r) ^ 2 - alpha 0

theorem tripleEulerPolynomial_eq_coefficients (alpha : TripleVector) {r : ℝ} (hr : 0 < r) :
    tripleEulerPolynomial alpha r = r ^ 2 * (1 + r) ^ 2 *
      (r * tripleFirstGapCoefficient alpha r - tripleSecondGapCoefficient alpha r) := by
  unfold tripleEulerPolynomial tripleFirstGapCoefficient tripleSecondGapCoefficient
  field_simp
  ring

theorem tripleFirstGapCoefficient_pos_at_root (alpha : TripleVector) (ha : ∀ i, 0 < alpha i)
    {r : ℝ} (hr : 0 < r) (hz : tripleEulerPolynomial alpha r = 0) :
    0 < tripleFirstGapCoefficient alpha r := by
  have hn : r ^ 2 * (1 + r) ^ 2 ≠ 0 :=
    mul_ne_zero (pow_ne_zero 2 (ne_of_gt hr))
      (pow_ne_zero 2 (ne_of_gt (show 0 < 1 + r by linarith)))
  rw [tripleEulerPolynomial_eq_coefficients alpha hr] at hz
  have heq : r * tripleFirstGapCoefficient alpha r = tripleSecondGapCoefficient alpha r :=
    sub_eq_zero.mp ((mul_eq_zero.mp hz).resolve_left hn)
  have hsum : 0 < tripleFirstGapCoefficient alpha r + tripleSecondGapCoefficient alpha r := by
    have h0 := ha 0
    have h1 := ha 1
    have h2 := ha 2
    have hp : 0 ≤ (alpha 0 + alpha 2) / (1 + r) ^ 2 := by positivity
    have hq : 0 ≤ alpha 1 / r ^ 2 := by positivity
    have heq' : tripleFirstGapCoefficient alpha r + tripleSecondGapCoefficient alpha r =
        alpha 1 + alpha 1 / r ^ 2 + (alpha 0 + alpha 2) / (1 + r) ^ 2 := by
      unfold tripleFirstGapCoefficient tripleSecondGapCoefficient
      ring
    rw [heq']; linarith
  rw [← heq] at hsum
  have hfactor : 0 < (1 + r) * tripleFirstGapCoefficient alpha r := by nlinarith
  by_contra hbad
  have hnonpos := mul_nonpos_of_nonneg_of_nonpos
    (show 0 ≤ 1 + r by linarith) (le_of_not_gt hbad)
  linarith

theorem tripleScalarForce_neg (x : ℝ) : tripleScalarForce (-x) = -tripleScalarForce x := by
  simp only [tripleScalarForce, abs_neg, neg_div]

theorem tripleScalarForce_positive_formula {x : ℝ} (hx : 0 < x) :
    tripleScalarForce x = 1 / x ^ 2 := by
  unfold tripleScalarForce
  rw [abs_of_pos hx]
  field_simp

theorem tripleScalarResidual_gap_rows (alpha z : TripleVector) {a b : ℝ}
    (ha : 0 < a) (hb : 0 < b) (hgap0 : z 1 - z 0 = a) (hgap1 : z 2 - z 1 = b) :
    (tripleScalarResidual alpha z 1 - tripleScalarResidual alpha z 0 =
      tripleD0 * a - (alpha 0 + alpha 1) / a ^ 2 - alpha 2 / (a + b) ^ 2 + alpha 2 / b ^ 2) ∧
    (tripleScalarResidual alpha z 2 - tripleScalarResidual alpha z 1 =
      tripleD0 * b + alpha 0 / a ^ 2 - alpha 0 / (a + b) ^ 2 - (alpha 1 + alpha 2) / b ^ 2) := by
  have h01 : z 0 - z 1 = -a := by linarith
  have h02 : z 0 - z 2 = -(a + b) := by linarith
  have h12 : z 1 - z 2 = -b := by linarith
  have h20 : z 2 - z 0 = a + b := by linarith
  have hF0 : tripleScalarForce 0 = 0 := by simp [tripleScalarForce]
  have hFa := tripleScalarForce_positive_formula ha
  have hFb := tripleScalarForce_positive_formula hb
  have hFab := tripleScalarForce_positive_formula (add_pos ha hb)
  have hFnab : tripleScalarForce (-b + -a) = -(1 / (a + b) ^ 2) := by
    rw [show -b + -a = -(a + b) by ring, tripleScalarForce_neg, hFab]
  constructor
  · simp [tripleScalarResidual, Fin.sum_univ_three, Finset.sum_erase_eq_sub,
      hgap0, h01, h02, h12, tripleScalarForce_neg, hFa, hFb, hFnab, hF0]
    linear_combination tripleD0 * hgap0
  · simp [tripleScalarResidual, Fin.sum_univ_three, Finset.sum_erase_eq_sub,
      hgap0, hgap1, h12, h20, tripleScalarForce_neg, hFa, hFb, hFab, hF0]
    linear_combination tripleD0 * hgap1

theorem tripleOrdered_of_positive_gaps {z : TripleVector}
    (h01 : z 0 < z 1) (h12 : z 1 < z 2) : TripleOrdered z := by
  have h02 := lt_trans h01 h12
  intro i j hij
  fin_cases i <;> fin_cases j
  all_goals simp_all

theorem tripleScalar_positive_root_exists (alpha : TripleVector)
    (ha : ∀ i, 0 < alpha i) (hasum : ∑ i, alpha i = 1) :
    ∃ z : TripleVector, TripleOrdered z ∧ ∀ i, tripleScalarResidual alpha z i = 0 := by
  obtain ⟨r, hr, hz⟩ := tripleEulerPolynomial_exists_pos_root alpha ha
  have hA := tripleFirstGapCoefficient_pos_at_root alpha ha hr hz
  let a : ℝ := (tripleFirstGapCoefficient alpha r / tripleD0) ^ ((3 : ℝ)⁻¹)
  have ha0 : 0 < a := Real.rpow_pos_of_pos (div_pos hA tripleD0_pos) _
  have ha3 : a ^ 3 = tripleFirstGapCoefficient alpha r / tripleD0 :=
    Real.rpow_inv_natCast_pow (div_pos hA tripleD0_pos).le (by decide : (3 : ℕ) ≠ 0)
  have hscale : tripleD0 * a ^ 3 = tripleFirstGapCoefficient alpha r := by
    rw [ha3]; field_simp [ne_of_gt tripleD0_pos]
  let v : TripleGaps := ![a, r * a]
  let z : TripleVector := tripleCenteringMatrix alpha *ᵥ v
  have hgap : tripleGapMatrix *ᵥ z = v := by
    change tripleGapMatrix *ᵥ (tripleCenteringMatrix alpha *ᵥ v) = v
    rw [Matrix.mulVec_mulVec, tripleGapMatrix_centeringMatrix alpha hasum, Matrix.one_mulVec]
  have hgap0 : z 1 - z 0 = a := by
    have h := congrFun hgap 0
    simp [tripleGapMatrix, Matrix.mulVec, dotProduct, Fin.sum_univ_three, v] at h
    linarith
  have hgap1 : z 2 - z 1 = r * a := by
    have h := congrFun hgap 1
    simp [tripleGapMatrix, Matrix.mulVec, dotProduct, Fin.sum_univ_three, v] at h
    linarith
  have hordered := tripleOrdered_of_positive_gaps
    (sub_pos.mp (show 0 < z 1 - z 0 by rw [hgap0]; exact ha0))
    (sub_pos.mp (show 0 < z 2 - z 1 by rw [hgap1]; exact mul_pos hr ha0))
  have hcoeff : r * tripleFirstGapCoefficient alpha r = tripleSecondGapCoefficient alpha r := by
    rw [tripleEulerPolynomial_eq_coefficients alpha hr] at hz
    have hn : r ^ 2 * (1 + r) ^ 2 ≠ 0 :=
      mul_ne_zero (pow_ne_zero 2 (ne_of_gt hr))
        (pow_ne_zero 2 (ne_of_gt (show 0 < 1 + r by linarith)))
    exact sub_eq_zero.mp ((mul_eq_zero.mp hz).resolve_left hn)
  obtain ⟨hrow0, hrow1⟩ := tripleScalarResidual_gap_rows alpha z ha0 (mul_pos hr ha0) hgap0 hgap1
  have hzrow0 : tripleScalarResidual alpha z 1 - tripleScalarResidual alpha z 0 = 0 := by
    rw [hrow0]
    unfold tripleFirstGapCoefficient at hscale
    have hr0 := ne_of_gt hr
    have ha0' := ne_of_gt ha0
    have hra : a + r * a ≠ 0 := ne_of_gt (add_pos ha0 (mul_pos hr ha0))
    field_simp
    field_simp at hscale
    nlinarith [hscale]
  have hzrow1 : tripleScalarResidual alpha z 2 - tripleScalarResidual alpha z 1 = 0 := by
    rw [hrow1]
    rw [← hscale] at hcoeff
    unfold tripleSecondGapCoefficient at hcoeff
    have hr0 := ne_of_gt hr
    have ha0' := ne_of_gt ha0
    have hra : a + r * a ≠ 0 := ne_of_gt (add_pos ha0 (mul_pos hr ha0))
    field_simp
    field_simp at hcoeff
    nlinarith [hcoeff]
  have hGgap : tripleGapMatrix *ᵥ (fun i => tripleScalarResidual alpha z i) = 0 := by
    ext i
    fin_cases i
    all_goals simp [tripleGapMatrix, Matrix.mulVec, dotProduct, Fin.sum_univ_three]
    · linarith
    · linarith
  exact ⟨z, hordered, tripleScalar_centered_gap_root_recovery alpha v
    ⟨fun i => (ha i).le, hasum⟩ hGgap⟩

theorem tripleScalar_positive_root_existsUnique (alpha : TripleVector)
    (ha : ∀ i, 0 < alpha i) (hasum : ∑ i, alpha i = 1) :
    ∃! z : TripleVector, TripleOrdered z ∧ ∀ i, tripleScalarResidual alpha z i = 0 := by
  obtain ⟨z, hzo, hzr⟩ := tripleScalar_positive_root_exists alpha ha hasum
  refine ⟨z, ⟨hzo, hzr⟩, ?_⟩
  intro y hy
  exact tripleScalar_root_unique alpha y z (fun i => (ha i).le) hy.1 hzo hy.2 hzr

end DominantFiveBody
