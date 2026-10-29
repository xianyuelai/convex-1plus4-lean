import DominantFiveBody.Coorbital

/-!
# The positive weighted quadratic form at the end of §2, Lemma `lem:cycle`

All unordered pairs are represented by `i < j`. The hypotheses below retain
the positive coefficient condition or the cycle comparison as explicit proof
obligations. These results do not supply the directed flow cycle decomposition.
-/

namespace DominantFiveBody.Coorbital

noncomputable section

open scoped BigOperators

def pairForm {n : ℕ} (weight : Fin n → Fin n → ℝ) (u : Fin n → ℝ) : ℝ :=
  ∑ i : Fin n, ∑ j : Fin n, if i < j then weight i j * (u j - u i) ^ 2 else 0

def weightedAngleForm {n : ℕ} (mass : Fin n → ℝ)
    (coefficient : Fin n → Fin n → ℝ) (u : Fin n → ℝ) : ℝ :=
  pairForm (fun i j => mass i * mass j * coefficient i j) u

theorem pairForm_nonneg {n : ℕ} (weight : Fin n → Fin n → ℝ) (u : Fin n → ℝ)
    (hweight : ∀ i j, i < j → 0 ≤ weight i j) : 0 ≤ pairForm weight u := by
  apply Finset.sum_nonneg
  intro i _
  apply Finset.sum_nonneg
  intro j _
  split_ifs with hij
  · exact mul_nonneg (hweight i j hij) (sq_nonneg _)
  · exact le_rfl

/-- A nonpositive energy with every pair weighted positively forces a
constant vector. This is the precise sum-of-squares argument at the end of
the proof of manuscript Lemma `lem:cycle`. -/
theorem constant_of_pairForm_nonpos {n : ℕ}
    (weight : Fin n → Fin n → ℝ) (u : Fin n → ℝ)
    (hweight : ∀ i j, i < j → 0 < weight i j)
    (hQ : pairForm weight u ≤ 0) : ∀ i j, u i = u j := by
  have hterm : ∀ i j, 0 ≤ if i < j then weight i j * (u j - u i) ^ 2 else 0 := by
    intro i j
    split_ifs with hij
    · exact mul_nonneg (le_of_lt (hweight i j hij)) (sq_nonneg _)
    · exact le_rfl
  have hlt : ∀ i j, i < j → u i = u j := by
    intro i j hij
    have hrow : (∑ j : Fin n, if i < j then weight i j * (u j - u i) ^ 2 else 0)
        ≤ pairForm weight u :=
      Finset.single_le_sum (fun k _ => Finset.sum_nonneg (fun l _ => hterm k l))
        (Finset.mem_univ i)
    have hentry := Finset.single_le_sum (fun k _ => hterm i k) (Finset.mem_univ j)
    have hle : weight i j * (u j - u i) ^ 2 ≤ 0 := by
      have h := le_trans hentry (le_trans hrow hQ)
      simpa only [hij, if_true] using h
    have hsq : (u j - u i) ^ 2 ≤ 0 :=
      nonpos_of_mul_nonpos_right hle (hweight i j hij)
    nlinarith [sq_nonneg (u j - u i)]
  intro i j
  rcases lt_trichotomy i j with hij | hij | hij
  · exact hlt i j hij
  · subst j; rfl
  · exact (hlt j i hij).symm

theorem pairForm_zero_of_constant {n : ℕ}
    (weight : Fin n → Fin n → ℝ) (u : Fin n → ℝ)
    (hu : ∀ i j, u i = u j) : pairForm weight u = 0 := by
  unfold pairForm
  apply Finset.sum_eq_zero
  intro i _
  apply Finset.sum_eq_zero
  intro j _
  rw [hu j i]
  simp

theorem pairForm_eq_zero_iff_constant {n : ℕ}
    (weight : Fin n → Fin n → ℝ) (u : Fin n → ℝ)
    (hweight : ∀ i j, i < j → 0 < weight i j) :
    pairForm weight u = 0 ↔ ∀ i j, u i = u j := by
  constructor
  · intro hQ
    exact constant_of_pairForm_nonpos weight u hweight (le_of_eq hQ)
  · exact pairForm_zero_of_constant weight u

theorem pairForm_pos_of_nonconstant {n : ℕ}
    (weight : Fin n → Fin n → ℝ) (u : Fin n → ℝ)
    (hweight : ∀ i j, i < j → 0 < weight i j)
    (hu : ¬ ∀ i j, u i = u j) : 0 < pairForm weight u := by
  by_contra hQ
  exact hu (constant_of_pairForm_nonpos weight u hweight (le_of_not_gt hQ))

theorem weightedAngleForm_pos_of_nonconstant {n : ℕ}
    (mass : Fin n → ℝ) (coefficient : Fin n → Fin n → ℝ) (u : Fin n → ℝ)
    (hmass : ∀ i, 0 < mass i)
    (hcoeff : ∀ i j, i < j → 0 < coefficient i j)
    (hu : ¬ ∀ i j, u i = u j) : 0 < weightedAngleForm mass coefficient u := by
  exact pairForm_pos_of_nonconstant _ u
    (fun i j hij => mul_pos (mul_pos (hmass i) (hmass j)) (hcoeff i j hij)) hu

/-- If the cycle bound in equation `eq:cycle-bound` has been established,
the resulting form is strictly positive off the constants. The comparison
is an explicit hypothesis; the present theorem does not prove that bound. -/
theorem angularForm_pos_of_cycle_bound {n : ℕ}
    (mass : Fin n → ℝ) (k b : Fin n → Fin n → ℝ) (u : Fin n → ℝ)
    (hmass : ∀ i, 0 < mass i)
    (hb : ∀ i j, i < j → 0 < b i j)
    (hcycle : weightedAngleForm mass b u ≤ weightedAngleForm mass k u)
    (hu : ¬ ∀ i j, u i = u j) : 0 < weightedAngleForm mass k u := by
  exact lt_of_lt_of_le (weightedAngleForm_pos_of_nonconstant mass b u hmass hb hu) hcycle

/-- Fixing any angle eliminates the constant kernel. This is the algebraic
positive-definiteness conclusion used in Theorem `thm:coorbital`. -/
theorem pairForm_pos_on_rotation_slice {n : ℕ}
    (weight : Fin n → Fin n → ℝ) (u : Fin n → ℝ) (p : Fin n)
    (hweight : ∀ i j, i < j → 0 < weight i j)
    (hp : u p = 0) (hu : u ≠ 0) : 0 < pairForm weight u := by
  apply pairForm_pos_of_nonconstant weight u hweight
  intro hconstant
  apply hu
  funext i
  exact (hconstant i p).trans hp

/-- The exact left hand quadratic expression in `eq:cycle-bound`. -/
def coorbitalKappaForm {n : ℕ} (mass theta u : Fin n → ℝ) : ℝ :=
  weightedAngleForm mass (fun i j => kappa (theta j - theta i)) u

/-- The exact right hand quadratic expression in `eq:cycle-bound`. -/
def coorbitalRemainderForm {n : ℕ} (mass theta u : Fin n → ℝ) : ℝ :=
  weightedAngleForm mass (fun i j => positiveRemainder (theta j - theta i)) u

/-- A concrete, source-matching version of the last inference of Lemma
`lem:cycle`. Its one unproved hypothesis is precisely `eq:cycle-bound`;
the scalar `b > 0` and sum-of-squares consequences are proved here. -/
theorem coorbitalKappaForm_pos_of_cycle_bound {n : ℕ}
    (mass theta u : Fin n → ℝ)
    (hmass : ∀ i, 0 < mass i)
    (harc : ∀ i j, i < j → 0 < theta j - theta i ∧ theta j - theta i < Real.pi)
    (hcycle : coorbitalRemainderForm mass theta u ≤ coorbitalKappaForm mass theta u)
    (hu : ¬ ∀ i j, u i = u j) : 0 < coorbitalKappaForm mass theta u := by
  exact angularForm_pos_of_cycle_bound mass _ _ u hmass
    (fun i j hij => positiveRemainder_pos (harc i j hij).1 (harc i j hij).2) hcycle hu

theorem coorbitalKappaForm_pos_on_rotation_slice {n : ℕ}
    (mass theta u : Fin n → ℝ) (p : Fin n)
    (hmass : ∀ i, 0 < mass i)
    (harc : ∀ i j, i < j → 0 < theta j - theta i ∧ theta j - theta i < Real.pi)
    (hcycle : coorbitalRemainderForm mass theta u ≤ coorbitalKappaForm mass theta u)
    (hp : u p = 0) (hu : u ≠ 0) : 0 < coorbitalKappaForm mass theta u := by
  apply coorbitalKappaForm_pos_of_cycle_bound mass theta u hmass harc hcycle
  intro hconstant
  apply hu
  funext i
  exact (hconstant i p).trans hp

end

end DominantFiveBody.Coorbital
