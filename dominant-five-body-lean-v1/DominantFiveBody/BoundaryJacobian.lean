import DominantFiveBody.Probe
import DominantFiveBody.CycleEstimate
import Mathlib.Analysis.Calculus.FDeriv.Prod
import Mathlib.Analysis.Calculus.FDeriv.Add
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Topology.Instances.Matrix
import Mathlib.Topology.Order.Compact
import Mathlib.Analysis.Matrix.Normed
import Mathlib.Data.Finset.Sort

/-! # The actual divided angular Jacobian at zero satellite masses

Manuscript Proposition `prop:closed`. This module differentiates the signed
equations themselves; zero masses remain coefficients and never cancel a row.
-/

noncomputable section
open scoped BigOperators Matrix Matrix.Norms.Operator

namespace DominantFiveBody

open Coorbital

theorem coorbitalKernel_hasDerivAt {t : ℝ} (ht : t ≠ 0) (htpi : |t| < Real.pi) :
    HasDerivAt coorbitalKernel (-kappa |t|) t := by
  rcases lt_or_gt_of_ne ht with hneg | hpos
  · rw [abs_of_neg hneg]
    have hnt : 0 < -t := neg_pos.mpr hneg
    have hntpi : -t < Real.pi := by simpa only [abs_of_neg hneg] using htpi
    have hcomp := ((kernelF_hasDerivAt hnt hntpi).comp t ((hasDerivAt_id t).neg)).neg
    have hd : HasDerivAt (fun x : ℝ => -kernelF (-x)) (-kappa (-t)) t := by
      convert hcomp using 1 <;> try rfl
      simp only [neg_mul_neg, mul_one]
    have heq : coorbitalKernel =ᶠ[nhds t] (fun x : ℝ => -kernelF (-x)) := by
      filter_upwards [isOpen_Iio.mem_nhds hneg] with x hx
      simp only [coorbitalKernel, if_neg (not_le.mpr (show x < 0 from hx))]
    exact hd.congr_of_eventuallyEq heq
  · rw [abs_of_pos hpos]
    have htpi' : t < Real.pi := by simpa only [abs_of_pos hpos] using htpi
    have heq : coorbitalKernel =ᶠ[nhds t] kernelF := by
      filter_upwards [isOpen_Ioi.mem_nhds hpos] with x hx
      exact coorbitalKernel_eq_positive_formula x (le_of_lt hx)
    exact (kernelF_hasDerivAt hpos htpi').congr_of_eventuallyEq heq

/-- Four distinct angles with every pair separation less than π. No mass
positivity occurs in this geometric definition. -/
def SeparatedSemicircle (theta : Satellite → ℝ) : Prop :=
  ∀ i j, i ≠ j → theta i ≠ theta j ∧ |theta j - theta i| < Real.pi

def angleProjection (i : Satellite) : (Satellite → ℝ) →L[ℝ] ℝ :=
  ContinuousLinearMap.proj i

def angularRowDifferential (mass theta : Satellite → ℝ) (i : Satellite) :
    (Satellite → ℝ) →L[ℝ] ℝ :=
  ∑ j ∈ Finset.univ.erase i,
    (mass j * kappa |theta j - theta i|) •
      (angleProjection i - angleProjection j)

def angularDifferential (mass theta : Satellite → ℝ) :
    (Satellite → ℝ) →L[ℝ] (Satellite → ℝ) :=
  ContinuousLinearMap.pi (angularRowDifferential mass theta)

/-- This is `D_theta E` in Proposition `prop:closed`, not a renamed abstract
matrix. The diagonal retains every positive or zero source coefficient. -/
def angularJacobian (mass theta : Satellite → ℝ) : Matrix Satellite Satellite ℝ :=
  fun i j => if i = j then
    ∑ k ∈ Finset.univ.erase i, mass k * kappa |theta k - theta i|
  else -mass j * kappa |theta j - theta i|

theorem coorbitalResidual_row_hasFDerivAt (mass theta : Satellite → ℝ)
    (htheta : SeparatedSemicircle theta) (i : Satellite) :
    HasFDerivAt (fun angles => coorbitalResidual mass angles i)
      (angularRowDifferential mass theta i) theta := by
  classical
  unfold coorbitalResidual angularRowDifferential
  apply HasFDerivAt.fun_sum
  intro j hj
  have hji : i ≠ j := Ne.symm (Finset.mem_erase.mp hj).1
  have hsep := htheta i j hji
  have hdiff : HasFDerivAt (fun angles : Satellite → ℝ => angles j - angles i)
      (angleProjection j - angleProjection i) theta :=
    (hasFDerivAt_apply (𝕜 := ℝ) j theta).sub (hasFDerivAt_apply (𝕜 := ℝ) i theta)
  have hd := (coorbitalKernel_hasDerivAt (sub_ne_zero.mpr hsep.1.symm) hsep.2).comp_hasFDerivAt
    (f := fun angles : Satellite → ℝ => angles j - angles i) theta hdiff
  convert hd.const_mul (mass j) using 1 <;> try rfl
  ext u
  simp only [angleProjection, smul_apply, sub_apply,
    ContinuousLinearMap.proj_apply, smul_eq_mul]
  ring

theorem coorbitalResidual_hasFDerivAt (mass theta : Satellite → ℝ)
    (htheta : SeparatedSemicircle theta) :
    HasFDerivAt (fun angles i => coorbitalResidual mass angles i)
      (angularDifferential mass theta) theta := by
  exact hasFDerivAt_pi.mpr (fun i => coorbitalResidual_row_hasFDerivAt mass theta htheta i)

theorem angularRowDifferential_apply (mass theta u : Satellite → ℝ) (i : Satellite) :
    angularRowDifferential mass theta i u =
      ∑ j ∈ Finset.univ.erase i, mass j * kappa |theta j - theta i| * (u i - u j) := by
  simp [angularRowDifferential, angleProjection]

theorem angularDifferential_apply (mass theta u : Satellite → ℝ) (i : Satellite) :
    angularDifferential mass theta u i =
      ∑ j ∈ Finset.univ.erase i, mass j * kappa |theta j - theta i| * (u i - u j) := by
  simp only [angularDifferential, ContinuousLinearMap.pi_apply]
  exact angularRowDifferential_apply mass theta u i

theorem angularJacobian_mulVec (mass theta u : Satellite → ℝ) :
    angularJacobian mass theta *ᵥ u = angularDifferential mass theta u := by
  classical
  funext i
  change (∑ j, angularJacobian mass theta i j * u j) = _
  rw [← Finset.sum_erase_add Finset.univ
    (fun j => angularJacobian mass theta i j * u j) (Finset.mem_univ i)]
  have hoff : (∑ j ∈ Finset.univ.erase i, angularJacobian mass theta i j * u j) =
      ∑ j ∈ Finset.univ.erase i, -(mass j * kappa |theta j - theta i| * u j) := by
    apply Finset.sum_congr rfl
    intro j hj
    have hji : i ≠ j := Ne.symm (Finset.mem_erase.mp hj).1
    simp only [angularJacobian, if_neg hji]
    ring
  rw [hoff, angularDifferential_apply]
  have hdiag : angularJacobian mass theta i i =
      ∑ k ∈ Finset.univ.erase i, mass k * kappa |theta k - theta i| := by
    simp [angularJacobian]
  rw [hdiag, Finset.sum_neg_distrib]
  simp_rw [mul_sub]
  rw [Finset.sum_sub_distrib, ← Finset.sum_mul]
  ring

theorem angularDifferential_constant (mass theta : Satellite → ℝ) (c : ℝ) :
    angularDifferential mass theta (fun _ => c) = 0 := by
  funext i
  rw [angularDifferential_apply]
  simp

theorem angularDifferential_apply_fullSum (mass theta u : Satellite → ℝ) (i : Satellite) :
    angularDifferential mass theta u i =
      ∑ j, mass j * kappa |theta j - theta i| * (u i - u j) := by
  rw [angularDifferential_apply, Finset.sum_erase_eq_sub (Finset.mem_univ i)]
  simp

def angularWeightedTerm (mass theta u : Satellite → ℝ) (i j : Satellite) : ℝ :=
  mass i * mass j * kappa |theta j - theta i| * (u i - u j)

theorem angularWeightedTerm_reverse (mass theta u : Satellite → ℝ) (i j : Satellite) :
    angularWeightedTerm mass theta u j i = -angularWeightedTerm mass theta u i j := by
  unfold angularWeightedTerm
  rw [abs_sub_comm (theta i) (theta j)]
  ring

theorem angularDifferential_weighted_zero (mass theta u : Satellite → ℝ) :
    (∑ i, mass i * angularDifferential mass theta u i) = 0 := by
  simp_rw [angularDifferential_apply_fullSum, Finset.mul_sum, ← mul_assoc]
  change (∑ i, ∑ j, angularWeightedTerm mass theta u i j) = 0
  have hneg : (∑ i, ∑ j, angularWeightedTerm mass theta u i j) =
      -(∑ i, ∑ j, angularWeightedTerm mass theta u i j) := by
    calc
      (∑ i, ∑ j, angularWeightedTerm mass theta u i j) =
          ∑ j, ∑ i, angularWeightedTerm mass theta u i j := Finset.sum_comm
      _ = -(∑ j, ∑ i, angularWeightedTerm mass theta u j i) := by
        rw [← Finset.sum_neg_distrib]
        apply Finset.sum_congr rfl
        intro j _
        rw [← Finset.sum_neg_distrib]
        apply Finset.sum_congr rfl
        intro i _
        exact angularWeightedTerm_reverse mass theta u j i
  linarith

theorem angularDifferential_recover_row (mass theta u : Satellite → ℝ) (p : Satellite)
    (hp : 0 < mass p) (hothers : ∀ i, i ≠ p → angularDifferential mass theta u i = 0) :
    angularDifferential mass theta u p = 0 := by
  have hsum : (∑ i, mass i * angularDifferential mass theta u i) =
      mass p * angularDifferential mass theta u p := by
    apply Finset.sum_eq_single p
    · intro i _ hip
      rw [hothers i hip, mul_zero]
    · simp
  rw [angularDifferential_weighted_zero] at hsum
  exact (mul_eq_zero.mp hsum.symm).resolve_left (ne_of_gt hp)

theorem angularEquation_eq_residual (mass theta : Satellite → ℝ) (i : Satellite) :
    angularEquation mass theta i = coorbitalResidual mass theta i := by
  unfold angularEquation coorbitalResidual
  rw [Finset.sum_erase_eq_sub (Finset.mem_univ i)]
  simp

theorem angularDifferential_energy_abs (mass theta u : Satellite → ℝ) :
    (∑ i, mass i * u i * angularDifferential mass theta u i) =
      weightedAngleForm mass (fun i j => kappa |theta j - theta i|) u := by
  simp [angularDifferential_apply_fullSum, weightedAngleForm, pairForm,
    Fin.sum_univ_four, abs_sub_comm]
  ring

def angularLinearRow {n : ℕ} (mass theta u : Fin n → ℝ) (i : Fin n) : ℝ :=
  ∑ j, mass j * kappa |theta j - theta i| * (u i - u j)

theorem angularLinearRow_energy_abs {n : ℕ} (hn₂ : 2 ≤ n) (hn₄ : n ≤ 4)
    (mass theta u : Fin n → ℝ) :
    (∑ i, mass i * u i * angularLinearRow mass theta u i) =
      weightedAngleForm mass (fun i j => kappa |theta j - theta i|) u := by
  interval_cases n
  · simp [angularLinearRow, weightedAngleForm, pairForm, Fin.sum_univ_two]
    simp_rw [abs_sub_comm (theta 0) (theta 1)]
    ring
  · simp [angularLinearRow, weightedAngleForm, pairForm, Fin.sum_univ_three, abs_sub_comm]
    ring
  · simpa only [angularLinearRow, angularDifferential_apply_fullSum] using
      angularDifferential_energy_abs mass theta u

theorem angularLinearRow_energy {n : ℕ} (hn₂ : 2 ≤ n) (hn₄ : n ≤ 4)
    (mass theta u : Fin n → ℝ)
    (harc : ∀ i j, i < j → 0 < theta j - theta i ∧ theta j - theta i < Real.pi) :
    (∑ i, mass i * u i * angularLinearRow mass theta u i) =
      coorbitalKappaForm mass theta u := by
  rw [angularLinearRow_energy_abs hn₂ hn₄]
  unfold coorbitalKappaForm weightedAngleForm pairForm
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  by_cases hij : i < j
  · simp only [if_pos hij]
    rw [abs_of_pos (harc i j hij).1]
  · rw [if_neg hij, if_neg hij]

theorem angularLinearRow_kernel_positive {n : ℕ} (hn₂ : 2 ≤ n) (hn₄ : n ≤ 4)
    (mass theta u : Fin n → ℝ) (hmass : ∀ i, 0 < mass i)
    (harc : ∀ i j, i < j → 0 < theta j - theta i ∧ theta j - theta i < Real.pi)
    (hroot : ∀ i, angularEquation mass theta i = 0)
    (hlinear : ∀ i, angularLinearRow mass theta u i = 0) : ∀ i j, u i = u j := by
  by_contra hnonconstant
  have hpos := coorbitalKappaForm_pos_at_root hn₂ hn₄ mass theta u hmass harc hroot hnonconstant
  have henergy := angularLinearRow_energy hn₂ hn₄ mass theta u harc
  simp only [hlinear, mul_zero, Finset.sum_const_zero] at henergy
  linarith

theorem angularDifferential_energy (mass theta u : Satellite → ℝ)
    (harc : ∀ i j, i < j → 0 < theta j - theta i ∧ theta j - theta i < Real.pi) :
    (∑ i, mass i * u i * angularDifferential mass theta u i) =
      coorbitalKappaForm mass theta u := by
  rw [angularDifferential_energy_abs]
  unfold coorbitalKappaForm weightedAngleForm pairForm
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  by_cases hij : i < j
  · simp only [if_pos hij]
    rw [abs_of_pos (harc i j hij).1]
  · rw [if_neg hij, if_neg hij]

/-- The actual divided angular differential has precisely the rotation
kernel at every strictly positive root. This conclusion uses the proved
cycle estimate, with no assumed Hessian or spectral condition. -/
theorem angularDifferential_kernel_iff_positive (mass theta u : Satellite → ℝ)
    (hmass : ∀ i, 0 < mass i)
    (harc : ∀ i j, i < j → 0 < theta j - theta i ∧ theta j - theta i < Real.pi)
    (hroot : ∀ i, coorbitalResidual mass theta i = 0) :
    angularDifferential mass theta u = 0 ↔ ∀ i j, u i = u j := by
  constructor
  · intro hzero
    by_contra hnonconstant
    have hpos := coorbitalKappaForm_pos_at_root (n := 4) (by decide) (by decide)
      mass theta u hmass harc
      (fun i => (angularEquation_eq_residual mass theta i).trans (hroot i)) hnonconstant
    have henergy := angularDifferential_energy mass theta u harc
    rw [hzero] at henergy
    simp only [Pi.zero_apply, mul_zero, Finset.sum_const_zero] at henergy
    linarith
  · intro hconstant
    have hu : u = fun _ => u 0 := by funext i; exact hconstant i 0
    rw [hu]
    exact angularDifferential_constant mass theta (u 0)

def deletedAngularJacobian (mass theta : Satellite → ℝ) (p q : Satellite) :
    Matrix (Fin 3) (Fin 3) ℝ :=
  (angularJacobian mass theta).submatrix p.succAbove q.succAbove

theorem deletedAngularJacobian_action (mass theta : Satellite → ℝ)
    (p q : Satellite) (v : Fin 3 → ℝ) (i : Fin 3) :
    (deletedAngularJacobian mass theta p q *ᵥ v) i =
      angularDifferential mass theta (Fin.insertNth q 0 v) (p.succAbove i) := by
  rw [← angularJacobian_mulVec]
  change (∑ j : Fin 3, angularJacobian mass theta (p.succAbove i) (q.succAbove j) * v j) =
    ∑ j : Fin 4, angularJacobian mass theta (p.succAbove i) j *
      Fin.insertNth (α := fun _ : Fin 4 => ℝ) q 0 v j
  rw [Fin.sum_univ_succAbove _ q]
  simp

theorem deletedAngularJacobian_isUnit_of_constant_kernel
    (mass theta : Satellite → ℝ) (p q : Satellite) (hp : 0 < mass p)
    (hkernel : ∀ u, angularDifferential mass theta u = 0 → ∀ i j, u i = u j) :
    IsUnit (deletedAngularJacobian mass theta p q) := by
  apply Matrix.mulVec_injective_iff_isUnit.mp
  intro v w hvw
  have hdiff : deletedAngularJacobian mass theta p q *ᵥ (v - w) = 0 := by
    rw [Matrix.mulVec_sub, hvw, sub_self]
  let u : Satellite → ℝ := Fin.insertNth q 0 (v - w)
  have hrows : ∀ i, i ≠ p → angularDifferential mass theta u i = 0 := by
    intro i hip
    obtain ⟨j, rfl⟩ := Fin.exists_succAbove_eq hip
    rw [← deletedAngularJacobian_action]
    exact congrFun hdiff j
  have hpzero := angularDifferential_recover_row mass theta u p hp hrows
  have hfull : angularDifferential mass theta u = 0 := by
    funext i
    by_cases hip : i = p
    · subst i; exact hpzero
    · exact hrows i hip
  have hconstant := hkernel u hfull
  have huq : u q = 0 := by
    exact Fin.insertNth_apply_same (α := fun _ : Fin 4 => ℝ) q 0 (v - w)
  funext j
  have hz : (v - w) j = 0 := by
    rw [← Fin.insertNth_apply_succAbove (α := fun _ : Fin 4 => ℝ) q 0 (v - w) j]
    exact (hconstant (q.succAbove j) q).trans huq
  exact sub_eq_zero.mp hz

/-- Every choice of fixed angle and omitted positive-mass row is valid in
the interior simplex. This verifies the actual three by three matrix. -/
theorem deletedAngularJacobian_isUnit_positive (mass theta : Satellite → ℝ)
    (p q : Satellite) (hmass : ∀ i, 0 < mass i)
    (harc : ∀ i j, i < j → 0 < theta j - theta i ∧ theta j - theta i < Real.pi)
    (hroot : ∀ i, coorbitalResidual mass theta i = 0) :
    IsUnit (deletedAngularJacobian mass theta p q) := by
  exact deletedAngularJacobian_isUnit_of_constant_kernel mass theta p q (hmass p)
    (fun u hu => (angularDifferential_kernel_iff_positive mass theta u hmass harc hroot).mp hu)

theorem deletedAngularJacobian_det_ne_zero_positive (mass theta : Satellite → ℝ)
    (p q : Satellite) (hmass : ∀ i, 0 < mass i)
    (harc : ∀ i j, i < j → 0 < theta j - theta i ∧ theta j - theta i < Real.pi)
    (hroot : ∀ i, coorbitalResidual mass theta i = 0) :
    (deletedAngularJacobian mass theta p q).det ≠ 0 := by
  exact ((Matrix.isUnit_iff_isUnit_det _).mp
    (deletedAngularJacobian_isUnit_positive mass theta p q hmass harc hroot)).ne_zero

/-- Four distinct retained probe equations cannot have only one positive
source: the three other labels would need three distinct positions among
the two points at distance `h` from that source. -/
theorem no_one_source_coorbital_root (mass theta : Satellite → ℝ) (p : Satellite)
    (hp : 0 < mass p) (hothers : ∀ i, i ≠ p → mass i = 0)
    (htheta : SeparatedSemicircle theta)
    (hroot : ∀ i, coorbitalResidual mass theta i = 0) : False := by
  classical
  have hh : 0 < h := by unfold h; positivity
  have htheta_inj : Function.Injective theta := by
    intro i j hij
    by_contra hne
    exact (htheta i j hne).1 hij
  have hprobe : ∀ i, i ≠ p → |theta p - theta i| = h := by
    intro i hip
    have he := (angularEquation_eq_residual mass theta i).trans (hroot i)
    have hsum : angularEquation mass theta i = mass p * coorbitalKernel (theta p - theta i) := by
      unfold angularEquation
      apply Finset.sum_eq_single p
      · intro j _ hjp
        rw [hothers j hjp, zero_mul]
      · simp
    rw [hsum] at he
    have hkernel := (mul_eq_zero.mp he).resolve_left (ne_of_gt hp)
    exact (coorbitalKernel_zero_iff_abs_eq_h
      (sub_ne_zero.mpr (htheta i p hip).1.symm) (htheta i p hip).2).mp hkernel
  have hsubset : (Finset.univ.erase p).image theta ⊆
      ({theta p - h, theta p + h} : Finset ℝ) := by
    intro y hy
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hy
    have hip := (Finset.mem_erase.mp hi).1
    have hd := hprobe i hip
    rcases le_total 0 (theta p - theta i) with hnonneg | hnonpos
    · rw [abs_of_nonneg hnonneg] at hd
      have hiθ : theta i = theta p - h := by linarith
      simp [hiθ]
    · rw [abs_of_nonpos hnonpos] at hd
      have hiθ : theta i = theta p + h := by linarith
      simp [hiθ]
  have hcard : ((Finset.univ.erase p).image theta).card = 3 := by
    rw [Finset.card_image_of_injective _ htheta_inj]
    simp
  have hpairne : theta p - h ≠ theta p + h := by linarith
  have hcardle := Finset.card_le_card hsubset
  rw [hcard] at hcardle
  simp [hpairne] at hcardle

theorem sum_mass_two_sources (mass : Satellite → ℝ) (a b : Satellite) (hab : a ≠ b)
    (hothers : ∀ j, j ≠ a → j ≠ b → mass j = 0) (f : Satellite → ℝ) :
    (∑ j, mass j * f j) = mass a * f a + mass b * f b := by
  classical
  rw [← Finset.sum_erase_add Finset.univ (fun j => mass j * f j) (Finset.mem_univ a)]
  have hrem : (∑ j ∈ Finset.univ.erase a, mass j * f j) = mass b * f b := by
    apply Finset.sum_eq_single b
    · intro j hj hjb
      rw [hothers j (Finset.mem_erase.mp hj).1 hjb, zero_mul]
    · simp [hab.symm]
  rw [hrem, add_comm]

theorem twoSourceSpan_lt_of_pair_separations {x : ℝ}
    (hx : |x| < Real.pi) (hxh : |x - h| < Real.pi) : twoSourceSpan x < Real.pi := by
  have hh : 0 < h := by unfold h; positivity
  have hhpi : h < Real.pi := by unfold h; linarith [Real.pi_pos]
  unfold twoSourceSpan
  by_cases hxneg : x < 0
  · rw [max_eq_left (by linarith), min_eq_right (le_of_lt hxneg)]
    have hdiff : x - h < 0 := by linarith
    simpa only [abs_of_neg hdiff, neg_sub] using hxh
  · have hxnonneg : 0 ≤ x := le_of_not_gt hxneg
    rw [min_eq_left hxnonneg]
    by_cases hhx : h ≤ x
    · rw [max_eq_right hhx]
      simpa only [sub_zero, abs_of_nonneg hxnonneg] using hx
    · rw [max_eq_left (le_of_not_ge hhx), sub_zero]
      exact hhpi

theorem two_source_separation (mass theta : Satellite → ℝ) (a b : Satellite)
    (hab : a < b) (_ha : 0 < mass a) (hb : 0 < mass b)
    (hothers : ∀ j, j ≠ a → j ≠ b → mass j = 0)
    (harc : ∀ i j, i < j → 0 < theta j - theta i ∧ theta j - theta i < Real.pi)
    (hroot : ∀ i, coorbitalResidual mass theta i = 0) : theta b - theta a = h := by
  have hroota := (angularEquation_eq_residual mass theta a).trans (hroot a)
  unfold angularEquation at hroota
  rw [sum_mass_two_sources mass a b (ne_of_lt hab) hothers] at hroota
  simp only [sub_self, coorbitalKernel_zero, mul_zero, zero_add] at hroota
  rw [coorbitalKernel_eq_positive_formula _ (harc a b hab).1.le] at hroota
  exact (kernelF_eq_zero_iff (harc a b hab).1 (harc a b hab).2).mp
    ((mul_eq_zero.mp hroota).resolve_left (ne_of_gt hb))

/-- The actual zero-source diagonal of `D_theta E` is positive when its
positive support consists of the two labels `a,b`. This applies Lemma 2.3
to the retained signed probe equation, rather than assuming its conclusion. -/
theorem two_source_probe_diagonal_pos (mass theta : Satellite → ℝ) (a b k : Satellite)
    (hab : a < b) (ha : 0 < mass a) (hb : 0 < mass b)
    (hothers : ∀ j, j ≠ a → j ≠ b → mass j = 0) (hsum : ∑ j, mass j = 1)
    (htheta : SeparatedSemicircle theta)
    (harc : ∀ i j, i < j → 0 < theta j - theta i ∧ theta j - theta i < Real.pi)
    (hroot : ∀ i, coorbitalResidual mass theta i = 0) (hka : k ≠ a) (hkb : k ≠ b) :
    0 < angularJacobian mass theta k k := by
  have hsep := two_source_separation mass theta a b hab ha hb hothers harc hroot
  have hsumab : mass a + mass b = 1 := by
    have hsum' := sum_mass_two_sources mass a b (ne_of_lt hab) hothers (fun _ => 1)
    simp only [mul_one] at hsum'
    exact hsum'.symm.trans hsum
  let x : ℝ := theta k - theta a
  have hx0 : x ≠ 0 := sub_ne_zero.mpr (htheta k a hka).1
  have hxh_eq : x - h = theta k - theta b := by dsimp [x]; linarith
  have hxh : x ≠ h := by
    intro heq
    have htne := (htheta k b hkb).1
    apply htne
    dsimp [x] at heq
    linarith
  have hspan : twoSourceSpan x < Real.pi := by
    apply twoSourceSpan_lt_of_pair_separations
    · exact (htheta a k hka.symm).2
    · rw [hxh_eq]
      exact (htheta b k hkb.symm).2
  have hproberoot : mass a * coorbitalKernel x + mass b * coorbitalKernel (x - h) = 0 := by
    have hk := (angularEquation_eq_residual mass theta k).trans (hroot k)
    unfold angularEquation at hk
    rw [sum_mass_two_sources mass a b (ne_of_lt hab) hothers] at hk
    have hdiffa : theta a - theta k = -x := by dsimp [x]; ring
    have hdiffb : theta b - theta k = -(x - h) := by rw [hxh_eq]; ring
    rw [hdiffa, hdiffb, coorbitalKernel_neg, coorbitalKernel_neg] at hk
    linarith
  have hprobe := twoSourceProbe ha.le hb.le hsumab hx0 hxh hspan hproberoot
  have hmassk : mass k = 0 := hothers k hka hkb
  have hdiag : angularJacobian mass theta k k =
      mass a * kappa |x| + mass b * kappa |x - h| := by
    rw [show angularJacobian mass theta k k =
      ∑ j ∈ Finset.univ.erase k, mass j * kappa |theta j - theta k| by simp [angularJacobian]]
    rw [Finset.sum_erase_eq_sub (Finset.mem_univ k), hmassk, zero_mul, sub_zero]
    rw [sum_mass_two_sources mass a b (ne_of_lt hab) hothers]
    rw [abs_sub_comm (theta a) (theta k), abs_sub_comm (theta b) (theta k)]
    rw [← hxh_eq]
  rw [hdiag]
  exact hprobe

theorem angularDifferential_two_sources (mass theta u : Satellite → ℝ) (a b i : Satellite)
    (hab : a ≠ b) (hothers : ∀ j, j ≠ a → j ≠ b → mass j = 0) :
    angularDifferential mass theta u i =
      mass a * kappa |theta a - theta i| * (u i - u a) +
      mass b * kappa |theta b - theta i| * (u i - u b) := by
  rw [angularDifferential_apply_fullSum]
  simpa only [mul_assoc] using sum_mass_two_sources mass a b hab hothers
    (fun j => kappa |theta j - theta i| * (u i - u j))

theorem angularJacobian_diagonal_two_sources (mass theta : Satellite → ℝ) (a b k : Satellite)
    (hab : a ≠ b) (hothers : ∀ j, j ≠ a → j ≠ b → mass j = 0)
    (hka : k ≠ a) (hkb : k ≠ b) :
    angularJacobian mass theta k k =
      mass a * kappa |theta a - theta k| + mass b * kappa |theta b - theta k| := by
  rw [show angularJacobian mass theta k k =
    ∑ j ∈ Finset.univ.erase k, mass j * kappa |theta j - theta k| by simp [angularJacobian]]
  rw [Finset.sum_erase_eq_sub (Finset.mem_univ k), hothers k hka hkb, zero_mul, sub_zero]
  exact sum_mass_two_sources mass a b hab hothers _

/-- The complete two-positive-source branch of Proposition `prop:closed`:
the two zero-source probe diagonals and the positive support are both checked. -/
theorem angularDifferential_kernel_two_sources (mass theta u : Satellite → ℝ)
    (a b : Satellite) (hab : a < b) (ha : 0 < mass a) (hb : 0 < mass b)
    (hothers : ∀ j, j ≠ a → j ≠ b → mass j = 0) (hsum : ∑ j, mass j = 1)
    (htheta : SeparatedSemicircle theta)
    (harc : ∀ i j, i < j → 0 < theta j - theta i ∧ theta j - theta i < Real.pi)
    (hroot : ∀ i, coorbitalResidual mass theta i = 0)
    (hzero : angularDifferential mass theta u = 0) : ∀ i j, u i = u j := by
  have hh : 0 < h := by unfold h; positivity
  have hsep := two_source_separation mass theta a b hab ha hb hothers harc hroot
  have habu : u a = u b := by
    have he := congrFun hzero a
    rw [angularDifferential_two_sources mass theta u a b a (ne_of_lt hab) hothers] at he
    simp only [sub_self, mul_zero, zero_add] at he
    rw [hsep, abs_of_pos hh, kappa_h] at he
    have hcoef : mass b * (9 / 4) ≠ 0 := by positivity
    exact sub_eq_zero.mp ((mul_eq_zero.mp he).resolve_left hcoef)
  have hsame : ∀ i, u i = u a := by
    intro i
    by_cases hia : i = a
    · subst i; rfl
    by_cases hib : i = b
    · subst i; exact habu.symm
    have hpos := two_source_probe_diagonal_pos mass theta a b i hab ha hb hothers hsum
      htheta harc hroot hia hib
    have he := congrFun hzero i
    simp only [Pi.zero_apply] at he
    rw [angularDifferential_two_sources mass theta u a b i (ne_of_lt hab) hothers] at he
    rw [← habu] at he
    have hcoef := angularJacobian_diagonal_two_sources mass theta a b i (ne_of_lt hab)
      hothers hia hib
    have hfactor : angularJacobian mass theta i i * (u i - u a) = 0 := by
      rw [hcoef]
      nlinarith [he]
    exact sub_eq_zero.mp ((mul_eq_zero.mp hfactor).resolve_left (ne_of_gt hpos))
  intro i j
  exact (hsame i).trans (hsame j).symm

/-- An explicit second kernel vector for a four by four skew matrix at a
three-source root. After ordering the zero source last and choosing a nonzero
two by two pivot, its last coordinate is one. This is the actual algebra
behind the rank argument in Proposition `prop:closed`. -/
theorem skew4_kernel_vector_at_zero_source
    (A : Matrix (Fin 4) (Fin 4) ℝ) (mass : Fin 4 → ℝ)
    (hdiag : ∀ i, A i i = 0) (hskew : ∀ i j, A j i = -A i j)
    (hroot : ∀ i, ∑ j, A i j * mass j = 0)
    (hzero : mass 3 = 0) (hpositive : 0 < mass 2) (hpivot : A 0 1 ≠ 0) :
    ∃ nu : Fin 4 → ℝ, nu 3 = 1 ∧ ∀ i, ∑ j, A i j * nu j = 0 := by
  have h10 := hskew 0 1
  have h20 := hskew 0 2
  have h21 := hskew 1 2
  have h30 := hskew 0 3
  have h31 := hskew 1 3
  have h32 := hskew 2 3
  have hrow0 := hroot 0
  have hrow1 := hroot 1
  have hrow3 := hroot 3
  simp only [Fin.sum_univ_four, hdiag, hzero, h10, h30, h31, h32,
    zero_mul, mul_zero, zero_add, add_zero] at hrow0 hrow1 hrow3
  have hpfmul : (A 0 1 * A 2 3 - A 0 2 * A 1 3 + A 0 3 * A 1 2) * mass 2 = 0 := by
    linear_combination -A 0 1 * hrow3 - A 1 3 * hrow0 + A 0 3 * hrow1
  have hpf : A 0 1 * A 2 3 - A 0 2 * A 1 3 + A 0 3 * A 1 2 = 0 :=
    (mul_eq_zero.mp hpfmul).resolve_right (ne_of_gt hpositive)
  let nu : Fin 4 → ℝ := ![A 1 3 / A 0 1, -A 0 3 / A 0 1, 0, 1]
  refine ⟨nu, by simp [nu], ?_⟩
  intro i
  rw [Fin.sum_univ_four]
  fin_cases i
  · change A 0 0 * (A 1 3 / A 0 1) + A 0 1 * (-A 0 3 / A 0 1) +
      A 0 2 * 0 + A 0 3 * 1 = 0
    rw [hdiag 0]
    field_simp [hpivot]
    ring
  · change A 1 0 * (A 1 3 / A 0 1) + A 1 1 * (-A 0 3 / A 0 1) +
      A 1 2 * 0 + A 1 3 * 1 = 0
    rw [h10, hdiag 1]
    field_simp [hpivot]
    ring
  · change A 2 0 * (A 1 3 / A 0 1) + A 2 1 * (-A 0 3 / A 0 1) +
      A 2 2 * 0 + A 2 3 * 1 = 0
    rw [h20, h21]
    field_simp [hpivot]
    linear_combination hpf
  · change A 3 0 * (A 1 3 / A 0 1) + A 3 1 * (-A 0 3 / A 0 1) +
      A 3 2 * 0 + A 3 3 * 1 = 0
    rw [h30, h31, hdiag 3]
    field_simp [hpivot]
    ring

theorem skew4_kernel_vector_reindexed
    (A : Matrix Satellite Satellite ℝ) (mass : Satellite → ℝ) (e : Equiv.Perm Satellite)
    (hdiag : ∀ i, A i i = 0) (hskew : ∀ i j, A j i = -A i j)
    (hroot : ∀ i, ∑ j, A i j * mass j = 0)
    (hzero : mass (e 3) = 0) (hpositive : 0 < mass (e 2))
    (hpivot : A (e 0) (e 1) ≠ 0) :
    ∃ nu : Satellite → ℝ, nu (e 3) = 1 ∧ ∀ i, ∑ j, A i j * nu j = 0 := by
  have hroot' : ∀ i, ∑ j, A (e i) (e j) * mass (e j) = 0 := by
    intro i
    exact (Equiv.sum_comp e (fun j => A (e i) j * mass j)).trans (hroot (e i))
  obtain ⟨nu', hnu3, hnu⟩ := skew4_kernel_vector_at_zero_source
    (fun i j => A (e i) (e j)) (fun i => mass (e i))
    (fun i => hdiag (e i)) (fun i j => hskew (e i) (e j)) hroot' hzero hpositive hpivot
  refine ⟨fun i => nu' (e.symm i), by simpa using hnu3, ?_⟩
  intro i
  have heq := (Equiv.sum_comp e (fun j => A i j * nu' (e.symm j))).symm
  simp only [Equiv.symm_apply_apply] at heq
  exact heq.trans (by simpa only [Equiv.apply_symm_apply] using hnu (e.symm i))

/-- The positive support is kept in its original increasing order while the
unique zero source is moved to the last index. -/
def zeroLastPermutation (k : Satellite) : Equiv.Perm Satellite :=
  if k = 0 then ((Equiv.swap 0 1).trans (Equiv.swap 0 2)).trans (Equiv.swap 0 3)
  else if k = 1 then (Equiv.swap 1 2).trans (Equiv.swap 1 3)
  else if k = 2 then Equiv.swap 2 3
  else Equiv.refl _

theorem zeroLastPermutation_last (k : Satellite) : zeroLastPermutation k 3 = k := by
  fin_cases k <;> decide

theorem zeroLastPermutation_support (k : Satellite) (i : Fin 3) :
    zeroLastPermutation k i.castSucc = k.succAbove i := by
  fin_cases k <;> fin_cases i <;> decide

theorem succAbove_preserves_lt_four (k : Satellite) (i j : Fin 3) :
    i < j → k.succAbove i < k.succAbove j := by
  fin_cases k <;> fin_cases i <;> fin_cases j <;> decide

theorem three_source_restricted_root (mass theta : Satellite → ℝ) (k : Satellite)
    (hzero : mass k = 0) (hroot : ∀ i, coorbitalResidual mass theta i = 0) :
    ∀ i : Fin 3, angularEquation (mass ∘ k.succAbove) (theta ∘ k.succAbove) i = 0 := by
  intro i
  have he := (angularEquation_eq_residual mass theta (k.succAbove i)).trans (hroot (k.succAbove i))
  unfold angularEquation at he ⊢
  rw [Fin.sum_univ_succAbove _ k] at he
  simpa only [hzero, zero_mul, zero_add, Function.comp_apply] using he

theorem three_source_support_kernel (mass theta u : Satellite → ℝ) (k : Satellite)
    (hzero : mass k = 0) (hmass : ∀ i, i ≠ k → 0 < mass i)
    (harc : ∀ i j, i < j → 0 < theta j - theta i ∧ theta j - theta i < Real.pi)
    (hroot : ∀ i, coorbitalResidual mass theta i = 0)
    (hlinear : angularDifferential mass theta u = 0) :
    ∀ i j : Fin 3, u (k.succAbove i) = u (k.succAbove j) := by
  apply angularLinearRow_kernel_positive (n := 3) (by decide) (by decide)
    (mass ∘ k.succAbove) (theta ∘ k.succAbove) (u ∘ k.succAbove)
  · intro i
    exact hmass (k.succAbove i) (Fin.succAbove_ne k i)
  · intro i j hij
    exact harc _ _ (succAbove_preserves_lt_four k i j hij)
  · exact three_source_restricted_root mass theta k hzero hroot
  · intro i
    have he := congrFun hlinear (k.succAbove i)
    rw [angularDifferential_apply_fullSum, Fin.sum_univ_succAbove _ k] at he
    simpa only [angularLinearRow, hzero, zero_mul, zero_add, Function.comp_apply,
      Pi.zero_apply] using he

/-- The auxiliary direction used to make all four masses positive is
constructed inside the actual signed matrix kernel. -/
theorem three_source_kernel_vector (mass theta : Satellite → ℝ) (k : Satellite)
    (hzero : mass k = 0) (hmass : ∀ i, i ≠ k → 0 < mass i)
    (harc : ∀ i j, i < j → 0 < theta j - theta i ∧ theta j - theta i < Real.pi)
    (hroot : ∀ i, coorbitalResidual mass theta i = 0) :
    ∃ nu : Satellite → ℝ, nu k = 1 ∧ ∀ i, coorbitalResidual nu theta i = 0 := by
  let e := zeroLastPermutation k
  have he0 : e 0 = k.succAbove 0 := zeroLastPermutation_support k 0
  have he1 : e 1 = k.succAbove 1 := zeroLastPermutation_support k 1
  have he2 : e 2 = k.succAbove 2 := zeroLastPermutation_support k 2
  have he3 : e 3 = k := zeroLastPermutation_last k
  have hmass3 : ∀ i : Fin 3, 0 < (mass ∘ k.succAbove) i :=
    fun i => hmass _ (Fin.succAbove_ne k i)
  have harc3 : ∀ i j : Fin 3, i < j →
      0 < (theta ∘ k.succAbove) j - (theta ∘ k.succAbove) i ∧
      (theta ∘ k.succAbove) j - (theta ∘ k.succAbove) i < Real.pi :=
    fun i j hij => harc _ _ (succAbove_preserves_lt_four k i j hij)
  have hroot3 := three_source_restricted_root mass theta k hzero hroot
  obtain ⟨hgap, _, _⟩ := three_root_gaps (mass ∘ k.succAbove) (theta ∘ k.succAbove)
    hmass3 harc3 hroot3
  have hpivot : coorbitalMatrix theta (e 0) (e 1) ≠ 0 := by
    rw [he0, he1]
    have hlt := succAbove_preserves_lt_four k 0 1 (by decide)
    have hpos := (harc _ _ hlt).1
    simp only [coorbitalMatrix, if_neg (ne_of_lt hlt),
      coorbitalKernel_eq_positive_formula _ hpos.le]
    exact ne_of_gt (kernelF_pos_on_short_arc hpos hgap)
  have hAroot : ∀ i, ∑ j, coorbitalMatrix theta i j * mass j = 0 := by
    intro i
    simpa only [mul_comm] using (coorbitalResidual_eq_matrix_sum mass theta i).symm.trans (hroot i)
  obtain ⟨nu, hnu, hnuA⟩ := skew4_kernel_vector_reindexed (coorbitalMatrix theta) mass e
    (fun i => by simp [coorbitalMatrix]) (coorbitalMatrix_reverse theta) hAroot
    (by rw [he3]; exact hzero) (by rw [he2]; exact hmass _ (Fin.succAbove_ne k 2)) hpivot
  refine ⟨nu, by rwa [he3] at hnu, ?_⟩
  intro i
  rw [coorbitalResidual_eq_matrix_sum]
  simpa only [mul_comm] using hnuA i

def coordinateIndicator (k : Satellite) : Satellite → ℝ := fun i => if i = k then 1 else 0

theorem weightedCoordinate_energy_identity (mass theta : Satellite → ℝ)
    (coefficient : ℝ → ℝ) (k : Satellite) :
    weightedAngleForm mass (fun i j => coefficient |theta j - theta i|)
      (coordinateIndicator k) =
      mass k * ∑ j ∈ Finset.univ.erase k, mass j * coefficient |theta j - theta k| := by
  classical
  have henergy (u : Satellite → ℝ) :
      weightedAngleForm mass (fun i j => coefficient |theta j - theta i|) u =
      ∑ i, mass i * u i * ∑ j, mass j * coefficient |theta j - theta i| * (u i - u j) := by
    simp [weightedAngleForm, pairForm, Fin.sum_univ_four, abs_sub_comm]
    ring
  rw [henergy]
  rw [Finset.sum_eq_single k]
  · simp only [coordinateIndicator, if_true, mul_one]
    rw [← Finset.sum_erase_add Finset.univ
      (fun j => mass j * coefficient |theta j - theta k| * (1 - (if j = k then 1 else 0)))
      (Finset.mem_univ k)]
    simp only [if_true, sub_self, mul_zero, add_zero]
    congr 1
    apply Finset.sum_congr rfl
    intro j hj
    rw [if_neg (Finset.mem_erase.mp hj).1]
    ring
  · intro i _ hik
    simp [coordinateIndicator, hik]
  · simp

theorem coorbitalSlopeForm_coordinate_identity (mass theta : Satellite → ℝ) (k : Satellite)
    (harc : ∀ i j, i < j → 0 < theta j - theta i ∧ theta j - theta i < Real.pi) :
    coorbitalSlopeForm mass theta (coordinateIndicator k) =
      mass k * ∑ j ∈ Finset.univ.erase k, mass j * slopeCoefficient |theta j - theta k| := by
  rw [← weightedCoordinate_energy_identity]
  unfold coorbitalSlopeForm weightedAngleForm pairForm
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  by_cases hij : i < j
  · simp only [if_pos hij]
    rw [abs_of_pos (harc i j hij).1]
  · rw [if_neg hij, if_neg hij]

/-- A right-sided limiting argument is applied to the actual small positive
kernel perturbations. Every root hypothesis comes from linearity of `Aμ=0`.
This proves the formerly zero-source diagonal strictly positive. -/
theorem three_source_probe_diagonal_pos (mass theta : Satellite → ℝ) (k : Satellite)
    (hzero : mass k = 0) (hmass : ∀ i, i ≠ k → 0 < mass i)
    (htheta : SeparatedSemicircle theta)
    (harc : ∀ i j, i < j → 0 < theta j - theta i ∧ theta j - theta i < Real.pi)
    (hroot : ∀ i, coorbitalResidual mass theta i = 0) :
    0 < angularJacobian mass theta k k := by
  obtain ⟨nu, hnuk, hnuroot⟩ := three_source_kernel_vector mass theta k hzero hmass harc hroot
  let positivePerturbation : ℝ → Satellite → ℝ := fun s i => mass i + s * nu i
  have hpositive : ∀ᶠ s in nhdsWithin (0 : ℝ) (Set.Ioi 0),
      ∀ i, 0 < positivePerturbation s i := by
    have hsupport : ∀ᶠ s in nhds (0 : ℝ), ∀ i, i ≠ k →
        0 < positivePerturbation s i := by
      apply Filter.eventually_all.mpr
      intro i
      by_cases hik : i = k
      · exact Filter.Eventually.of_forall (fun _ hne => False.elim (hne hik))
      · have hc : ContinuousAt (fun s : ℝ => positivePerturbation s i) 0 := by
          dsimp [positivePerturbation]
          fun_prop
        have hpzero : 0 < positivePerturbation 0 i := by
          simpa only [positivePerturbation, zero_mul, add_zero] using hmass i hik
        exact (Filter.Tendsto.eventually_const_lt hpzero hc.tendsto).mono (fun s hs _ => hs)
    filter_upwards [hsupport.filter_mono nhdsWithin_le_nhds,
      eventually_mem_nhdsWithin] with s hs hspos i
    by_cases hik : i = k
    · subst i
      simpa only [positivePerturbation, hzero, hnuk, mul_one, zero_add, Set.mem_Ioi] using hspos
    · exact hs i hik
  have hpertroot (s : ℝ) : ∀ i, angularEquation (positivePerturbation s) theta i = 0 := by
    intro i
    unfold angularEquation positivePerturbation
    simp_rw [add_mul, mul_assoc, Finset.sum_add_distrib, ← Finset.mul_sum]
    change angularEquation mass theta i + s * angularEquation nu theta i = 0
    rw [angularEquation_eq_residual mass theta i, hroot i,
      angularEquation_eq_residual nu theta i, hnuroot i]
    ring
  have hnonneg : ∀ᶠ s in nhdsWithin (0 : ℝ) (Set.Ioi 0),
      0 ≤ ∑ j ∈ Finset.univ.erase k, positivePerturbation s j *
        slopeCoefficient |theta j - theta k| := by
    filter_upwards [hpositive] with s hs
    have hcycle := four_coorbitalSlopeForm_nonneg (positivePerturbation s) theta
      (coordinateIndicator k) hs harc (hpertroot s)
    rw [coorbitalSlopeForm_coordinate_identity (positivePerturbation s) theta k harc] at hcycle
    exact nonneg_of_mul_nonneg_right hcycle (hs k)
  have hcontinuous : ContinuousAt
      (fun s : ℝ => ∑ j ∈ Finset.univ.erase k, positivePerturbation s j *
        slopeCoefficient |theta j - theta k|) 0 := by
    dsimp [positivePerturbation]
    fun_prop
  have hlimit := ge_of_tendsto (hcontinuous.tendsto.mono_left nhdsWithin_le_nhds) hnonneg
  simp only [positivePerturbation, zero_mul, add_zero] at hlimit
  have hbremainder : 0 < ∑ j ∈ Finset.univ.erase k,
      mass j * positiveRemainder |theta j - theta k| := by
    apply Finset.sum_pos
    · intro j hj
      have hjk := (Finset.mem_erase.mp hj).1
      have hsep := htheta k j hjk.symm
      have hdiff : 0 < |theta j - theta k| := abs_pos.mpr (sub_ne_zero.mpr hsep.1.symm)
      exact mul_pos (hmass j hjk) (positiveRemainder_pos hdiff hsep.2)
    · have hcard : (Finset.univ.erase k).card = 3 := by simp
      exact Finset.card_pos.mp (by omega)
  rw [show angularJacobian mass theta k k =
    ∑ j ∈ Finset.univ.erase k, mass j * kappa |theta j - theta k| by simp [angularJacobian]]
  have hsplit : (∑ j ∈ Finset.univ.erase k, mass j * kappa |theta j - theta k|) =
      (∑ j ∈ Finset.univ.erase k, mass j * positiveRemainder |theta j - theta k|) +
      (∑ j ∈ Finset.univ.erase k, mass j * slopeCoefficient |theta j - theta k|) := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro j _
    unfold positiveRemainder
    ring
  rw [hsplit]
  linarith

theorem angularDifferential_kernel_three_sources (mass theta u : Satellite → ℝ) (k : Satellite)
    (hzero : mass k = 0) (hmass : ∀ i, i ≠ k → 0 < mass i)
    (htheta : SeparatedSemicircle theta)
    (harc : ∀ i j, i < j → 0 < theta j - theta i ∧ theta j - theta i < Real.pi)
    (hroot : ∀ i, coorbitalResidual mass theta i = 0)
    (hlinear : angularDifferential mass theta u = 0) : ∀ i j, u i = u j := by
  let p : Satellite := k.succAbove 0
  have hs := three_source_support_kernel mass theta u k hzero hmass harc hroot hlinear
  have hsupport : ∀ j, j ≠ k → u j = u p := by
    intro j hjk
    obtain ⟨i, rfl⟩ := Fin.exists_succAbove_eq hjk
    exact hs i 0
  have hdiagpos := three_source_probe_diagonal_pos mass theta k hzero hmass htheta harc hroot
  have hfactor : angularJacobian mass theta k k * (u k - u p) = 0 := by
    calc
      angularJacobian mass theta k k * (u k - u p) =
          (∑ j ∈ Finset.univ.erase k, mass j * kappa |theta j - theta k|) * (u k - u p) := by
        simp [angularJacobian]
      _ = ∑ j ∈ Finset.univ.erase k, mass j * kappa |theta j - theta k| * (u k - u p) :=
        Finset.sum_mul _ _ _
      _ = ∑ j ∈ Finset.univ.erase k, mass j * kappa |theta j - theta k| * (u k - u j) := by
        apply Finset.sum_congr rfl
        intro j hj
        rw [hsupport j (Finset.mem_erase.mp hj).1]
      _ = angularDifferential mass theta u k := (angularDifferential_apply mass theta u k).symm
      _ = 0 := congrFun hlinear k
  have hkp : u k = u p := sub_eq_zero.mp
    ((mul_eq_zero.mp hfactor).resolve_left (ne_of_gt hdiagpos))
  have hsame : ∀ i, u i = u p := by
    intro i
    by_cases hik : i = k
    · subst i; exact hkp
    · exact hsupport i hik
  intro i j
  exact (hsame i).trans (hsame j).symm

/-- The complete constant-kernel assertion of Proposition `prop:closed`
on its ordered angle chart. Every possible nonnegative support is handled;
the divided zero-source equations remain assumptions and are never dropped. -/
theorem angularDifferential_kernel_nonnegative (mass theta u : Satellite → ℝ)
    (hmass : ∀ i, 0 ≤ mass i) (hsum : ∑ i, mass i = 1)
    (htheta : SeparatedSemicircle theta)
    (harc : ∀ i j, i < j → 0 < theta j - theta i ∧ theta j - theta i < Real.pi)
    (hroot : ∀ i, coorbitalResidual mass theta i = 0)
    (hlinear : angularDifferential mass theta u = 0) : ∀ i j, u i = u j := by
  have hpos (i : Satellite) (hi : mass i ≠ 0) : 0 < mass i :=
    lt_of_le_of_ne (hmass i) (Ne.symm hi)
  by_cases h0 : mass 0 = 0 <;> by_cases h1 : mass 1 = 0 <;>
    by_cases h2 : mass 2 = 0 <;> by_cases h3 : mass 3 = 0
  · have hs := hsum
    simp only [Fin.sum_univ_four, h0, h1, h2, h3, zero_add] at hs
    norm_num at hs
  · exact (no_one_source_coorbital_root mass theta 3 (hpos 3 h3)
      (by intro i hi; fin_cases i <;> first | assumption | exact False.elim (hi rfl))
      htheta hroot).elim
  · exact (no_one_source_coorbital_root mass theta 2 (hpos 2 h2)
      (by intro i hi; fin_cases i <;> first | assumption | exact False.elim (hi rfl))
      htheta hroot).elim
  · exact angularDifferential_kernel_two_sources mass theta u 2 3 (by decide)
      (hpos 2 h2) (hpos 3 h3)
      (by intro i hia hib; fin_cases i <;> first | assumption | contradiction)
      hsum htheta harc hroot hlinear
  · exact (no_one_source_coorbital_root mass theta 1 (hpos 1 h1)
      (by intro i hi; fin_cases i <;> first | assumption | exact False.elim (hi rfl))
      htheta hroot).elim
  · exact angularDifferential_kernel_two_sources mass theta u 1 3 (by decide)
      (hpos 1 h1) (hpos 3 h3)
      (by intro i hia hib; fin_cases i <;> first | assumption | contradiction)
      hsum htheta harc hroot hlinear
  · exact angularDifferential_kernel_two_sources mass theta u 1 2 (by decide)
      (hpos 1 h1) (hpos 2 h2)
      (by intro i hia hib; fin_cases i <;> first | assumption | contradiction)
      hsum htheta harc hroot hlinear
  · exact angularDifferential_kernel_three_sources mass theta u 0 h0
      (by intro i hi; fin_cases i <;> first | exact hpos _ (by assumption) | contradiction)
      htheta harc hroot hlinear
  · exact (no_one_source_coorbital_root mass theta 0 (hpos 0 h0)
      (by intro i hi; fin_cases i <;> first | assumption | exact False.elim (hi rfl))
      htheta hroot).elim
  · exact angularDifferential_kernel_two_sources mass theta u 0 3 (by decide)
      (hpos 0 h0) (hpos 3 h3)
      (by intro i hia hib; fin_cases i <;> first | assumption | contradiction)
      hsum htheta harc hroot hlinear
  · exact angularDifferential_kernel_two_sources mass theta u 0 2 (by decide)
      (hpos 0 h0) (hpos 2 h2)
      (by intro i hia hib; fin_cases i <;> first | assumption | contradiction)
      hsum htheta harc hroot hlinear
  · exact angularDifferential_kernel_three_sources mass theta u 1 h1
      (by intro i hi; fin_cases i <;> first | exact hpos _ (by assumption) | contradiction)
      htheta harc hroot hlinear
  · exact angularDifferential_kernel_two_sources mass theta u 0 1 (by decide)
      (hpos 0 h0) (hpos 1 h1)
      (by intro i hia hib; fin_cases i <;> first | assumption | contradiction)
      hsum htheta harc hroot hlinear
  · exact angularDifferential_kernel_three_sources mass theta u 2 h2
      (by intro i hi; fin_cases i <;> first | exact hpos _ (by assumption) | contradiction)
      htheta harc hroot hlinear
  · exact angularDifferential_kernel_three_sources mass theta u 3 h3
      (by intro i hi; fin_cases i <;> first | exact hpos _ (by assumption) | contradiction)
      htheta harc hroot hlinear
  · exact (angularDifferential_kernel_iff_positive mass theta u
      (by intro i; fin_cases i <;> exact hpos _ (by assumption)) harc hroot).mp hlinear

theorem angularDifferential_kernel_iff_nonnegative (mass theta u : Satellite → ℝ)
    (hmass : ∀ i, 0 ≤ mass i) (hsum : ∑ i, mass i = 1)
    (htheta : SeparatedSemicircle theta)
    (harc : ∀ i j, i < j → 0 < theta j - theta i ∧ theta j - theta i < Real.pi)
    (hroot : ∀ i, coorbitalResidual mass theta i = 0) :
    angularDifferential mass theta u = 0 ↔ ∀ i j, u i = u j := by
  constructor
  · exact angularDifferential_kernel_nonnegative mass theta u hmass hsum htheta harc hroot
  · intro hconstant
    have hu : u = fun _ => u 0 := by funext i; exact hconstant i 0
    rw [hu]
    exact angularDifferential_constant mass theta (u 0)

theorem deletedAngularJacobian_isUnit_nonnegative (mass theta : Satellite → ℝ)
    (p q : Satellite) (hmass : ∀ i, 0 ≤ mass i) (hsum : ∑ i, mass i = 1)
    (hp : 0 < mass p) (htheta : SeparatedSemicircle theta)
    (harc : ∀ i j, i < j → 0 < theta j - theta i ∧ theta j - theta i < Real.pi)
    (hroot : ∀ i, coorbitalResidual mass theta i = 0) :
    IsUnit (deletedAngularJacobian mass theta p q) := by
  exact deletedAngularJacobian_isUnit_of_constant_kernel mass theta p q hp
    (fun u hu => angularDifferential_kernel_nonnegative mass theta u hmass hsum htheta harc hroot hu)

theorem deletedAngularJacobian_det_ne_zero_nonnegative (mass theta : Satellite → ℝ)
    (p q : Satellite) (hmass : ∀ i, 0 ≤ mass i) (hsum : ∑ i, mass i = 1)
    (hp : 0 < mass p) (htheta : SeparatedSemicircle theta)
    (harc : ∀ i j, i < j → 0 < theta j - theta i ∧ theta j - theta i < Real.pi)
    (hroot : ∀ i, coorbitalResidual mass theta i = 0) :
    (deletedAngularJacobian mass theta p q).det ≠ 0 := by
  exact ((Matrix.isUnit_iff_isUnit_det _).mp
    (deletedAngularJacobian_isUnit_nonnegative mass theta p q hmass hsum hp htheta harc hroot)).ne_zero

theorem separatedSemicircle_of_ordered (theta : Satellite → ℝ)
    (harc : ∀ i j, i < j → 0 < theta j - theta i ∧ theta j - theta i < Real.pi) :
    SeparatedSemicircle theta := by
  intro i j hij
  rcases lt_or_gt_of_ne hij with hlt | hgt
  · have hs := harc i j hlt
    exact ⟨ne_of_lt (sub_pos.mp hs.1), by simpa only [abs_of_pos hs.1] using hs.2⟩
  · have hs := harc j i hgt
    exact ⟨ne_of_gt (sub_pos.mp hs.1), by simpa only [abs_sub_comm, abs_of_pos hs.1] using hs.2⟩

/-- The source's consecutive gap and span bounds imply the all-pair bounds
used in the ordered angle chart. -/
theorem pairGapBounds_of_consecutive (theta : Satellite → ℝ) (delta eta : ℝ)
    (hdelta : 0 < delta)
    (hgaps : ∀ i : Fin 3, delta ≤ theta i.succ - theta i.castSucc)
    (hspan : theta 3 - theta 0 ≤ Real.pi - eta) :
    ∀ i j : Satellite, i < j →
      delta ≤ theta j - theta i ∧ theta j - theta i ≤ Real.pi - eta := by
  have h01 := hgaps 0
  have h12 := hgaps 1
  have h23 := hgaps 2
  change delta ≤ theta 1 - theta 0 at h01
  change delta ≤ theta 2 - theta 1 at h12
  change delta ≤ theta 3 - theta 2 at h23
  intro i j hij
  fin_cases i <;> fin_cases j
  all_goals try { norm_num at hij }
  all_goals dsimp
  all_goals constructor <;> linarith

theorem angularJacobian_continuousAt (mass theta : Satellite → ℝ)
    (htheta : SeparatedSemicircle theta) :
    ContinuousAt (fun z : (Satellite → ℝ) × (Satellite → ℝ) =>
      angularJacobian z.1 z.2) (mass, theta) := by
  classical
  apply continuousAt_pi.mpr
  intro i
  apply continuousAt_pi.mpr
  intro j
  by_cases hij : i = j
  · subst j
    simp only [angularJacobian]
    apply tendsto_finsetSum
    intro k hk
    have hsep := htheta i k (Ne.symm (Finset.mem_erase.mp hk).1)
    have htpos : 0 < |theta k - theta i| :=
      abs_pos.mpr (sub_ne_zero.mpr hsep.1.symm)
    exact (by fun_prop : ContinuousAt
      (fun z : (Satellite → ℝ) × (Satellite → ℝ) => z.1 k) (mass, theta)).mul
      ((kappa_hasDerivAt htpos hsep.2).continuousAt.comp
        (f := fun z : (Satellite → ℝ) × (Satellite → ℝ) => |z.2 k - z.2 i|)
        (x := (mass, theta))
        (by fun_prop))
  · simp only [angularJacobian, if_neg hij]
    have hsep := htheta i j hij
    have htpos : 0 < |theta j - theta i| :=
      abs_pos.mpr (sub_ne_zero.mpr hsep.1.symm)
    exact (by fun_prop : ContinuousAt
      (fun z : (Satellite → ℝ) × (Satellite → ℝ) => -z.1 j) (mass, theta)).mul
      ((kappa_hasDerivAt htpos hsep.2).continuousAt.comp
        (f := fun z : (Satellite → ℝ) × (Satellite → ℝ) => |z.2 j - z.2 i|)
        (x := (mass, theta))
        (by fun_prop))

theorem deletedAngularJacobian_continuousAt (mass theta : Satellite → ℝ)
    (p q : Satellite) (htheta : SeparatedSemicircle theta) :
    ContinuousAt (fun z : (Satellite → ℝ) × (Satellite → ℝ) =>
      deletedAngularJacobian z.1 z.2 p q) (mass, theta) := by
  exact (show Continuous (fun A : Matrix Satellite Satellite ℝ =>
    A.submatrix p.succAbove q.succAbove) by fun_prop).continuousAt.comp
      (f := fun z : (Satellite → ℝ) × (Satellite → ℝ) => angularJacobian z.1 z.2)
      (x := (mass, theta)) (angularJacobian_continuousAt mass theta htheta)

theorem deletedAngularJacobian_inverse_continuousAt (mass theta : Satellite → ℝ)
    (p q : Satellite) (hmass : ∀ i, 0 ≤ mass i) (hsum : ∑ i, mass i = 1)
    (hp : 0 < mass p)
    (harc : ∀ i j, i < j → 0 < theta j - theta i ∧ theta j - theta i < Real.pi)
    (hroot : ∀ i, coorbitalResidual mass theta i = 0) :
    ContinuousAt (fun z : (Satellite → ℝ) × (Satellite → ℝ) =>
      (deletedAngularJacobian z.1 z.2 p q)⁻¹) (mass, theta) := by
  have htheta := separatedSemicircle_of_ordered theta harc
  have hdet := deletedAngularJacobian_det_ne_zero_nonnegative
    mass theta p q hmass hsum hp htheta harc hroot
  have hinv : ContinuousAt Ring.inverse (deletedAngularJacobian mass theta p q).det := by
    simpa only [Ring.inverse_eq_inv'] using continuousAt_inv₀ hdet
  exact (continuousAt_matrix_inv _ hinv).comp
    (f := fun z : (Satellite → ℝ) × (Satellite → ℝ) => deletedAngularJacobian z.1 z.2 p q)
    (x := (mass, theta))
    (deletedAngularJacobian_continuousAt mass theta p q htheta)

/-- A closed set of anchored, ordered roots with collision and semicircle
margins is compact. Translation is fixed by theta 0 = 0, as in the source's
angle domain; the simplex itself supplies all mass bounds. -/
theorem isCompact_closed_coorbital_roots
    (K : Set ((Satellite → ℝ) × (Satellite → ℝ))) (delta eta : ℝ)
    (hK : IsClosed K) (hdelta : 0 < delta) (heta : 0 < eta)
    (hdata : ∀ z ∈ K, (∀ i, 0 ≤ z.1 i) ∧ (∑ i, z.1 i) = 1 ∧ z.2 0 = 0 ∧
      (∀ i : Fin 3, delta ≤ z.2 i.succ - z.2 i.castSucc) ∧
      z.2 3 - z.2 0 ≤ Real.pi - eta) : IsCompact K := by
  have hmassBox : IsCompact {m : Satellite → ℝ | ∀ i, m i ∈ Set.Icc (0 : ℝ) 1} :=
    isCompact_pi_infinite (fun _ => isCompact_Icc)
  have hangleBox : IsCompact {t : Satellite → ℝ | ∀ i, t i ∈ Set.Icc (0 : ℝ) Real.pi} :=
    isCompact_pi_infinite (fun _ => isCompact_Icc)
  apply (hmassBox.prod hangleBox).of_isClosed_subset hK
  intro z hz
  obtain ⟨hm, hsum, hanchor, hgaps, hspan⟩ := hdata z hz
  have hpairs := pairGapBounds_of_consecutive z.2 delta eta hdelta hgaps hspan
  constructor
  · intro i
    refine ⟨hm i, ?_⟩
    have hle : z.1 i ≤ ∑ j, z.1 j :=
      Finset.single_le_sum (fun j _ => hm j) (Finset.mem_univ i)
    rwa [hsum] at hle
  · intro i
    by_cases hi : i = 0
    · subst i
      exact ⟨by rw [hanchor], by rw [hanchor]; exact le_of_lt Real.pi_pos⟩
    · have h0i : (0 : Satellite) < i := lt_of_le_of_ne (Fin.zero_le i) (Ne.symm hi)
      have hs := hpairs 0 i h0i
      rw [hanchor, sub_zero] at hs
      exact ⟨le_trans (le_of_lt hdelta) hs.1, by linarith [hs.2]⟩

/-- The uniform inverse assertion of manuscript Proposition `prop:closed`,
for every closed root set in its anchored ordered chart. The consecutive
gap margin, semicircle margin and omitted mass lower bound are the source
hypotheses; no inverse bound or spectral hypothesis is assumed. -/
theorem deletedAngularJacobian_inverse_uniform_on_closed_roots
    (K : Set ((Satellite → ℝ) × (Satellite → ℝ))) (delta eta : ℝ)
    (p q : Satellite) (hK : IsClosed K) (hdelta : 0 < delta) (heta : 0 < eta)
    (hdata : ∀ z ∈ K, (∀ i, 0 ≤ z.1 i) ∧ (∑ i, z.1 i) = 1 ∧ z.2 0 = 0 ∧
      (∀ i : Fin 3, delta ≤ z.2 i.succ - z.2 i.castSucc) ∧
      z.2 3 - z.2 0 ≤ Real.pi - eta ∧ (1 / 4 : ℝ) ≤ z.1 p ∧
      (∀ i, coorbitalResidual z.1 z.2 i = 0)) :
    ∃ C : ℝ, 0 < C ∧ ∀ z ∈ K, ‖(deletedAngularJacobian z.1 z.2 p q)⁻¹‖ ≤ C := by
  have hcompact : IsCompact K := isCompact_closed_coorbital_roots K delta eta
    hK hdelta heta (by
      intro z hz
      obtain ⟨hm, hs, ha, hg, hl, _, _⟩ := hdata z hz
      exact ⟨hm, hs, ha, hg, hl⟩)
  have hcont : ContinuousOn (fun z : (Satellite → ℝ) × (Satellite → ℝ) =>
      (deletedAngularJacobian z.1 z.2 p q)⁻¹) K := by
    intro z hz
    obtain ⟨hm, hs, _, hg, hl, hp, hr⟩ := hdata z hz
    have hpairs := pairGapBounds_of_consecutive z.2 delta eta hdelta hg hl
    have harc : ∀ i j, i < j → 0 < z.2 j - z.2 i ∧ z.2 j - z.2 i < Real.pi := by
      intro i j hij
      have ht := hpairs i j hij
      exact ⟨lt_of_lt_of_le hdelta ht.1, by linarith [ht.2]⟩
    exact (deletedAngularJacobian_inverse_continuousAt z.1 z.2 p q hm hs
      (by linarith) harc hr).continuousWithinAt
  obtain ⟨C, hC⟩ := hcompact.bddAbove_image hcont.norm
  refine ⟨max C 1, lt_of_lt_of_le (by norm_num) (le_max_right C 1), ?_⟩
  intro z hz
  exact le_trans (hC (Set.mem_image_of_mem _ hz)) (le_max_left C 1)

/-- Distinct real angles can be relabeled increasingly. The pair separation
bound is preserved by this permutation; no cyclic-order hypothesis is added. -/
theorem exists_ordered_semicircle_permutation (theta : Satellite → ℝ)
    (htheta : SeparatedSemicircle theta) :
    ∃ e : Equiv.Perm Satellite, ∀ i j, i < j →
      0 < theta (e j) - theta (e i) ∧ theta (e j) - theta (e i) < Real.pi := by
  classical
  have hinj : Function.Injective theta := by
    intro i j heq
    by_contra hij
    exact (htheta i j hij).1 heq
  let s : Finset ℝ := Finset.univ.image theta
  have hcard : s.card = 4 := by
    rw [Finset.card_image_of_injective _ hinj]
    simp
  let label : Satellite → s := fun i => ⟨theta i,
    Finset.mem_image.mpr ⟨i, Finset.mem_univ i, rfl⟩⟩
  have hbij : Function.Bijective label := by
    constructor
    · intro i j heq
      exact hinj (congrArg Subtype.val heq)
    · intro x
      obtain ⟨i, _, hi⟩ := Finset.mem_image.mp x.2
      refine ⟨i, ?_⟩
      exact Subtype.ext hi
  let labels : Satellite ≃ s := Equiv.ofBijective label hbij
  let sorted : Satellite ≃o s := s.orderIsoOfFin hcard
  let e : Equiv.Perm Satellite := sorted.toEquiv.trans labels.symm
  have heq (i : Satellite) : theta (e i) = (sorted i).val := by
    exact congrArg Subtype.val (labels.apply_symm_apply (sorted i))
  refine ⟨e, ?_⟩
  intro i j hij
  have hlt : theta (e i) < theta (e j) := by
    rw [heq i, heq j]
    exact sorted.strictMono hij
  have hsep := (htheta (e i) (e j) (e.injective.ne (ne_of_lt hij))).2
  exact ⟨sub_pos.mpr hlt, by simpa only [abs_of_pos (sub_pos.mpr hlt)] using hsep⟩

theorem coorbitalResidual_reindex (mass theta : Satellite → ℝ)
    (e : Equiv.Perm Satellite) (i : Satellite) :
    coorbitalResidual (mass ∘ e) (theta ∘ e) i = coorbitalResidual mass theta (e i) := by
  rw [← angularEquation_eq_residual, ← angularEquation_eq_residual]
  exact Equiv.sum_comp e (fun j => mass j * coorbitalKernel (theta j - theta (e i)))

theorem angularDifferential_reindex_apply (mass theta u : Satellite → ℝ)
    (e : Equiv.Perm Satellite) (i : Satellite) :
    angularDifferential (mass ∘ e) (theta ∘ e) (u ∘ e) i =
      angularDifferential mass theta u (e i) := by
  rw [angularDifferential_apply_fullSum, angularDifferential_apply_fullSum]
  exact Equiv.sum_comp e (fun j => mass j * kappa |theta j - theta (e i)| * (u (e i) - u j))

/-- The complete constant-kernel assertion with arbitrary original labels.
Ordering is established by an actual finite permutation and all equations
are transported; it is not supplied as an additional hypothesis. -/
theorem angularDifferential_kernel_separated_nonnegative (mass theta u : Satellite → ℝ)
    (hmass : ∀ i, 0 ≤ mass i) (hsum : ∑ i, mass i = 1)
    (htheta : SeparatedSemicircle theta)
    (hroot : ∀ i, coorbitalResidual mass theta i = 0)
    (hlinear : angularDifferential mass theta u = 0) : ∀ i j, u i = u j := by
  obtain ⟨e, harc⟩ := exists_ordered_semicircle_permutation theta htheta
  have hsum' : (∑ i, (mass ∘ e) i) = 1 := (Equiv.sum_comp e mass).trans hsum
  have hroot' : ∀ i, coorbitalResidual (mass ∘ e) (theta ∘ e) i = 0 := by
    intro i
    rw [coorbitalResidual_reindex]
    exact hroot (e i)
  have hlinear' : angularDifferential (mass ∘ e) (theta ∘ e) (u ∘ e) = 0 := by
    funext i
    rw [angularDifferential_reindex_apply]
    exact congrFun hlinear (e i)
  have hconst := angularDifferential_kernel_nonnegative (mass ∘ e) (theta ∘ e) (u ∘ e)
    (fun i => hmass (e i)) hsum' (separatedSemicircle_of_ordered _ harc) harc hroot' hlinear'
  intro i j
  simpa only [Function.comp_apply, Equiv.apply_symm_apply] using hconst (e.symm i) (e.symm j)

theorem angularDifferential_kernel_iff_separated_nonnegative (mass theta u : Satellite → ℝ)
    (hmass : ∀ i, 0 ≤ mass i) (hsum : ∑ i, mass i = 1)
    (htheta : SeparatedSemicircle theta)
    (hroot : ∀ i, coorbitalResidual mass theta i = 0) :
    angularDifferential mass theta u = 0 ↔ ∀ i j, u i = u j := by
  constructor
  · exact angularDifferential_kernel_separated_nonnegative mass theta u hmass hsum htheta hroot
  · intro hconstant
    have hu : u = fun _ => u 0 := by funext i; exact hconstant i 0
    rw [hu]
    exact angularDifferential_constant mass theta (u 0)

theorem deletedAngularJacobian_isUnit_separated_nonnegative (mass theta : Satellite → ℝ)
    (p q : Satellite) (hmass : ∀ i, 0 ≤ mass i) (hsum : ∑ i, mass i = 1)
    (hp : 0 < mass p) (htheta : SeparatedSemicircle theta)
    (hroot : ∀ i, coorbitalResidual mass theta i = 0) :
    IsUnit (deletedAngularJacobian mass theta p q) := by
  exact deletedAngularJacobian_isUnit_of_constant_kernel mass theta p q hp
    (fun u hu => angularDifferential_kernel_separated_nonnegative
      mass theta u hmass hsum htheta hroot hu)

theorem deletedAngularJacobian_det_ne_zero_separated_nonnegative (mass theta : Satellite → ℝ)
    (p q : Satellite) (hmass : ∀ i, 0 ≤ mass i) (hsum : ∑ i, mass i = 1)
    (hp : 0 < mass p) (htheta : SeparatedSemicircle theta)
    (hroot : ∀ i, coorbitalResidual mass theta i = 0) :
    (deletedAngularJacobian mass theta p q).det ≠ 0 := by
  exact ((Matrix.isUnit_iff_isUnit_det _).mp
    (deletedAngularJacobian_isUnit_separated_nonnegative mass theta p q hmass hsum hp htheta hroot)).ne_zero

/-- Full Proposition `prop:closed`: the derivative of the actual divided
equations, its exact constant kernel, all permitted deleted inverses, and
the uniform inverse assertion. Closed sets use the manuscript's ordered
translation gauge theta 0 = 0; the pointwise assertion is label independent. -/
theorem coorbital_closed_mass_jacobian_complete :
    (∀ mass theta : Satellite → ℝ,
      (∀ i, 0 ≤ mass i) → (∑ i, mass i) = 1 →
      SeparatedSemicircle theta → (∀ i, coorbitalResidual mass theta i = 0) →
      HasFDerivAt (fun angles i => coorbitalResidual mass angles i)
        (angularDifferential mass theta) theta ∧
      (∀ u, angularDifferential mass theta u = 0 ↔ ∀ i j, u i = u j) ∧
      (∀ p q, 0 < mass p → IsUnit (deletedAngularJacobian mass theta p q))) ∧
    (∀ (K : Set ((Satellite → ℝ) × (Satellite → ℝ))) (delta eta : ℝ)
      (p q : Satellite), IsClosed K → 0 < delta → 0 < eta →
      (∀ z ∈ K, (∀ i, 0 ≤ z.1 i) ∧ (∑ i, z.1 i) = 1 ∧ z.2 0 = 0 ∧
        (∀ i : Fin 3, delta ≤ z.2 i.succ - z.2 i.castSucc) ∧
        z.2 3 - z.2 0 ≤ Real.pi - eta ∧ (1 / 4 : ℝ) ≤ z.1 p ∧
        (∀ i, coorbitalResidual z.1 z.2 i = 0)) →
      ∃ C : ℝ, 0 < C ∧ ∀ z ∈ K, ‖(deletedAngularJacobian z.1 z.2 p q)⁻¹‖ ≤ C) := by
  constructor
  · intro mass theta hm hs ht hr
    exact ⟨coorbitalResidual_hasFDerivAt mass theta ht,
      fun u => angularDifferential_kernel_iff_separated_nonnegative mass theta u hm hs ht hr,
      fun p q hp => deletedAngularJacobian_isUnit_separated_nonnegative mass theta p q hm hs hp ht hr⟩
  · exact deletedAngularJacobian_inverse_uniform_on_closed_roots

end DominantFiveBody
