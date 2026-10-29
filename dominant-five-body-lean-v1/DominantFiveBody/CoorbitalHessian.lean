import DominantFiveBody.CycleEstimate
import Mathlib.Analysis.Calculus.FDeriv.Add
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Analysis.Calculus.FDeriv.CompCLM

/-! # The physical angular Hessian in Lemma 2.1

The chord-distance potential from the manuscript is identified with its scalar
pair potential before differentiating. The second differential refers to
`fderiv` of that physical potential, and is not a separate assumed matrix.
-/

noncomputable section
open scoped BigOperators
open Filter Set Topology

namespace DominantFiveBody
open Coorbital

theorem unit_circle_chord_sq (a b : ℝ) :
    ‖point (Real.cos a) (Real.sin a) - point (Real.cos b) (Real.sin b)‖^2 =
      (2 * Real.sin ((b-a)/2))^2 := by
  rw [EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_two]
  simp only [PiLp.sub_apply, point, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_fin_one]
  have ha := Real.sin_sq_add_cos_sq a
  have hb := Real.sin_sq_add_cos_sq b
  have hd := Real.cos_sub b a
  have hh := cos_half_identity (b-a)
  nlinarith

/-- Positive semicircle separations justify the sign of the chord length. -/
theorem unit_circle_chord (a b : ℝ) (hab : 0 < b-a) (hpi : b-a < Real.pi) :
    ‖point (Real.cos a) (Real.sin a) - point (Real.cos b) (Real.sin b)‖ =
      2 * Real.sin ((b-a)/2) := by
  have hp : 0 ≤ 2 * Real.sin ((b-a)/2) := (mul_pos (by norm_num) (sin_half_pos hab hpi)).le
  exact (sq_eq_sq₀ (norm_nonneg _) hp).mp (unit_circle_chord_sq a b)

def OrderedSemicircle {n : ℕ} (theta : Fin n → ℝ) : Prop :=
  ∀ i j, i < j → 0 < theta j-theta i ∧ theta j-theta i < Real.pi

theorem orderedSemicircle_of_coorbitalAngleDomain (theta : Satellite → ℝ)
    (htheta : CoorbitalAngleDomain theta) : OrderedSemicircle theta := by
  intro i j hij
  have hmin : theta 0 ≤ theta i := by
    rcases eq_or_lt_of_le (Fin.zero_le i) with hi | hi
    · rw [← hi]
    · exact (htheta.2.1 0 i hi).le
  have hmax : theta j ≤ theta 3 := by
    have hj : j ≤ (3 : Satellite) := by omega
    rcases lt_or_eq_of_le hj with hj | hj
    · exact (htheta.2.1 j 3 hj).le
    · rw [hj]
  exact ⟨sub_pos.mpr (htheta.2.1 i j hij), by linarith [htheta.1, htheta.2.2]⟩

def angleDifference {n : ℕ} (i j : Fin n) : (Fin n → ℝ) →L[ℝ] ℝ :=
  (ContinuousLinearMap.proj j : (Fin n → ℝ) →L[ℝ] ℝ) - ContinuousLinearMap.proj i

@[simp] theorem angleDifference_apply {n : ℕ} (i j : Fin n) (u : Fin n → ℝ) :
    angleDifference i j u = u j-u i := rfl

def angularPotential {n : ℕ} (mass theta : Fin n → ℝ) : ℝ :=
  ∑ i, ∑ j, if i < j then mass i*mass j*pairPotential (theta j-theta i) else 0

/-- Formula (2.2) for the actual chord-distance potential on its open domain. -/
theorem coorbitalPotential_eq_angularPotential (mass theta : Satellite → ℝ)
    (harc : OrderedSemicircle theta) :
    coorbitalPotential mass theta = angularPotential mass theta := by
  unfold coorbitalPotential satellitePairs
  rw [Finset.sum_filter, Fintype.sum_prod_type]
  unfold angularPotential
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  split_ifs with hij
  · obtain ⟨ht,hpi⟩ := harc i j hij
    have hc : coorbitalDistance theta i j = 2 * Real.sin ((theta j-theta i)/2) :=
      unit_circle_chord (theta i) (theta j) ht hpi
    rw [hc]
    unfold pairPotential
    rw [cos_half_identity (theta j-theta i)]
    ring
  · rfl

def angularPotentialDerivative {n : ℕ} (mass theta : Fin n → ℝ) :
    (Fin n → ℝ) →L[ℝ] ℝ :=
  ∑ i, ∑ j, if i < j then
    (-(mass i*mass j) * kernelF (theta j-theta i)) • angleDifference i j else 0

def angularHessianMap {n : ℕ} (mass theta : Fin n → ℝ) :
    (Fin n → ℝ) →L[ℝ] (Fin n → ℝ) →L[ℝ] ℝ :=
  ∑ i, ∑ j, if i < j then
    (mass i*mass j*kappa (theta j-theta i)) •
      ((angleDifference i j).smulRight (angleDifference i j)) else 0

theorem angularPotential_hasFDerivAt {n : ℕ} (mass theta : Fin n → ℝ)
    (harc : OrderedSemicircle theta) :
    HasFDerivAt (angularPotential mass) (angularPotentialDerivative mass theta) theta := by
  unfold angularPotential angularPotentialDerivative
  apply HasFDerivAt.fun_sum
  intro i _
  apply HasFDerivAt.fun_sum
  intro j _
  by_cases hij : i < j
  · simp only [if_pos hij]
    have hd := (pairPotential_hasDerivAt (harc i j hij).1 (harc i j hij).2).comp_hasFDerivAt
      (f := fun angles : Fin n → ℝ => angles j-angles i) theta
      (angleDifference i j).hasFDerivAt
    convert! hd.const_mul (mass i*mass j) using 1
    ext u
    simp only [smul_apply, smul_eq_mul]
    ring
  · simp only [if_neg hij]
    exact hasFDerivAt_const _ _

theorem isOpen_orderedSemicircle (n : ℕ) :
    IsOpen {theta : Fin n → ℝ | OrderedSemicircle theta} := by
  simp only [OrderedSemicircle, Set.ofPred_forall]
  apply isOpen_iInter_of_finite
  intro i
  apply isOpen_iInter_of_finite
  intro j
  apply isOpen_iInter_of_finite
  intro _
  have h1 : IsOpen {a : Fin n → ℝ | 0 < angleDifference i j a} :=
    isOpen_lt continuous_const (angleDifference i j).continuous
  have h2 : IsOpen {a : Fin n → ℝ | angleDifference i j a < Real.pi} :=
    isOpen_lt (angleDifference i j).continuous continuous_const
  exact h1.inter h2

theorem angularPotential_fderiv {n : ℕ} (mass theta : Fin n → ℝ)
    (harc : OrderedSemicircle theta) :
    fderiv ℝ (angularPotential mass) theta = angularPotentialDerivative mass theta :=
  (angularPotential_hasFDerivAt mass theta harc).fderiv

theorem angularPotentialDerivative_hasFDerivAt {n : ℕ} (mass theta : Fin n → ℝ)
    (harc : OrderedSemicircle theta) :
    HasFDerivAt (angularPotentialDerivative mass) (angularHessianMap mass theta) theta := by
  unfold angularPotentialDerivative angularHessianMap
  apply HasFDerivAt.fun_sum
  intro i _
  apply HasFDerivAt.fun_sum
  intro j _
  by_cases hij : i < j
  · simp only [if_pos hij]
    have hd := (kernelF_hasDerivAt (harc i j hij).1 (harc i j hij).2).comp_hasFDerivAt
      (f := fun angles : Fin n → ℝ => angles j-angles i) theta
      (angleDifference i j).hasFDerivAt
    convert! (hd.const_mul (-(mass i*mass j))).smul_const (angleDifference i j) using 1
    ext u v
    simp only [ContinuousLinearMap.smulRight_apply, smul_apply,
      smul_eq_mul]
    ring
  · simp only [if_neg hij]
    exact hasFDerivAt_const _ _

theorem angularPotential_second_fderiv {n : ℕ} (mass theta : Fin n → ℝ)
    (harc : OrderedSemicircle theta) :
    fderiv ℝ (fderiv ℝ (angularPotential mass)) theta = angularHessianMap mass theta := by
  have hnear : ∀ᶠ angles in nhds theta, OrderedSemicircle angles :=
    (isOpen_orderedSemicircle n).mem_nhds harc
  have heq : fderiv ℝ (angularPotential mass) =ᶠ[nhds theta] angularPotentialDerivative mass :=
    hnear.mono (fun angles ha => angularPotential_fderiv mass angles ha)
  exact ((angularPotentialDerivative_hasFDerivAt mass theta harc).congr_of_eventuallyEq heq).fderiv

def coorbitalPhysicalHessian (mass theta u v : Satellite → ℝ) : ℝ :=
  (fderiv ℝ (fderiv ℝ (coorbitalPotential mass)) theta) u v

/-- Neighborhood equality is used at both derivative levels. -/
theorem coorbitalPhysicalHessian_eq_map (mass theta u v : Satellite → ℝ)
    (harc : OrderedSemicircle theta) :
    coorbitalPhysicalHessian mass theta u v = angularHessianMap mass theta u v := by
  have hnear : ∀ᶠ angles in nhds theta, OrderedSemicircle angles :=
    (isOpen_orderedSemicircle 4).mem_nhds harc
  have heq : coorbitalPotential mass =ᶠ[nhds theta] angularPotential mass :=
    hnear.mono (fun angles ha => coorbitalPotential_eq_angularPotential mass angles ha)
  have hdeq : fderiv ℝ (coorbitalPotential mass) =ᶠ[nhds theta]
      fderiv ℝ (angularPotential mass) := heq.fderiv
  unfold coorbitalPhysicalHessian
  rw [hdeq.fderiv_eq, angularPotential_second_fderiv mass theta harc]

theorem angularHessianMap_apply {n : ℕ} (mass theta u v : Fin n → ℝ) :
    angularHessianMap mass theta u v =
      ∑ i, ∑ j, if i < j then
        mass i*mass j*kappa (theta j-theta i)*(u j-u i)*(v j-v i) else 0 := by
  simp only [angularHessianMap, sum_apply]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  split_ifs
  · simp only [smul_apply, ContinuousLinearMap.smulRight_apply, smul_eq_mul,
      angleDifference_apply]
    ring
  · simp

theorem angularHessianMap_self {n : ℕ} (mass theta u : Fin n → ℝ) :
    angularHessianMap mass theta u u = coorbitalKappaForm mass theta u := by
  rw [angularHessianMap_apply]
  unfold coorbitalKappaForm weightedAngleForm pairForm
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  split_ifs <;> ring

theorem coorbitalPhysicalHessian_self (mass theta u : Satellite → ℝ)
    (harc : OrderedSemicircle theta) :
    coorbitalPhysicalHessian mass theta u u = coorbitalKappaForm mass theta u := by
  rw [coorbitalPhysicalHessian_eq_map mass theta u u harc, angularHessianMap_self]

theorem angularHessianMap_constant_left {n : ℕ} (mass theta v : Fin n → ℝ) (c : ℝ) :
    angularHessianMap mass theta (fun _ => c) v = 0 := by
  simp [angularHessianMap_apply]

theorem angularHessianMap_constant_right {n : ℕ} (mass theta u : Fin n → ℝ) (c : ℝ) :
    angularHessianMap mass theta u (fun _ => c) = 0 := by
  simp [angularHessianMap_apply]

/-- The actual physical Hessian has precisely the rotational constant kernel
at a positive-mass root, as asserted in Lemma 2.1. -/
theorem coorbitalPhysicalHessian_kernel_iff (mass theta u : Satellite → ℝ)
    (hm : ∀ i, 0 < mass i) (harc : OrderedSemicircle theta)
    (hroot : ∀ i, angularEquation mass theta i = 0) :
    (∀ v, coorbitalPhysicalHessian mass theta u v = 0) ↔ ∀ i j, u i = u j := by
  constructor
  · intro hker
    by_contra hnonconstant
    have hp := coorbitalKappaForm_pos_at_root (by decide : 2 ≤ 4) (le_refl 4)
      mass theta u hm harc hroot hnonconstant
    rw [← coorbitalPhysicalHessian_self mass theta u harc, hker u] at hp
    exact (lt_irrefl 0) hp
  · intro hconstant v
    have hu : u = fun _ => u 0 := funext (fun i => hconstant i 0)
    rw [coorbitalPhysicalHessian_eq_map mass theta u v harc, hu,
      angularHessianMap_constant_left]

theorem coorbitalPhysicalHessian_pos_on_slice (mass theta u : Satellite → ℝ) (p : Satellite)
    (hm : ∀ i, 0 < mass i) (harc : OrderedSemicircle theta)
    (hroot : ∀ i, angularEquation mass theta i = 0) (hp : u p = 0) (hu : u ≠ 0) :
    0 < coorbitalPhysicalHessian mass theta u u := by
  rw [coorbitalPhysicalHessian_self mass theta u harc]
  exact coorbitalKappaForm_pos_on_slice_at_root (by decide : 2 ≤ 4) (le_refl 4)
    mass theta u p hm harc hroot hp hu

/-- The original model's positive-mass divided equations and anchored angle
domain instantiate the kernel result, with no alternative root predicate. -/
theorem coorbital_hessian_kernel (mass theta u : Satellite → ℝ)
    (hm : ∀ i, 0 < mass i) (htheta : CoorbitalAngleDomain theta)
    (hroot : ∀ i, coorbitalResidual mass theta i = 0) :
    (∀ v, coorbitalPhysicalHessian mass theta u v = 0) ↔ ∀ i j, u i=u j := by
  apply coorbitalPhysicalHessian_kernel_iff mass theta u hm
    (orderedSemicircle_of_coorbitalAngleDomain theta htheta)
  intro i
  rw [angularEquation_eq_coorbitalResidual, hroot i]

theorem coorbital_hessian_positive_on_slice (mass theta u : Satellite → ℝ) (p : Satellite)
    (hm : ∀ i, 0 < mass i) (htheta : CoorbitalAngleDomain theta)
    (hroot : ∀ i, coorbitalResidual mass theta i = 0) (hp : u p=0) (hu : u≠0) :
    0 < coorbitalPhysicalHessian mass theta u u := by
  apply coorbitalPhysicalHessian_pos_on_slice mass theta u p hm
    (orderedSemicircle_of_coorbitalAngleDomain theta htheta) _ hp hu
  intro i
  rw [angularEquation_eq_coorbitalResidual, hroot i]

/-- The same physical chord potential for the two- and three-source versions
of Lemma 2.1. This contains no equilibrium or nondegeneracy requirements. -/
def angularChordPotential {n : ℕ} (mass theta : Fin n → ℝ) : ℝ :=
  ∑ i, ∑ j, if i < j then mass i*mass j*
    ((‖point (Real.cos (theta i)) (Real.sin (theta i)) -
      point (Real.cos (theta j)) (Real.sin (theta j))‖)⁻¹ +
    ‖point (Real.cos (theta i)) (Real.sin (theta i)) -
      point (Real.cos (theta j)) (Real.sin (theta j))‖^2/2) else 0

theorem angularChordPotential_eq {n : ℕ} (mass theta : Fin n → ℝ)
    (harc : OrderedSemicircle theta) :
    angularChordPotential mass theta = angularPotential mass theta := by
  unfold angularChordPotential angularPotential
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  split_ifs with hij
  · rw [unit_circle_chord (theta i) (theta j) (harc i j hij).1 (harc i j hij).2]
    unfold pairPotential
    rw [cos_half_identity (theta j-theta i)]
    ring
  · rfl

def angularChordHessian {n : ℕ} (mass theta u v : Fin n → ℝ) : ℝ :=
  (fderiv ℝ (fderiv ℝ (angularChordPotential mass)) theta) u v

theorem angularChordHessian_eq_map {n : ℕ} (mass theta u v : Fin n → ℝ)
    (harc : OrderedSemicircle theta) :
    angularChordHessian mass theta u v = angularHessianMap mass theta u v := by
  have hnear : ∀ᶠ angles in nhds theta, OrderedSemicircle angles :=
    (isOpen_orderedSemicircle n).mem_nhds harc
  have heq : angularChordPotential mass =ᶠ[nhds theta] angularPotential mass :=
    hnear.mono (fun angles ha => angularChordPotential_eq mass angles ha)
  have hdeq : fderiv ℝ (angularChordPotential mass) =ᶠ[nhds theta]
      fderiv ℝ (angularPotential mass) := heq.fderiv
  unfold angularChordHessian
  rw [hdeq.fderiv_eq, angularPotential_second_fderiv mass theta harc]

theorem angularChordHessian_kernel_iff {n : ℕ} (hn₂ : 2 ≤ n) (hn₄ : n ≤ 4)
    (mass theta u : Fin n → ℝ)
    (hm : ∀ i, 0 < mass i) (harc : OrderedSemicircle theta)
    (hroot : ∀ i, angularEquation mass theta i = 0) :
    (∀ v, angularChordHessian mass theta u v = 0) ↔ ∀ i j, u i = u j := by
  constructor
  · intro hker
    by_contra hnonconstant
    have hp := coorbitalKappaForm_pos_at_root hn₂ hn₄ mass theta u hm harc hroot hnonconstant
    rw [← angularHessianMap_self, ← angularChordHessian_eq_map mass theta u u harc,
      hker u] at hp
    exact (lt_irrefl 0) hp
  · intro hconstant v
    obtain ⟨p⟩ : Nonempty (Fin n) := ⟨⟨0, by omega⟩⟩
    have hu : u = fun _ => u p := funext (fun i => hconstant i p)
    rw [angularChordHessian_eq_map mass theta u v harc, hu,
      angularHessianMap_constant_left]

/-- The complete mathematical assertion of Lemma 2.1, including the actual
second differential of the physical chord potential for every allowed N.
The scalar proof uses the mean value theorem; cycle decomposition is explicit
for the finite sizes, and no circulation estimate is assumed. -/
theorem angular_hessian_estimate {n : ℕ} (hn₂ : 2 ≤ n) (hn₄ : n ≤ 4)
    (mass theta : Fin n → ℝ)
    (hm : ∀ i, 0 < mass i) (harc : OrderedSemicircle theta)
    (hroot : ∀ i, angularEquation mass theta i = 0) :
    (∀ i j, i < j → 0 < positiveRemainder (theta j-theta i)) ∧
    (∀ u, angularChordHessian mass theta u u = coorbitalKappaForm mass theta u ∧
      coorbitalRemainderForm mass theta u ≤ angularChordHessian mass theta u u) ∧
    (∀ u, (∀ v, angularChordHessian mass theta u v = 0) ↔ ∀ i j, u i = u j) := by
  refine ⟨fun i j hij => positiveRemainder_pos (harc i j hij).1 (harc i j hij).2,
    ?_, fun u => angularChordHessian_kernel_iff hn₂ hn₄ mass theta u hm harc hroot⟩
  intro u
  have heq : angularChordHessian mass theta u u = coorbitalKappaForm mass theta u := by
    rw [angularChordHessian_eq_map mass theta u u harc, angularHessianMap_self]
  exact ⟨heq, heq.symm ▸ coorbital_cycle_bound hn₂ hn₄ mass theta u hm harc hroot⟩

end DominantFiveBody
