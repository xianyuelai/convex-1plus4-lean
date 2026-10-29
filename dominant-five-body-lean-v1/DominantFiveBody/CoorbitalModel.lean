import DominantFiveBody.Definitions
import DominantFiveBody.Coorbital

/-! # Signed coorbital equations, with an explicit odd extension

The positive-argument formula alone is not odd when substituted at negative
angles. This module is the manuscript's signed `f`, matrix `A`, equations `E`,
and physical coorbital potential `V`. Analytic results in `Coorbital.lean` apply
to positive separations; their transfer to all matrix entries is separate.
-/

noncomputable section
open scoped BigOperators

namespace DominantFiveBody

/-- Equation `eq:angle-domain`, anchored first satellite, all points in a semicircle. -/
def CoorbitalAngleDomain (θ : Satellite → ℝ) : Prop :=
  θ 0 = 0 ∧ (∀ i j, i < j → θ i < θ j) ∧ θ 3 < Real.pi

/-- The paper's odd extension of its positive-angle formula `eq:kernel`. -/
def coorbitalKernel (t : ℝ) : ℝ :=
  if 0 ≤ t then Coorbital.kernelF t else -Coorbital.kernelF (-t)

def coorbitalMatrix (θ : Satellite → ℝ) : Matrix Satellite Satellite ℝ :=
  fun i j => if i = j then 0 else coorbitalKernel (θ j - θ i)

/-- Equation `eq:co-equations`, with all four probe equations retained. -/
def coorbitalResidual (μ θ : Satellite → ℝ) (i : Satellite) : ℝ :=
  ∑ j ∈ Finset.univ.erase i, μ j * coorbitalKernel (θ j - θ i)

def satellitePairs : Finset (Satellite × Satellite) :=
  Finset.univ.filter (fun p => p.1 < p.2)

def coorbitalDistance (θ : Satellite → ℝ) (i j : Satellite) : ℝ :=
  ‖point (Real.cos (θ i)) (Real.sin (θ i)) -
    point (Real.cos (θ j)) (Real.sin (θ j))‖

/-- Physical `V` in equation `eq:co-equations`, including the chord-distance term. -/
def coorbitalPotential (μ θ : Satellite → ℝ) : ℝ :=
  ∑ p ∈ satellitePairs,
    μ p.1 * μ p.2 *
      ((coorbitalDistance θ p.1 p.2)⁻¹ + coorbitalDistance θ p.1 p.2 ^ 2 / 2)

@[simp] theorem coorbitalKernel_zero : coorbitalKernel 0 = 0 := by
  simp [coorbitalKernel, Coorbital.kernelF]

theorem coorbitalKernel_eq_positive_formula (t : ℝ) (ht : 0 ≤ t) :
    coorbitalKernel t = Coorbital.kernelF t := by
  simp [coorbitalKernel, ht]

/-- The signed kernel is actually odd, including its zero value. -/
theorem coorbitalKernel_neg (t : ℝ) : coorbitalKernel (-t) = -coorbitalKernel t := by
  rcases lt_trichotomy t 0 with hneg | hzero | hpos
  · simp [coorbitalKernel, not_le.mpr hneg, le_of_lt (neg_pos.mpr hneg)]
  · subst t
    simp
  · simp [coorbitalKernel, le_of_lt hpos, not_le.mpr (neg_neg_of_pos hpos)]

/-- Equation `eq:co-equations`: the actual signed matrix is antisymmetric. -/
theorem coorbitalMatrix_reverse (θ : Satellite → ℝ) (i j : Satellite) :
    coorbitalMatrix θ j i = -coorbitalMatrix θ i j := by
  by_cases hij : i = j
  · subst j
    simp [coorbitalMatrix]
  · simp only [coorbitalMatrix, if_neg hij, if_neg (Ne.symm hij)]
    rw [show θ i - θ j = -(θ j - θ i) by ring]
    exact coorbitalKernel_neg _

/-- All four divided equations are the rows of the actual signed matrix `Aμ`. -/
theorem coorbitalResidual_eq_matrix_sum (μ θ : Satellite → ℝ) (i : Satellite) :
    coorbitalResidual μ θ i = ∑ j, μ j * coorbitalMatrix θ i j := by
  classical
  simp [coorbitalResidual, coorbitalMatrix, Finset.sum_erase_eq_sub]
  apply Finset.sum_congr rfl
  intro j _
  by_cases hij : i = j
  · subst j
    simp
  · simp [hij]

def coorbitalWeightedPair (μ θ : Satellite → ℝ) (i j : Satellite) : ℝ :=
  μ i * μ j * coorbitalMatrix θ i j

theorem coorbitalWeightedPair_reverse (μ θ : Satellite → ℝ) (i j : Satellite) :
    coorbitalWeightedPair μ θ j i = -coorbitalWeightedPair μ θ i j := by
  rw [coorbitalWeightedPair, coorbitalWeightedPair, coorbitalMatrix_reverse]
  ring

/-- Equation `eq:co-equations`: `∑ μᵢ Eᵢ=0` is true even at zero ratios. -/
theorem coorbital_weightedResidual_zero (μ θ : Satellite → ℝ) :
    (∑ i, μ i * coorbitalResidual μ θ i) = 0 := by
  simp_rw [coorbitalResidual_eq_matrix_sum, Finset.mul_sum, ← mul_assoc]
  change (∑ i, ∑ j, coorbitalWeightedPair μ θ i j) = 0
  have hneg : (∑ i, ∑ j, coorbitalWeightedPair μ θ i j) =
      -(∑ i, ∑ j, coorbitalWeightedPair μ θ i j) := by
    calc
      (∑ i, ∑ j, coorbitalWeightedPair μ θ i j) =
          ∑ j, ∑ i, coorbitalWeightedPair μ θ i j := Finset.sum_comm
      _ = -(∑ j, ∑ i, coorbitalWeightedPair μ θ j i) := by
        rw [← Finset.sum_neg_distrib]
        apply Finset.sum_congr rfl
        intro j _
        rw [← Finset.sum_neg_distrib]
        apply Finset.sum_congr rfl
        intro i _
        exact coorbitalWeightedPair_reverse μ θ j i
  linarith

/-- §2 `prop:closed`: recovering a deleted row REQUIRES a positive mass in it.
The other three masses may be zero, and their probe equations are retained. -/
theorem coorbital_recover_positive_mass_row (μ θ : Satellite → ℝ)
    (p : Satellite) (hμp : 0 < μ p)
    (hothers : ∀ i, i ≠ p → coorbitalResidual μ θ i = 0) :
    coorbitalResidual μ θ p = 0 := by
  have hsum : (∑ i, μ i * coorbitalResidual μ θ i) =
      μ p * coorbitalResidual μ θ p := by
    apply Finset.sum_eq_single p
    · intro i _ hip
      rw [hothers i hip, mul_zero]
    · simp
  rw [coorbital_weightedResidual_zero] at hsum
  exact (mul_eq_zero.mp hsum.symm).resolve_left (ne_of_gt hμp)

end DominantFiveBody
