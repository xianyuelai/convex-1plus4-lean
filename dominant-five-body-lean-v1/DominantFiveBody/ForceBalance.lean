import DominantFiveBody.Coordinates

/-! # Pair cancellation and recovery of multiplier-one equations

This verifies the force-balance hinge following `eq:G` in §3. Physical use of
these equations assumes collision freedom; cancellation itself is an algebraic
identity even for Lean's total division operation.
-/

noncomputable section
open scoped BigOperators

namespace DominantFiveBody

def pairForce (m : MassVector) (x : Configuration) (i j : Label) : Plane :=
  (m i * m j / pairDistance x i j ^ 3) • (x j - x i)

@[simp] theorem pairForce_self (m : MassVector) (x : Configuration) (i : Label) :
    pairForce m x i i = 0 := by simp [pairForce]

theorem pairForce_reverse (m : MassVector) (x : Configuration) (i j : Label) :
    pairForce m x j i = -pairForce m x i j := by
  unfold pairForce pairDistance
  rw [norm_sub_rev (x j) (x i), mul_comm (m j) (m i)]
  calc
    (m i * m j / ‖x i - x j‖ ^ 3) • (x i - x j) =
        (m i * m j / ‖x i - x j‖ ^ 3) • (-(x j - x i)) := by congr 1; abel
    _ = -((m i * m j / ‖x i - x j‖ ^ 3) • (x j - x i)) := smul_neg _ _

theorem weighted_acceleration_as_pair_sum (m : MassVector) (x : Configuration)
    (i : Label) : m i • acceleration m x i = ∑ j, pairForce m x i j := by
  simp [acceleration, Finset.smul_sum, smul_smul, mul_div_assoc,
    pairForce, Finset.sum_erase_eq_sub]

/-- §3, after `eq:G`: internal Newtonian forces cancel in the mass-weighted sum. -/
theorem weighted_acceleration_zero (m : MassVector) (x : Configuration) :
    (∑ i, m i • acceleration m x i) = 0 := by
  simp_rw [weighted_acceleration_as_pair_sum]
  have hneg : (∑ i, ∑ j, pairForce m x i j) =
      -(∑ i, ∑ j, pairForce m x i j) := by
    calc
      (∑ i, ∑ j, pairForce m x i j) = ∑ j, ∑ i, pairForce m x i j :=
        Finset.sum_comm
      _ = -(∑ j, ∑ i, pairForce m x j i) := by
        rw [← Finset.sum_neg_distrib]
        apply Finset.sum_congr rfl
        intro j _
        rw [← Finset.sum_neg_distrib]
        apply Finset.sum_congr rfl
        intro i _
        exact pairForce_reverse m x j i
  have htwice : (2 : ℝ) • (∑ i, ∑ j, pairForce m x i j) = 0 := by
    rw [two_smul]
    exact eq_neg_iff_add_eq_zero.mp hneg
  exact (smul_eq_zero.mp htwice).resolve_left (by norm_num)

/-- Differences with the primary recover all centered multiplier-one equations.
The nonzero total mass is checked explicitly; no omitted zero-mass angular row
is restored by an invalid division. -/
theorem normalized_of_primary_differences (m : MassVector) (x : Configuration)
    (hm : totalMass m ≠ 0) (hcollision : CollisionFree x)
    (hcenter : weightedPosition m x = 0)
    (hdiff : ∀ i, acceleration m x i - acceleration m x 0 = -(x i - x 0)) :
    NormalizedCentralConfiguration m x := by
  have hsame : ∀ i, acceleration m x i + x i = acceleration m x 0 + x 0 := by
    intro i
    have hi := hdiff i
    apply sub_eq_zero.mp
    calc
      acceleration m x i + x i - (acceleration m x 0 + x 0) =
          (acceleration m x i - acceleration m x 0) + (x i - x 0) := by abel
      _ = 0 := by rw [hi]; abel
  have hweighted : (∑ i, m i • (acceleration m x i + x i)) = 0 := by
    simp only [smul_add, Finset.sum_add_distrib, weighted_acceleration_zero]
    simpa only [zero_add, weightedPosition] using hcenter
  have hres : acceleration m x 0 + x 0 = 0 := by
    simp_rw [hsame] at hweighted
    rw [← Finset.sum_smul] at hweighted
    exact (smul_eq_zero.mp hweighted).resolve_left hm
  refine ⟨hcollision, hcenter, ?_⟩
  intro i
  exact eq_neg_of_add_eq_zero_left ((hsame i).trans hres)

end DominantFiveBody
