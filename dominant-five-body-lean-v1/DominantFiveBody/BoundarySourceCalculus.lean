import DominantFiveBody.BoundaryJacobian
import DominantFiveBody.CoorbitalSkewRank

/-! The precise limiting lower bound and block entries in Proposition 2.4.
The positivity conclusion alone does not replace these source formulas. -/
noncomputable section
open scoped BigOperators
namespace DominantFiveBody
open Coorbital

theorem three_source_probe_remainder_lower_bound (mass theta : Satellite → ℝ) (k : Satellite)
    (hzero : mass k = 0) (hmass : ∀ i, i ≠ k → 0 < mass i)
    (htheta : SeparatedSemicircle theta)
    (harc : ∀ i j, i < j → 0 < theta j - theta i ∧ theta j - theta i < Real.pi)
    (hroot : ∀ i, coorbitalResidual mass theta i = 0) :
    (∑ j ∈ Finset.univ.erase k, mass j * positiveRemainder |theta j-theta k|) ≤
      angularJacobian mass theta k k ∧
    0 < ∑ j ∈ Finset.univ.erase k, mass j * positiveRemainder |theta j-theta k| := by
  obtain ⟨nu, hnuk, hnuroot⟩ := coorbital_three_source_kernel_vector_by_rank mass theta k hzero hmass harc hroot
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
  refine ⟨?_,hbremainder⟩
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

theorem angularJacobian_zero_mass_column (mass theta : Satellite → ℝ)
    (i j : Satellite) (hij : i≠j) (hm : mass j=0) :
    angularJacobian mass theta i j=0 := by
  simp [angularJacobian,hij,hm]

theorem angularJacobian_zero_support_diagonal (mass theta : Satellite → ℝ)
    (k : Satellite) (hk : mass k=0) :
    angularJacobian mass theta k k =
      ∑ j ∈ Finset.univ.filter (fun j => mass j≠0), mass j*kappa |theta j-theta k| := by
  classical
  rw [angularJacobian,if_pos rfl,Finset.sum_erase_eq_sub (Finset.mem_univ k)]
  simp only [hk,zero_mul,sub_zero,Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro j _
  by_cases hj : mass j=0 <;> simp [hj]

end DominantFiveBody
