import DominantFiveBody.CoorbitalCompactness

/-! The literal cut identities and negative-term bound used in the original
properness proof of Theorem 2.2. -/
noncomputable section
open scoped BigOperators
namespace DominantFiveBody
open Coorbital

theorem coorbital_cut_flow (mass theta : Satellite → ℝ)
    (hroot : ∀ i,angularEquation mass theta i=0) (k : Fin 3) :
    (∑ i : Satellite,∑ j : Satellite,
      if i.val≤k.val ∧ k.val<j.val then angularFlow mass theta i j else 0)=0 := by
  obtain ⟨h0,h1,h2⟩ := four_flow_balance mass theta hroot
  fin_cases k <;> norm_num [Fin.sum_univ_four] <;> (try simp at *) <;> linarith

theorem coorbital_cut (mass theta : Satellite → ℝ) (ha : OrderedSemicircle theta)
    (hroot : ∀ i,angularEquation mass theta i=0) (k : Fin 3) :
    (∑ i : Satellite,∑ j : Satellite,
      if i.val≤k.val ∧ k.val<j.val then
        mass i*mass j*kernelF (theta j-theta i) else 0)=0 := by
  trans ∑ i : Satellite,∑ j : Satellite,
    if i.val≤k.val ∧ k.val<j.val then angularFlow mass theta i j else 0
  · apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    split_ifs with hij
    · exact (angularFlow_positive_formula mass theta i j (ha i j (by omega)).1).symm
    · rfl
  · exact coorbital_cut_flow mass theta hroot k

theorem coorbital_negative_terms_lower_bound (mass theta : Satellite → ℝ)
    (hm : PositiveRatio mass) (ha : OrderedSemicircle theta) :
    -Real.pi/2 ≤ ∑ i : Satellite,∑ j : Satellite,
      if i<j then min (mass i*mass j*(theta j-theta i)*kernelF (theta j-theta i)) 0 else 0 := by
  have hterm (i j : Satellite) :
      (if i<j then -Real.pi*(mass i*mass j) else 0) ≤
      (if i<j then min (mass i*mass j*(theta j-theta i)*kernelF (theta j-theta i)) 0 else 0) := by
    split_ifs with hij
    · have ht := ha i j hij
      have hmij : 0<mass i*mass j := mul_pos (hm.1 i) (hm.1 j)
      have htf : -Real.pi≤(theta j-theta i)*kernelF (theta j-theta i) := by
        have hh := mul_le_mul_of_nonneg_left (kernelF_ge_neg_one ht.1 ht.2) ht.1.le
        linarith
      have hh := mul_le_mul_of_nonneg_left htf hmij.le
      exact le_min (by nlinarith) (by nlinarith [Real.pi_pos])
    · exact le_rfl
  have hs := Finset.sum_le_sum (s := Finset.univ) (fun i _ =>
    Finset.sum_le_sum (s := Finset.univ) (fun j _ => hterm i j))
  have heq : (∑ i : Satellite,∑ j : Satellite,if i<j then -Real.pi*(mass i*mass j) else 0) =
      -Real.pi*satelliteMassPairSum mass := by
    simp only [satelliteMassPairSum,Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    split_ifs <;> simp
  rw [heq] at hs
  have hp := satelliteMassPairSum_le_half mass hm.2
  have hh := mul_le_mul_of_nonpos_left hp (neg_nonpos.mpr Real.pi_pos.le)
  linarith

end DominantFiveBody
