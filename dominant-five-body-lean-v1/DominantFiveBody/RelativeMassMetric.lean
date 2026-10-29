import DominantFiveBody.RelativeAction
import Mathlib.LinearAlgebra.Matrix.PosDef

/-! # The actual positive definite primary-relative mass matrix

Source: §3, immediately after `eq:action`. The matrix is the same C used in
the proved identity ∇Φ = (C ⊗ I₂)F. The parameter range is ε > -1, and no
positive lower bound on a mass ratio is imposed.
-/

noncomputable section
open scoped BigOperators
open Matrix

namespace DominantFiveBody

theorem relativeMassMatrix_mulVec (eps : ℝ) (mu u : Satellite → ℝ) (i : Satellite) :
    (relativeMassMatrix eps mu *ᵥ u) i =
      mu i*(u i-(eps/(1+eps))*(∑ j, mu j*u j)) := by
  simp only [Matrix.mulVec, dotProduct, relativeMassMatrix, sub_mul, Finset.sum_sub_distrib]
  have hdiag : (∑ j, (if i=j then mu i else 0)*u j)=mu i*u i := by simp
  rw [hdiag]
  simp_rw [mul_assoc]
  rw [← Finset.mul_sum, ← Finset.mul_sum]
  ring

theorem relativeMassMatrix_dotProduct (eps : ℝ) (mu u : Satellite → ℝ) :
    u ⬝ᵥ (relativeMassMatrix eps mu *ᵥ u) =
      (∑ i, mu i*u i^2) - (eps/(1+eps))*(∑ i, mu i*u i)^2 := by
  simp only [dotProduct, relativeMassMatrix_mulVec, mul_sub, Finset.sum_sub_distrib]
  have h1 : (∑ i, u i*(mu i*u i))=∑ i, mu i*u i^2 := by
    apply Finset.sum_congr rfl
    intro i _
    ring
  have h2 : (∑ i, u i*(mu i*((eps/(1+eps))*(∑ j, mu j*u j)))) =
      (eps/(1+eps))*(∑ i, mu i*u i)^2 := by
    simp_rw [show ∀ i, u i*(mu i*((eps/(1+eps))*(∑ j, mu j*u j))) =
      ((eps/(1+eps))*(∑ j, mu j*u j))*(mu i*u i) from fun i => by ring]
    rw [← Finset.mul_sum]
    ring
  rw [h1, h2]

theorem massWeightedVariance_identity (mu u : Satellite → ℝ) (hsum : ∑ i, mu i=1) :
    (∑ i, mu i*(u i-(∑ j, mu j*u j))^2) =
      (∑ i, mu i*u i^2)-(∑ i, mu i*u i)^2 := by
  simp_rw [sub_sq, mul_add, mul_sub, Finset.sum_add_distrib, Finset.sum_sub_distrib]
  have hcross : (∑ i, mu i*(2*u i*(∑ j, mu j*u j))) = 2*(∑ i, mu i*u i)^2 := by
    simp_rw [show ∀ i, mu i*(2*u i*(∑ j, mu j*u j)) =
      (2*(∑ j, mu j*u j))*(mu i*u i) from fun i => by ring]
    rw [← Finset.mul_sum]
    ring
  rw [hcross, ← Finset.sum_mul, hsum, one_mul]
  ring

theorem relativeMassMatrix_posDef (eps : ℝ) (mu : MassRatio)
    (heps : -1<eps) (hm : ∀ i, 0<mu i) (hsum : ∑ i, mu i=1) :
    (relativeMassMatrix eps mu).PosDef := by
  apply Matrix.PosDef.of_dotProduct_mulVec_pos
  · ext i j
    simp only [Matrix.conjTranspose_apply, star_trivial, relativeMassMatrix]
    by_cases hij : i=j
    · subst j
      rfl
    · simp only [hij, Ne.symm hij, if_false]
      ring
  · intro u hu
    simp only [star_trivial]
    rw [relativeMassMatrix_dotProduct]
    have hden : 0<1+eps := by linarith
    have hvariance : 0≤(∑ i, mu i*u i^2)-(∑ i, mu i*u i)^2 := by
      rw [← massWeightedVariance_identity mu u hsum]
      exact Finset.sum_nonneg fun i _ => mul_nonneg (hm i).le (sq_nonneg _)
    have hsumpos : 0<∑ i, mu i*u i^2 := by
      have hn : ∃ i, u i≠0 := by
        by_contra h
        apply hu
        ext i
        change u i=0
        exact (by simpa only [not_exists, not_not] using h : ∀ j, u j=0) i
      obtain ⟨i, hi⟩ := hn
      exact Finset.sum_pos' (fun j _ => mul_nonneg (hm j).le (sq_nonneg _))
        ⟨i, Finset.mem_univ i, mul_pos (hm i) (sq_pos_of_ne_zero hi)⟩
    by_cases he : 0≤eps
    · have hk : 0≤eps/(1+eps) := div_nonneg he hden.le
      have heq : (∑ i, mu i*u i^2)-(eps/(1+eps))*(∑ i, mu i*u i)^2 =
          (∑ i, mu i*u i^2)/(1+eps)+(eps/(1+eps))*
            ((∑ i, mu i*u i^2)-(∑ i, mu i*u i)^2) := by
        field_simp [ne_of_gt hden]
        ring
      rw [heq]
      exact add_pos_of_pos_of_nonneg (div_pos hsumpos hden) (mul_nonneg hk hvariance)
    · have hk : eps/(1+eps)≤0 := div_nonpos_of_nonpos_of_nonneg (le_of_not_ge he) hden.le
      have hneg : (eps/(1+eps))*(∑ i, mu i*u i)^2≤0 :=
        mul_nonpos_of_nonpos_of_nonneg hk (sq_nonneg _)
      have hbound : (∑ i, mu i*u i^2)≤
          (∑ i, mu i*u i^2)-(eps/(1+eps))*(∑ i, mu i*u i)^2 := by linarith
      exact lt_of_lt_of_le hsumpos hbound

theorem relativeMassMatrix_isUnit (eps : ℝ) (mu : MassRatio)
    (heps : -1<eps) (hm : ∀ i, 0<mu i) (hsum : ∑ i, mu i=1) :
    IsUnit (relativeMassMatrix eps mu) :=
  (relativeMassMatrix_posDef eps mu heps hm hsum).isUnit

theorem relativeMassMatrix_tensor_kernel (eps : ℝ) (mu : MassRatio)
    (heps : -1<eps) (hm : ∀ i, 0<mu i) (hsum : ∑ i, mu i=1)
    (v : SatelliteConfiguration) :
    (∀ i, (∑ j, relativeMassMatrix eps mu i j • v j)=0) ↔ v=0 := by
  constructor
  · intro hv
    have hinj := Matrix.mulVec_injective_of_isUnit
      (relativeMassMatrix_isUnit eps mu heps hm hsum)
    have hscalar (k : Fin 2) :
        relativeMassMatrix eps mu *ᵥ (fun j => v j k)=
          relativeMassMatrix eps mu *ᵥ (0 : Satellite → ℝ) := by
      ext i
      have h := congrArg (fun z : Plane => z k) (hv i)
      simpa only [WithLp.ofLp_sum, Finset.sum_apply, PiLp.smul_apply, PiLp.zero_apply, smul_eq_mul,
        Matrix.mulVec, dotProduct, Pi.zero_apply, mul_zero, Finset.sum_const_zero] using h
    have hz (k : Fin 2) : (fun j => v j k)=(0 : Satellite → ℝ) := hinj (hscalar k)
    ext i k
    exact congrFun (hz k) i
  · rintro rfl i
    simp

theorem relativeActionVectorGradient_zero_iff (eps : ℝ) (mu : MassRatio)
    (heps : -1<eps) (hm : PositiveRatio mu) (q : SatelliteConfiguration) :
    (∀ i, relativeActionVectorGradient eps mu q i=0) ↔
      (∀ i, vectorResidual eps mu q i=0) := by
  simp_rw [relativeActionVectorGradient_eq_CF eps mu hm.2
    (parameter_denominator_ne_zero eps heps) q]
  rw [relativeMassMatrix_tensor_kernel eps mu heps hm.1 hm.2]
  exact funext_iff

theorem relativeActionDerivative_zero_iff_gradient (eps : ℝ) (mu : MassRatio)
    (q : SatelliteConfiguration) :
    relativeActionDerivative eps mu q=0 ↔
      (∀ i, relativeActionVectorGradient eps mu q i=0) := by
  constructor
  · intro hd i
    have h := congrArg (fun L : SatelliteConfiguration →L[ℝ] ℝ =>
      L (Pi.single i (relativeActionVectorGradient eps mu q i))) hd
    rw [relativeActionDerivative_apply] at h
    have heq : (∑ j, inner ℝ (relativeActionVectorGradient eps mu q j)
        ((Pi.single i (relativeActionVectorGradient eps mu q i) : SatelliteConfiguration) j)) =
        ‖relativeActionVectorGradient eps mu q i‖^2 := by
      calc
        (∑ j, inner ℝ (relativeActionVectorGradient eps mu q j)
          ((Pi.single i (relativeActionVectorGradient eps mu q i) : SatelliteConfiguration) j)) =
            inner ℝ (relativeActionVectorGradient eps mu q i) (relativeActionVectorGradient eps mu q i) := by
          rw [Finset.sum_eq_single i]
          · simp
          · intro j _ hji
            simp [hji]
          · simp
        _ = _ := real_inner_self_eq_norm_sq _
    rw [heq] at h
    simpa only [_root_.zero_apply, sq_eq_zero_iff, norm_eq_zero] using h
  · intro hg
    ext v
    rw [relativeActionDerivative_apply]
    simp only [hg, inner_zero_left, Finset.sum_const_zero, _root_.zero_apply]

/-- The critical-point equivalence is for the actual Fréchet derivative of
the actual action, with collision freedom and C's positivity proved. -/
theorem relativeAction_critical_iff_vectorRoot (eps : ℝ) (mu : MassRatio)
    (heps : -1<eps) (hm : PositiveRatio mu) (q : SatelliteConfiguration)
    (hq : RelativeCollisionFree q) :
    fderiv ℝ (relativeAction eps mu) q=0 ↔
      (∀ i, vectorResidual eps mu q i=0) := by
  rw [(relativeAction_hasFDerivAt eps mu q hq).fderiv,
    relativeActionDerivative_zero_iff_gradient,
    relativeActionVectorGradient_zero_iff eps mu heps hm q]

end DominantFiveBody
