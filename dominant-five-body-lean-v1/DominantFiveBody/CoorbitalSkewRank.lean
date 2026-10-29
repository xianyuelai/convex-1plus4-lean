import DominantFiveBody.BoundaryJacobian
import Mathlib.LinearAlgebra.Matrix.Rank

/-! The literal rank and kernel-dimension claims of the three-source
paragraph in Proposition 2.3. The full rank upper bound uses an exact
two-column factorization forced by the actual mass equations, rather than
assuming the requested rank or a second kernel vector. -/

noncomputable section
open scoped BigOperators
open Matrix

namespace DominantFiveBody
open Coorbital

theorem skew_matrix_two_le_rank {N : Type*} [Fintype N]
    (A : Matrix N N ℝ) (p q : N)
    (hdiag : ∀ i, A i i = 0) (hskew : ∀ i j, A j i = -A i j)
    (hpivot : A p q ≠ 0) : 2 ≤ A.rank := by
  classical
  let B : Matrix (Fin 2) (Fin 2) ℝ := A.submatrix ![p,q] ![p,q]
  have hdet : B.det ≠ 0 := by
    rw [Matrix.det_fin_two]
    simp only [B, Matrix.submatrix_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_fin_one, hdiag, hskew p q, zero_mul, zero_sub, mul_neg, neg_neg]
    exact mul_ne_zero hpivot hpivot
  have hB : B.rank = 2 := by simpa only [Fintype.card_fin] using Matrix.rank_of_det_ne_zero hdet
  rw [← hB]
  exact Matrix.rank_submatrix_le A ![p,q] ![p,q]

theorem matrix_three_rank_nullity (A : Matrix (Fin 3) (Fin 3) ℝ) :
    A.rank + Module.finrank ℝ (LinearMap.ker A.mulVecLin) = 3 := by
  simpa [Matrix.rank, Module.finrank_pi_fintype] using A.mulVecLin.finrank_range_add_finrank_ker

theorem matrix_four_rank_nullity (A : Matrix (Fin 4) (Fin 4) ℝ) :
    A.rank + Module.finrank ℝ (LinearMap.ker A.mulVecLin) = 4 := by
  simpa [Matrix.rank, Module.finrank_pi_fintype] using A.mulVecLin.finrank_range_add_finrank_ker

theorem skew3_rank_two_of_nonzero_kernel (A : Matrix (Fin 3) (Fin 3) ℝ)
    (v : Fin 3 → ℝ) (hdiag : ∀ i, A i i = 0) (hskew : ∀ i j, A j i = -A i j)
    (hpivot : A 0 1 ≠ 0) (hv : v ≠ 0) (hroot : ∀ i, ∑ j, A i j * v j = 0) :
    A.rank = 2 ∧ Module.finrank ℝ (LinearMap.ker A.mulVecLin) = 1 := by
  have hmem : v ∈ LinearMap.ker A.mulVecLin := by
    change A *ᵥ v = 0
    funext i
    exact hroot i
  have hker : LinearMap.ker A.mulVecLin ≠ ⊥ := by
    intro heq
    rw [heq, Submodule.mem_bot] at hmem
    exact hv hmem
  have hdim := Submodule.one_le_finrank_iff.mpr hker
  have hlow := skew_matrix_two_le_rank A 0 1 hdiag hskew hpivot
  have hsum := matrix_three_rank_nullity A
  constructor <;> omega

/-- An actual four-by-four skew matrix with a three-source root has rank two.
The Pfaffian identity follows from the three original root rows; it gives an
explicit factorization through a two-dimensional vector space. -/
theorem skew4_rank_two_at_zero_source
    (A : Matrix (Fin 4) (Fin 4) ℝ) (mass : Fin 4 → ℝ)
    (hdiag : ∀ i, A i i = 0) (hskew : ∀ i j, A j i = -A i j)
    (hroot : ∀ i, ∑ j, A i j * mass j = 0)
    (hzero : mass 3 = 0) (hpositive : 0 < mass 2) (hpivot : A 0 1 ≠ 0) :
    A.rank = 2 ∧ Module.finrank ℝ (LinearMap.ker A.mulVecLin) = 2 := by
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
  let C : Matrix (Fin 4) (Fin 2) ℝ := fun i j => A i (j.castAdd 2)
  let D : Matrix (Fin 2) (Fin 4) ℝ :=
    fun i j => if i = 0 then -A 1 j / A 0 1 else A 0 j / A 0 1
  have hfactor : A = C * D := by
    ext i j
    change A i j = ∑ t : Fin 2, C i t * D t j
    rw [Fin.sum_univ_two]
    fin_cases i <;> fin_cases j
    all_goals simp [C, D, hdiag, h10, h20, h21, h30, h31, h32]
    all_goals field_simp [hpivot]
    all_goals nlinarith [hpf]
  have hupper : A.rank ≤ 2 := by
    rw [hfactor]
    exact (Matrix.rank_mul_le_left C D).trans (Matrix.rank_le_width C)
  have hlower := skew_matrix_two_le_rank A 0 1 hdiag hskew hpivot
  have hrank : A.rank = 2 := Nat.le_antisymm hupper hlower
  have hsum := matrix_four_rank_nullity A
  exact ⟨hrank, by omega⟩

def coorbitalSupportMatrix (theta : Satellite → ℝ) (k : Satellite) :
    Matrix (Fin 3) (Fin 3) ℝ := (coorbitalMatrix theta).submatrix k.succAbove k.succAbove

theorem coorbital_three_source_pivot (mass theta : Satellite → ℝ) (k : Satellite)
    (hzero : mass k = 0) (hmass : ∀ i, i ≠ k → 0 < mass i)
    (harc : ∀ i j, i < j → 0 < theta j - theta i ∧ theta j - theta i < Real.pi)
    (hroot : ∀ i, coorbitalResidual mass theta i = 0) :
    coorbitalMatrix theta (k.succAbove 0) (k.succAbove 1) ≠ 0 := by
  have hmass3 : ∀ i : Fin 3, 0 < (mass ∘ k.succAbove) i :=
    fun i => hmass _ (Fin.succAbove_ne k i)
  have harc3 : ∀ i j : Fin 3, i < j →
      0 < (theta ∘ k.succAbove) j - (theta ∘ k.succAbove) i ∧
      (theta ∘ k.succAbove) j - (theta ∘ k.succAbove) i < Real.pi :=
    fun i j hij => harc _ _ (succAbove_preserves_lt_four k i j hij)
  obtain ⟨hgap, _, _⟩ := three_root_gaps (mass ∘ k.succAbove) (theta ∘ k.succAbove)
    hmass3 harc3 (three_source_restricted_root mass theta k hzero hroot)
  have hlt := succAbove_preserves_lt_four k 0 1 (by decide)
  have hpos := (harc _ _ hlt).1
  simp only [coorbitalMatrix, if_neg (ne_of_lt hlt), coorbitalKernel_eq_positive_formula _ hpos.le]
  exact ne_of_gt (Coorbital.kernelF_pos_on_short_arc hpos hgap)

/-- The literal three-source rank claims of TeX line 200, including both
kernel dimensions. The positive support retains its original increasing order. -/
theorem coorbital_three_source_ranks_and_kernel_dimensions
    (mass theta : Satellite → ℝ) (k : Satellite)
    (hzero : mass k = 0) (hmass : ∀ i, i ≠ k → 0 < mass i)
    (harc : ∀ i j, i < j → 0 < theta j - theta i ∧ theta j - theta i < Real.pi)
    (hroot : ∀ i, coorbitalResidual mass theta i = 0) :
    (coorbitalSupportMatrix theta k).rank = 2 ∧
    (coorbitalMatrix theta).rank = 2 ∧
    Module.finrank ℝ (LinearMap.ker (coorbitalMatrix theta).mulVecLin) = 2 ∧
    Module.finrank ℝ (LinearMap.ker (coorbitalSupportMatrix theta k).mulVecLin) = 1 := by
  have hpivot := coorbital_three_source_pivot mass theta k hzero hmass harc hroot
  have hAroot : ∀ i, ∑ j, coorbitalMatrix theta i j * mass j = 0 := by
    intro i
    simpa only [mul_comm] using (coorbitalResidual_eq_matrix_sum mass theta i).symm.trans (hroot i)
  have hSroot : ∀ i, ∑ j, coorbitalSupportMatrix theta k i j * mass (k.succAbove j) = 0 := by
    intro i
    have h := hAroot (k.succAbove i)
    rw [Fin.sum_univ_succAbove _ k] at h
    simpa only [coorbitalSupportMatrix, Matrix.submatrix_apply, hzero, mul_zero, zero_add] using h
  have hv : (fun i : Fin 3 => mass (k.succAbove i)) ≠ 0 := by
    intro heq
    have hz := congrFun heq 2
    exact (ne_of_gt (hmass _ (Fin.succAbove_ne k 2))) hz
  obtain ⟨hSrank,hSker⟩ := skew3_rank_two_of_nonzero_kernel (coorbitalSupportMatrix theta k)
    (fun i => mass (k.succAbove i)) (fun i => by simp [coorbitalSupportMatrix, coorbitalMatrix])
    (fun i j => coorbitalMatrix_reverse theta _ _) hpivot hv hSroot
  let e := zeroLastPermutation k
  have he0 : e 0 = k.succAbove 0 := zeroLastPermutation_support k 0
  have he1 : e 1 = k.succAbove 1 := zeroLastPermutation_support k 1
  have he2 : e 2 = k.succAbove 2 := zeroLastPermutation_support k 2
  have he3 : e 3 = k := zeroLastPermutation_last k
  have hroot' : ∀ i, ∑ j, coorbitalMatrix theta (e i) (e j) * mass (e j) = 0 := by
    intro i
    exact (Equiv.sum_comp e (fun j => coorbitalMatrix theta (e i) j * mass j)).trans (hAroot (e i))
  obtain ⟨hArank',_⟩ := skew4_rank_two_at_zero_source
    ((coorbitalMatrix theta).submatrix e e) (mass ∘ e)
    (fun i => by simp [coorbitalMatrix]) (fun i j => coorbitalMatrix_reverse theta _ _)
    hroot' (by simpa only [Function.comp_apply, he3] using hzero)
    (by simpa only [Function.comp_apply, he2] using hmass _ (Fin.succAbove_ne k 2))
    (by simpa only [Matrix.submatrix_apply, he0, he1] using hpivot)
  have hArank : (coorbitalMatrix theta).rank = 2 := by
    simpa only [Matrix.rank_submatrix] using hArank'
  have hsum := matrix_four_rank_nullity (coorbitalMatrix theta)
  rw [hArank] at hsum
  refine ⟨hSrank,hArank,?_,hSker⟩
  exact Nat.add_left_cancel hsum

/-- The manuscript's kernel-dimension contradiction, kept separate from
the rank calculation: restriction would inject a two-dimensional kernel
into the one-dimensional support kernel if all vectors vanished at k. -/
theorem coorbital_three_source_kernel_not_all_zero_at_missing_source
    (mass theta : Satellite → ℝ) (k : Satellite)
    (hzero : mass k = 0) (hmass : ∀ i, i ≠ k → 0 < mass i)
    (harc : ∀ i j, i < j → 0 < theta j - theta i ∧ theta j - theta i < Real.pi)
    (hroot : ∀ i, coorbitalResidual mass theta i = 0) :
    ∃ v : Satellite → ℝ, v ∈ LinearMap.ker (coorbitalMatrix theta).mulVecLin ∧ v k ≠ 0 := by
  classical
  obtain ⟨_,_,hfull,hsmall⟩ :=
    coorbital_three_source_ranks_and_kernel_dimensions mass theta k hzero hmass harc hroot
  by_contra h
  push Not at h
  let fullKernel := LinearMap.ker (coorbitalMatrix theta).mulVecLin
  let smallKernel := LinearMap.ker (coorbitalSupportMatrix theta k).mulVecLin
  let restriction : fullKernel →ₗ[ℝ] (Fin 3 → ℝ) :=
    { toFun := fun v i => (v : Satellite → ℝ) (k.succAbove i)
      map_add' := by intro v w; rfl
      map_smul' := by intro a v; rfl }
  have hrestriction (v : fullKernel) : restriction v ∈ smallKernel := by
    change (coorbitalSupportMatrix theta k) *ᵥ restriction v = 0
    funext i
    change (∑ j : Fin 3, coorbitalMatrix theta (k.succAbove i) (k.succAbove j) *
      (v : Satellite → ℝ) (k.succAbove j)) = 0
    have hv := congrFun (LinearMap.mem_ker.mp v.property) (k.succAbove i)
    change (∑ j : Satellite, coorbitalMatrix theta (k.succAbove i) j *
      (v : Satellite → ℝ) j) = 0 at hv
    rw [Fin.sum_univ_succAbove _ k] at hv
    simpa only [h v.val v.property, mul_zero, zero_add] using hv
  let R : fullKernel →ₗ[ℝ] smallKernel := restriction.codRestrict smallKernel hrestriction
  have hR : Function.Injective R := by
    intro v w heq
    apply Subtype.ext
    funext i
    by_cases hik : i = k
    · subst i
      exact (h v.val v.property).trans (h w.val w.property).symm
    · obtain ⟨j,rfl⟩ := Fin.exists_succAbove_eq hik
      exact congrArg (fun z : smallKernel => z.val j) heq
  have hle := LinearMap.finrank_le_finrank_of_injective hR
  change Module.finrank ℝ (LinearMap.ker (coorbitalMatrix theta).mulVecLin) ≤
    Module.finrank ℝ (LinearMap.ker (coorbitalSupportMatrix theta k).mulVecLin) at hle
  rw [hfull,hsmall] at hle
  omega

/-- The positive missing-source coordinate is obtained by the original
rank-and-restriction route, then rescaled to one within the actual kernel. -/
theorem coorbital_three_source_kernel_vector_by_rank
    (mass theta : Satellite → ℝ) (k : Satellite)
    (hzero : mass k = 0) (hmass : ∀ i, i ≠ k → 0 < mass i)
    (harc : ∀ i j, i < j → 0 < theta j - theta i ∧ theta j - theta i < Real.pi)
    (hroot : ∀ i, coorbitalResidual mass theta i = 0) :
    ∃ nu : Satellite → ℝ, nu k = 1 ∧ ∀ i, coorbitalResidual nu theta i = 0 := by
  obtain ⟨v,hv,hvk⟩ :=
    coorbital_three_source_kernel_not_all_zero_at_missing_source mass theta k hzero hmass harc hroot
  let nu : Satellite → ℝ := (v k)⁻¹ • v
  have hnuk : nu k = 1 := by simp only [nu, Pi.smul_apply, smul_eq_mul, inv_mul_cancel₀ hvk]
  have hnu : nu ∈ LinearMap.ker (coorbitalMatrix theta).mulVecLin :=
    (LinearMap.ker (coorbitalMatrix theta).mulVecLin).smul_mem (v k)⁻¹ hv
  refine ⟨nu,hnuk,?_⟩
  intro i
  have hz := congrFun (LinearMap.mem_ker.mp hnu) i
  rw [coorbitalResidual_eq_matrix_sum]
  simpa only [Matrix.mulVecLin_apply, Matrix.mulVec, dotProduct, mul_comm, Pi.zero_apply] using hz

end DominantFiveBody
