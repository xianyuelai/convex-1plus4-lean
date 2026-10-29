import DominantFiveBody.CoorbitalHessian
import Mathlib.Analysis.Calculus.FDeriv.CompCLM
import Mathlib.LinearAlgebra.Matrix.DotProduct

/-! Coordinate formulas for the physical coorbital Hessian and its anchored slice.

The coefficient uses the positively ordered separation, then extends symmetrically.
Every matrix below is obtained from the actual second differential of the physical
chord potential. No equilibrium or mass-positivity assumption is needed for these
coordinate identities.
-/

noncomputable section
open scoped BigOperators
open Filter Set Topology Matrix

namespace DominantFiveBody
open Coorbital

/-- The manuscript's `cᵢⱼ`, symmetrically extended from `i < j`, with zero diagonal. -/
def coorbitalHessianCoefficient (mass theta : Satellite → ℝ) (i j : Satellite) : ℝ :=
  if i < j then mass i * mass j * kappa (theta j - theta i)
  else if j < i then mass j * mass i * kappa (theta i - theta j) else 0

@[simp] theorem coorbitalHessianCoefficient_self (mass theta : Satellite → ℝ)
    (i : Satellite) : coorbitalHessianCoefficient mass theta i i = 0 := by
  simp [coorbitalHessianCoefficient]

theorem coorbitalHessianCoefficient_of_lt (mass theta : Satellite → ℝ)
    (i j : Satellite) (hij : i < j) :
    coorbitalHessianCoefficient mass theta i j =
      mass i * mass j * kappa (theta j - theta i) := by
  simp [coorbitalHessianCoefficient, hij]

theorem coorbitalHessianCoefficient_symmetric (mass theta : Satellite → ℝ)
    (i j : Satellite) :
    coorbitalHessianCoefficient mass theta i j = coorbitalHessianCoefficient mass theta j i := by
  rcases lt_trichotomy i j with hij | hij | hij
  · simp [coorbitalHessianCoefficient, hij, not_lt.mpr hij.le]
  · subst j; rfl
  · simp [coorbitalHessianCoefficient, hij, not_lt.mpr hij.le]

/-- Matrix entries are evaluations of the physical second differential on coordinate vectors. -/
def coorbitalHessianMatrix (mass theta : Satellite → ℝ) : Matrix Satellite Satellite ℝ :=
  fun i j => coorbitalPhysicalHessian mass theta (Pi.single i 1) (Pi.single j 1)

theorem coorbitalPhysicalHessian_pair_formula (mass theta u v : Satellite → ℝ)
    (harc : OrderedSemicircle theta) :
    coorbitalPhysicalHessian mass theta u v =
      ∑ i, ∑ j, if i < j then
        mass i * mass j * kappa (theta j-theta i) * (u j-u i) * (v j-v i) else 0 := by
  rw [coorbitalPhysicalHessian_eq_map mass theta u v harc, angularHessianMap_apply]

theorem coorbitalHessianMatrix_diagonal (mass theta : Satellite → ℝ)
    (harc : OrderedSemicircle theta) (i : Satellite) :
    coorbitalHessianMatrix mass theta i i =
      ∑ j ∈ Finset.univ.erase i, coorbitalHessianCoefficient mass theta i j := by
  classical
  unfold coorbitalHessianMatrix
  rw [coorbitalPhysicalHessian_pair_formula mass theta _ _ harc]
  fin_cases i <;>
    simp [coorbitalHessianCoefficient, Fin.sum_univ_four, Finset.sum_erase_eq_sub]
  all_goals ring

theorem coorbitalHessianMatrix_offDiagonal (mass theta : Satellite → ℝ)
    (harc : OrderedSemicircle theta) (i j : Satellite) (hij : i ≠ j) :
    coorbitalHessianMatrix mass theta i j = -coorbitalHessianCoefficient mass theta i j := by
  classical
  unfold coorbitalHessianMatrix
  rw [coorbitalPhysicalHessian_pair_formula mass theta _ _ harc]
  fin_cases i <;> fin_cases j <;>
    simp_all [coorbitalHessianCoefficient, Fin.sum_univ_four]

theorem coorbitalHessianMatrix_entries (mass theta : Satellite → ℝ)
    (harc : OrderedSemicircle theta) (i j : Satellite) :
    coorbitalHessianMatrix mass theta i j =
      if i = j then ∑ k ∈ Finset.univ.erase i, coorbitalHessianCoefficient mass theta i k
      else -coorbitalHessianCoefficient mass theta i j := by
  by_cases hij : i = j
  · subst j; simp [coorbitalHessianMatrix_diagonal mass theta harc]
  · simp [hij, coorbitalHessianMatrix_offDiagonal mass theta harc i j hij]

theorem coorbitalHessianMatrix_symmetric (mass theta : Satellite → ℝ)
    (harc : OrderedSemicircle theta) : (coorbitalHessianMatrix mass theta).IsSymm := by
  ext i j
  change coorbitalHessianMatrix mass theta j i = coorbitalHessianMatrix mass theta i j
  by_cases hij : i = j
  · subst j; rfl
  · rw [coorbitalHessianMatrix_offDiagonal mass theta harc j i (Ne.symm hij),
      coorbitalHessianMatrix_offDiagonal mass theta harc i j hij,
      coorbitalHessianCoefficient_symmetric mass theta j i]

theorem coorbitalHessianMatrix_bilinear (mass theta u v : Satellite → ℝ)
    (harc : OrderedSemicircle theta) :
    dotProduct u (coorbitalHessianMatrix mass theta *ᵥ v) =
      coorbitalPhysicalHessian mass theta u v := by
  classical
  simp [Matrix.mulVec, dotProduct, coorbitalHessianMatrix,
    coorbitalPhysicalHessian_pair_formula mass theta _ _ harc, Fin.sum_univ_four]
  ring

theorem coorbitalHessianMatrix_quadratic (mass theta u : Satellite → ℝ)
    (harc : OrderedSemicircle theta) :
    dotProduct u (coorbitalHessianMatrix mass theta *ᵥ u) =
      ∑ i, ∑ j, if i < j then
        mass i * mass j * kappa (theta j-theta i) * (u j-u i)^2 else 0 := by
  rw [coorbitalHessianMatrix_bilinear mass theta u u harc,
    coorbitalPhysicalHessian_self mass theta u harc]
  rfl

theorem coorbitalHessianMatrix_quadratic_expanded (mass theta u : Satellite → ℝ)
    (harc : OrderedSemicircle theta) :
    dotProduct u (coorbitalHessianMatrix mass theta *ᵥ u) =
      ∑ i, ∑ j, if i < j then coorbitalHessianCoefficient mass theta i j *
        (u i^2+u j^2-2*u i*u j) else 0 := by
  rw [coorbitalHessianMatrix_quadratic mass theta u harc]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  split_ifs with hij
  · rw [coorbitalHessianCoefficient_of_lt mass theta i j hij]; ring
  · rfl

/-- Linear insertion of the fixed first angular coordinate. -/
def coorbitalFirstAngleInsertion : (Fin 3 → ℝ) →L[ℝ] (Satellite → ℝ) :=
  ContinuousLinearMap.pi (fun i => Fin.cases 0 (fun j => ContinuousLinearMap.proj j) i)

@[simp] theorem coorbitalFirstAngleInsertion_zero (z : Fin 3 → ℝ) :
    coorbitalFirstAngleInsertion z 0 = 0 := by
  simp [coorbitalFirstAngleInsertion]

@[simp] theorem coorbitalFirstAngleInsertion_succ (z : Fin 3 → ℝ) (i : Fin 3) :
    coorbitalFirstAngleInsertion z i.succ = z i := by
  simp [coorbitalFirstAngleInsertion]

theorem coorbitalFirstAngleInsertion_eq_insertNth (z : Fin 3 → ℝ) :
    coorbitalFirstAngleInsertion z = Fin.insertNth 0 0 z := by
  funext i
  refine Fin.cases ?_ (fun j => ?_) i <;> simp

theorem coorbitalFirstAngleInsertion_coordinate (i : Fin 3) :
    coorbitalFirstAngleInsertion (Pi.single i 1) = Pi.single i.succ 1 := by
  classical
  funext j
  refine Fin.cases ?_ (fun k => ?_) j
  · simp
  · rw [coorbitalFirstAngleInsertion_succ]
    fin_cases i <;> fin_cases k <;> simp

/-- The actual physical coorbital potential restricted to `theta 0 = 0`. -/
def coorbitalSlicePotential (mass : Satellite → ℝ) (z : Fin 3 → ℝ) : ℝ :=
  coorbitalPotential mass (coorbitalFirstAngleInsertion z)

def coorbitalSlicePotentialDerivative (mass : Satellite → ℝ) (z : Fin 3 → ℝ) :
    (Fin 3 → ℝ) →L[ℝ] ℝ :=
  (angularPotentialDerivative mass (coorbitalFirstAngleInsertion z)).comp
    coorbitalFirstAngleInsertion

def coorbitalSliceHessianMap (mass : Satellite → ℝ) (z : Fin 3 → ℝ) :
    (Fin 3 → ℝ) →L[ℝ] (Fin 3 → ℝ) →L[ℝ] ℝ :=
  ((ContinuousLinearMap.compL ℝ (Fin 3 → ℝ) (Satellite → ℝ) ℝ).flip
    coorbitalFirstAngleInsertion).comp
    ((angularHessianMap mass (coorbitalFirstAngleInsertion z)).comp coorbitalFirstAngleInsertion)

theorem coorbitalSlicePotential_hasFDerivAt (mass : Satellite → ℝ) (z : Fin 3 → ℝ)
    (harc : OrderedSemicircle (coorbitalFirstAngleInsertion z)) :
    HasFDerivAt (coorbitalSlicePotential mass) (coorbitalSlicePotentialDerivative mass z) z := by
  have hgeom : ∀ᶠ angles in nhds (coorbitalFirstAngleInsertion z), OrderedSemicircle angles :=
    (isOpen_orderedSemicircle 4).mem_nhds harc
  have hnear : coorbitalPotential mass =ᶠ[nhds (coorbitalFirstAngleInsertion z)] angularPotential mass :=
    hgeom.mono (fun angles ha => coorbitalPotential_eq_angularPotential mass angles ha)
  have hd := (angularPotential_hasFDerivAt mass (coorbitalFirstAngleInsertion z) harc).congr_of_eventuallyEq hnear
  exact hd.comp z coorbitalFirstAngleInsertion.hasFDerivAt

theorem coorbitalSlicePotentialDerivative_hasFDerivAt (mass : Satellite → ℝ) (z : Fin 3 → ℝ)
    (harc : OrderedSemicircle (coorbitalFirstAngleInsertion z)) :
    HasFDerivAt (coorbitalSlicePotentialDerivative mass) (coorbitalSliceHessianMap mass z) z := by
  have hd := (angularPotentialDerivative_hasFDerivAt mass (coorbitalFirstAngleInsertion z) harc).comp z
    coorbitalFirstAngleInsertion.hasFDerivAt
  have hc : HasFDerivAt (𝕜 := ℝ) (fun _ : (Fin 3 → ℝ) => coorbitalFirstAngleInsertion) 0 z :=
    hasFDerivAt_const _ _
  convert! hd.clm_comp hc using 1
  ext u v
  simp [coorbitalSliceHessianMap]

theorem coorbitalSlicePotential_second_fderiv (mass : Satellite → ℝ) (z : Fin 3 → ℝ)
    (harc : OrderedSemicircle (coorbitalFirstAngleInsertion z)) :
    fderiv ℝ (fderiv ℝ (coorbitalSlicePotential mass)) z = coorbitalSliceHessianMap mass z := by
  have hnear : ∀ᶠ w in nhds z, OrderedSemicircle (coorbitalFirstAngleInsertion w) :=
    coorbitalFirstAngleInsertion.continuous.continuousAt.preimage_mem_nhds
      ((isOpen_orderedSemicircle 4).mem_nhds harc)
  have heq : fderiv ℝ (coorbitalSlicePotential mass) =ᶠ[nhds z]
      coorbitalSlicePotentialDerivative mass :=
    hnear.mono (fun w hw => (coorbitalSlicePotential_hasFDerivAt mass w hw).fderiv)
  exact ((coorbitalSlicePotentialDerivative_hasFDerivAt mass z harc).congr_of_eventuallyEq heq).fderiv

theorem coorbitalSlicePotential_hessian_pullback (mass : Satellite → ℝ)
    (z u v : Fin 3 → ℝ) (harc : OrderedSemicircle (coorbitalFirstAngleInsertion z)) :
    (fderiv ℝ (fderiv ℝ (coorbitalSlicePotential mass)) z) u v =
      coorbitalPhysicalHessian mass (coorbitalFirstAngleInsertion z)
        (coorbitalFirstAngleInsertion u) (coorbitalFirstAngleInsertion v) := by
  rw [coorbitalSlicePotential_second_fderiv mass z harc,
    coorbitalPhysicalHessian_eq_map mass _ _ _ harc]
  rfl

def coorbitalSliceHessianMatrix (mass : Satellite → ℝ) (z : Fin 3 → ℝ) :
    Matrix (Fin 3) (Fin 3) ℝ :=
  fun i j => (fderiv ℝ (fderiv ℝ (coorbitalSlicePotential mass)) z)
    (Pi.single i 1) (Pi.single j 1)

theorem coorbitalSliceHessianMatrix_eq_submatrix (mass : Satellite → ℝ)
    (z : Fin 3 → ℝ) (harc : OrderedSemicircle (coorbitalFirstAngleInsertion z)) :
    coorbitalSliceHessianMatrix mass z =
      (coorbitalHessianMatrix mass (coorbitalFirstAngleInsertion z)).submatrix Fin.succ Fin.succ := by
  ext i j
  unfold coorbitalSliceHessianMatrix
  rw [coorbitalSlicePotential_hessian_pullback mass z _ _ harc,
    coorbitalFirstAngleInsertion_coordinate, coorbitalFirstAngleInsertion_coordinate]
  rfl

theorem coorbitalSliceHessianMatrix_bilinear (mass : Satellite → ℝ)
    (z u v : Fin 3 → ℝ) (harc : OrderedSemicircle (coorbitalFirstAngleInsertion z)) :
    dotProduct u (coorbitalSliceHessianMatrix mass z *ᵥ v) =
      (fderiv ℝ (fderiv ℝ (coorbitalSlicePotential mass)) z) u v := by
  rw [coorbitalSliceHessianMatrix_eq_submatrix mass z harc,
    coorbitalSlicePotential_hessian_pullback mass z u v harc]
  have hmatrix := coorbitalHessianMatrix_bilinear mass (coorbitalFirstAngleInsertion z)
    (coorbitalFirstAngleInsertion u) (coorbitalFirstAngleInsertion v) harc
  convert hmatrix using 1
  simp only [dotProduct, Matrix.mulVec, Matrix.submatrix_apply,
    Fin.sum_univ_succ, coorbitalFirstAngleInsertion_zero, coorbitalFirstAngleInsertion_succ,
    zero_mul, mul_zero, zero_add]

theorem coorbitalSliceHessian_quadratic (mass : Satellite → ℝ) (z u : Fin 3 → ℝ)
    (harc : OrderedSemicircle (coorbitalFirstAngleInsertion z)) :
    (fderiv ℝ (fderiv ℝ (coorbitalSlicePotential mass)) z) u u =
      coorbitalKappaForm mass (coorbitalFirstAngleInsertion z) (coorbitalFirstAngleInsertion u) := by
  rw [coorbitalSlicePotential_hessian_pullback mass z u u harc,
    coorbitalPhysicalHessian_self mass _ _ harc]

theorem coorbitalSliceHessianMatrix_quadratic (mass : Satellite → ℝ) (z u : Fin 3 → ℝ)
    (harc : OrderedSemicircle (coorbitalFirstAngleInsertion z)) :
    dotProduct u (coorbitalSliceHessianMatrix mass z *ᵥ u) =
      coorbitalKappaForm mass (coorbitalFirstAngleInsertion z) (coorbitalFirstAngleInsertion u) := by
  rw [coorbitalSliceHessianMatrix_bilinear mass z u u harc,
    coorbitalSliceHessian_quadratic mass z u harc]

theorem coorbitalSliceHessian_quadratic_zero_first (mass theta u : Satellite → ℝ)
    (harc : OrderedSemicircle theta) (htheta : theta 0 = 0) (hu : u 0 = 0) :
    (fderiv ℝ (fderiv ℝ (coorbitalSlicePotential mass)) (fun i => theta i.succ))
        (fun i => u i.succ) (fun i => u i.succ) = coorbitalKappaForm mass theta u := by
  have ht : coorbitalFirstAngleInsertion (fun i : Fin 3 => theta i.succ) = theta := by
    funext i
    refine Fin.cases ?_ (fun j => ?_) i <;> simp [htheta]
  have hv : coorbitalFirstAngleInsertion (fun i : Fin 3 => u i.succ) = u := by
    funext i
    refine Fin.cases ?_ (fun j => ?_) i <;> simp [hu]
  have ha : OrderedSemicircle (coorbitalFirstAngleInsertion (fun i : Fin 3 => theta i.succ)) := by
    simpa only [ht] using harc
  simpa only [ht, hv] using coorbitalSliceHessian_quadratic mass
    (fun i => theta i.succ) (fun i => u i.succ) ha

end DominantFiveBody
