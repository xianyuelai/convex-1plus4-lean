import Mathlib.Analysis.Calculus.FDeriv.CompCLM
import Mathlib.Topology.Algebra.Module.Equiv

/-! # Coordinate-dependent row changes at actual roots

Source: §3 Lemma 3.1. The derivative of the row map is retained in the
product rule and vanishes because the actual residual is zero at the root.
-/

noncomputable section

namespace DominantFiveBody

variable {E F G H : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedAddCommGroup G] [NormedSpace ℝ G]
  [NormedAddCommGroup H] [NormedSpace ℝ H]

theorem row_transform_hasFDerivAt_at_root (f : E → F) (L : E → (F →L[ℝ] G))
    (x : E) (df : E →L[ℝ] F) (dL : E →L[ℝ] (F →L[ℝ] G))
    (hf : HasFDerivAt f df x) (hL : HasFDerivAt L dL x) (hroot : f x=0) :
    HasFDerivAt (fun y => L y (f y)) ((L x).comp df) x := by
  have h := hL.clm_apply hf
  simpa only [hroot, map_zero, add_zero] using h

theorem row_transform_fderiv_at_root (f : E → F) (L : E → (F →L[ℝ] G)) (x : E)
    (hf : DifferentiableAt ℝ f x) (hL : DifferentiableAt ℝ L x) (hroot : f x=0) :
    fderiv ℝ (fun y => L y (f y)) x = (L x).comp (fderiv ℝ f x) :=
  (row_transform_hasFDerivAt_at_root f L x _ _ hf.hasFDerivAt hL.hasFDerivAt hroot).fderiv

theorem coordinate_row_transform_fderiv_at_root (f : E → F) (L : E → (F →L[ℝ] G))
    (psi : H → E) (z : H)
    (hf : DifferentiableAt ℝ f (psi z)) (hL : DifferentiableAt ℝ L (psi z))
    (hpsi : DifferentiableAt ℝ psi z) (hroot : f (psi z)=0) :
    fderiv ℝ (fun y => L (psi y) (f (psi y))) z =
      ((L (psi z)).comp (fderiv ℝ f (psi z))).comp (fderiv ℝ psi z) :=
  ((row_transform_hasFDerivAt_at_root f L (psi z) _ _
    hf.hasFDerivAt hL.hasFDerivAt hroot).comp z hpsi.hasFDerivAt).fderiv

theorem coordinate_row_transform_isInvertible_iff (f : E → F) (L : E → (F →L[ℝ] G))
    (psi : H → E) (z : H)
    (hf : DifferentiableAt ℝ f (psi z)) (hL : DifferentiableAt ℝ L (psi z))
    (hpsi : DifferentiableAt ℝ psi z) (hroot : f (psi z)=0)
    (hLi : (L (psi z)).IsInvertible) (hpsii : (fderiv ℝ psi z).IsInvertible) :
    (fderiv ℝ (fun y => L (psi y) (f (psi y))) z).IsInvertible ↔
      (fderiv ℝ f (psi z)).IsInvertible := by
  rw [coordinate_row_transform_fderiv_at_root f L psi z hf hL hpsi hroot]
  obtain ⟨eL,heL⟩ := hLi
  obtain ⟨epsi,hepsi⟩ := hpsii
  rw [← heL, ← hepsi]
  simp only [ContinuousLinearMap.isInvertible_comp_equiv,
    ContinuousLinearMap.isInvertible_equiv_comp]

end DominantFiveBody
