import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-! The target-only line-segment formula used in Section 5. -/

noncomputable section
open scoped ContDiff
open Set

namespace DominantFiveBody

set_option maxHeartbeats 700000

/-- The exact two-variable Hadamard formula. Only the target coordinates
vary along this segment; parameters of the field remain fixed. Smoothness
is required only on an open neighborhood of the actual segment. -/
theorem hadamard_target_difference
    (K : ℝ × ℝ → ℝ) (U : Set (ℝ × ℝ)) (hU : IsOpen U)
    (hK : ContDiffOn ℝ 1 K U) (rho v t u z : ℝ) (ht : t ≠ 0)
    (hsegment : ∀ s ∈ Icc (0 : ℝ) 1, (rho + s * (t * u), v + s * (t * z)) ∈ U) :
    (K (rho + t * u, v + t * z) - K (rho, v)) / t =
      ∫ s in (0 : ℝ)..1,
        u * (fderiv ℝ K (rho + s * (t * u), v + s * (t * z))) (1, 0) +
        z * (fderiv ℝ K (rho + s * (t * u), v + s * (t * z))) (0, 1) := by
  let path : ℝ → ℝ × ℝ := fun s => (rho + s * (t * u), v + s * (t * z))
  let f : ℝ → ℝ := K ∘ path
  let g : ℝ → ℝ := fun s => (fderiv ℝ K (path s)) (t * u, t * z)
  have hp : Continuous path := by fun_prop
  have hc : ContinuousOn g (Icc (0 : ℝ) 1) :=
    ((hK.continuousOn_fderiv_of_isOpen hU le_rfl).comp hp.continuousOn hsegment).clm_apply
      continuousOn_const
  have hd (s : ℝ) (hs : s ∈ Icc (0 : ℝ) 1) : HasDerivAt f (g s) s := by
    have hpath : HasDerivAt path (t * u, t * z) s := by
      simpa [path] using (((hasDerivAt_id s).mul_const (t * u)).const_add rho).prodMk
        (((hasDerivAt_id s).mul_const (t * z)).const_add v)
    exact ((hK (path s) (hsegment s hs)).contDiffAt
      (hU.mem_nhds (hsegment s hs))).differentiableAt (by norm_num) |>.hasFDerivAt.comp_hasDerivAt s hpath
  have hFTC := intervalIntegral.integral_unitInterval_deriv_eq_sub
    (z₀ := (0 : ℝ)) (z₁ := (1 : ℝ)) (f := f) (f' := g)
    (by simpa only [smul_eq_mul, mul_one, zero_add] using hc)
    (by simpa only [smul_eq_mul, mul_one, zero_add] using hd)
  simp only [one_smul, zero_add] at hFTC
  have hlinear (s : ℝ) : g s = t *
      (u * (fderiv ℝ K (path s)) (1, 0) + z * (fderiv ℝ K (path s)) (0, 1)) := by
    have he : (t * u, t * z) = (t * u) • ((1 : ℝ), 0) + (t * z) • ((0 : ℝ), 1) := by
      ext <;> simp
    change (fderiv ℝ K (path s)) (t * u, t * z) = _
    rw [he, map_add, map_smul, map_smul]
    simp only [smul_eq_mul]
    ring
  simp only [f, Function.comp_apply, path, zero_mul, add_zero, one_mul] at hFTC
  rw [← hFTC]
  simp_rw [hlinear]
  rw [intervalIntegral.integral_const_mul]
  simp [ht, path]

end DominantFiveBody
