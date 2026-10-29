import DominantFiveBody.HadamardTargetDifference
import DominantFiveBody.NestedKernelFormulas

/-! The original three-target-coordinate line integral of Section 5.4.
It is separate from the existing alternative rationalized Newton quotient. -/

noncomputable section
open scoped ContDiff
open Set

namespace DominantFiveBody

set_option maxHeartbeats 800000

abbrev NestedScalarTarget := ℝ × (ℝ × ℝ)

theorem nested_target_kernel_integral
    (K : NestedScalarTarget → ℝ) (U : Set NestedScalarTarget) (hU : IsOpen U)
    (hK : ContDiffOn ℝ 1 K U) (S t eta alpha u₁ u₂ z₁ z₂ : ℝ) (he : eta ≠ 0)
    (hsegment : ∀ s ∈ Icc (-(1 - alpha)) alpha,
      (S + t * eta * s * u₂, (u₁ - eta * s * u₂, z₁ - eta * s * z₂)) ∈ U) :
    (K (S + t * eta * alpha * u₂, (u₁ - eta * alpha * u₂, z₁ - eta * alpha * z₂)) -
      K (S - t * eta * (1 - alpha) * u₂,
        (u₁ + eta * (1 - alpha) * u₂, z₁ + eta * (1 - alpha) * z₂))) / eta =
      ∫ s in (-(1 - alpha))..alpha,
        t * u₂ * (fderiv ℝ K
          (S + t * eta * s * u₂, (u₁ - eta * s * u₂, z₁ - eta * s * z₂))) (1, (0, 0)) -
        u₂ * (fderiv ℝ K
          (S + t * eta * s * u₂, (u₁ - eta * s * u₂, z₁ - eta * s * z₂))) (0, (1, 0)) -
        z₂ * (fderiv ℝ K
          (S + t * eta * s * u₂, (u₁ - eta * s * u₂, z₁ - eta * s * z₂))) (0, (0, 1)) := by
  let path : ℝ → NestedScalarTarget := fun s =>
    (S + t * eta * s * u₂, (u₁ - eta * s * u₂, z₁ - eta * s * z₂))
  let f : ℝ → ℝ := K ∘ path
  let v : NestedScalarTarget := (t * eta * u₂, (-eta * u₂, -eta * z₂))
  let g : ℝ → ℝ := fun s => (fderiv ℝ K (path s)) v
  have hp : Continuous path := by fun_prop
  have hc : ContinuousOn g (Icc (-(1 - alpha)) alpha) :=
    ((hK.continuousOn_fderiv_of_isOpen hU le_rfl).comp hp.continuousOn hsegment).clm_apply
      continuousOn_const
  have hd (s : ℝ) (hs : s ∈ Icc (-(1 - alpha)) alpha) : HasDerivAt f (g s) s := by
    have hpath : HasDerivAt path v s := by
      have hr := ((((hasDerivAt_id s).const_mul (t * eta)).mul_const u₂).const_add S)
      have hP := (((hasDerivAt_id s).const_mul eta).mul_const u₂).const_sub u₁
      have hQ := (((hasDerivAt_id s).const_mul eta).mul_const z₂).const_sub z₁
      convert hr.prodMk (hP.prodMk hQ) using 1 <;> simp [path, v, mul_assoc]
    exact ((hK (path s) (hsegment s hs)).contDiffAt
      (hU.mem_nhds (hsegment s hs))).differentiableAt (by norm_num)
      |>.hasFDerivAt.comp_hasDerivAt s hpath
  have hab : -(1 - alpha) ≤ alpha := by linarith
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun s hs => hd s ((uIcc_of_le hab) ▸ hs)) (hc.intervalIntegrable_of_Icc hab)
  have hlinear (s : ℝ) : g s = eta *
      (t * u₂ * (fderiv ℝ K (path s)) (1, (0, 0)) -
        u₂ * (fderiv ℝ K (path s)) (0, (1, 0)) -
        z₂ * (fderiv ℝ K (path s)) (0, (0, 1))) := by
    have heq : v = (t * eta * u₂) • ((1 : ℝ), (0, 0)) +
        (-eta * u₂) • ((0 : ℝ), (1, 0)) + (-eta * z₂) • ((0 : ℝ), (0, 1)) := by
      ext <;> simp [v]
    change (fderiv ℝ K (path s)) v = _
    rw [heq, map_add, map_add, map_smul, map_smul, map_smul]
    simp only [smul_eq_mul]
    ring
  have hendpoint : path (-(1 - alpha)) =
      (S - t * eta * (1 - alpha) * u₂,
        (u₁ + eta * (1 - alpha) * u₂, z₁ + eta * (1 - alpha) * z₂)) := by
    ext <;> simp [path] <;> ring
  simp only [f, Function.comp_apply] at hFTC
  rw [hendpoint] at hFTC
  change (f (alpha) - K _) / eta = _
  simp only [f, Function.comp_apply]
  rw [← hFTC]
  simp_rw [hlinear]
  rw [intervalIntegral.integral_const_mul]
  simp [he, path]

theorem nested_kernel_integral_shift (g : ℝ → ℝ) (alpha : ℝ) :
    (∫ s in (-(1 - alpha))..alpha, g s) =
      ∫ x in (0 : ℝ)..1, g (x - (1 - alpha)) := by
  rw [intervalIntegral.integral_comp_sub_right]
  congr 1 <;> ring

end DominantFiveBody
