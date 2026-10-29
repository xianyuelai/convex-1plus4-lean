import DominantFiveBody.OriginalNestedIntegral
import DominantFiveBody.ChartExplicitDefinitions
import DominantFiveBody.CompactContinuation

/-! Original scalar L and N kernels and their actual coordinate substitution. -/

noncomputable section
open scoped ContDiff
open Set Filter Topology
namespace DominantFiveBody

set_option maxHeartbeats 900000

def nestedScalarTargetWSq (t rc : ℝ) (v : NestedScalarTarget) : ℝ :=
  v.2.1 ^ 2 + v.1 * rc * v.2.2 ^ 2 * Real.sinc (t * v.2.2 / 2) ^ 2

def nestedScalarAngularKernel (eps t rc : ℝ) (v : NestedScalarTarget) : ℝ :=
  v.1 * rc * v.2.2 * Real.sinc (t * v.2.2) *
    ((Real.sqrt (nestedScalarTargetWSq t rc v) ^ 3)⁻¹ - t ^ 3 / (1 + eps))

def nestedScalarRadialKernel (t rc : ℝ) (v : NestedScalarTarget) : ℝ :=
  (v.2.1 - rc * singleScaleChi t v.2.2) *
    (Real.sqrt (nestedScalarTargetWSq t rc v) ^ 3)⁻¹

theorem positive_sqrt_cube_inverse_rpow (x : ℝ) (hx : 0 < x) :
    (Real.sqrt x ^ 3)⁻¹ = x ^ (-(3 : ℝ) / 2) := by
  rw [Real.sqrt_eq_rpow, ← Real.rpow_mul_natCast hx.le, ← Real.rpow_neg hx.le]
  congr 1
  norm_num

theorem nestedScalarAngularKernel_formula (eps t rc : ℝ) (v : NestedScalarTarget)
    (hW : 0 < nestedScalarTargetWSq t rc v) :
    nestedScalarAngularKernel eps t rc v = v.1 * rc * v.2.2 * Real.sinc (t * v.2.2) *
      ((v.2.1 ^ 2 + v.1 * rc * v.2.2 ^ 2 * Real.sinc (t * v.2.2 / 2) ^ 2) ^
        (-(3 : ℝ) / 2) - t ^ 3 / (1 + eps)) := by
  unfold nestedScalarAngularKernel
  rw [positive_sqrt_cube_inverse_rpow _ hW]
  rfl

theorem nestedScalarRadialKernel_formula (t rc : ℝ) (v : NestedScalarTarget)
    (hW : 0 < nestedScalarTargetWSq t rc v) :
    nestedScalarRadialKernel t rc v = (v.2.1 - rc * singleScaleChi t v.2.2) *
      (v.2.1 ^ 2 + v.1 * rc * v.2.2 ^ 2 * Real.sinc (t * v.2.2 / 2) ^ 2) ^
        (-(3 : ℝ) / 2) := by
  unfold nestedScalarRadialKernel
  rw [positive_sqrt_cube_inverse_rpow _ hW]
  rfl

theorem nestedScalarTargetWSq_contDiff (n : ℕ∞ω) (t rc : ℝ) :
    ContDiff ℝ n (nestedScalarTargetWSq t rc) := by
  unfold nestedScalarTargetWSq
  fun_prop

theorem nestedScalarAngularKernel_contDiffAt (n : ℕ∞ω) (eps t rc : ℝ)
    (v : NestedScalarTarget) (hW : 0 < nestedScalarTargetWSq t rc v) :
    ContDiffAt ℝ n (nestedScalarAngularKernel eps t rc) v := by
  have hsqrt := (nestedScalarTargetWSq_contDiff n t rc).contDiffAt.sqrt hW.ne'
  have hnorm : Real.sqrt (nestedScalarTargetWSq t rc v) ^ 3 ≠ 0 := by
    exact pow_ne_zero _ (Real.sqrt_pos.mpr hW).ne'
  unfold nestedScalarAngularKernel
  exact (((contDiffAt_fst.mul contDiffAt_const).mul contDiffAt_snd.snd).mul
    ((sinc_contDiff n).contDiffAt.comp v (contDiffAt_const.mul contDiffAt_snd.snd))).mul
      ((hsqrt.pow 3).inv hnorm |>.sub contDiffAt_const)

theorem nestedScalarRadialKernel_contDiffAt (n : ℕ∞ω) (t rc : ℝ)
    (v : NestedScalarTarget) (hW : 0 < nestedScalarTargetWSq t rc v) :
    ContDiffAt ℝ n (nestedScalarRadialKernel t rc) v := by
  have hsqrt := (nestedScalarTargetWSq_contDiff n t rc).contDiffAt.sqrt hW.ne'
  have hnorm : Real.sqrt (nestedScalarTargetWSq t rc v) ^ 3 ≠ 0 := by
    exact pow_ne_zero _ (Real.sqrt_pos.mpr hW).ne'
  have hchi : ContDiffAt ℝ n (fun x : NestedScalarTarget => singleScaleChi t x.2.2) v := by
    unfold singleScaleChi
    fun_prop
  unfold nestedScalarRadialKernel
  exact (contDiffAt_snd.fst.sub (contDiffAt_const.mul hchi)).mul ((hsqrt.pow 3).inv hnorm)

theorem nestedScalarKernel_domain_isOpen (t rc : ℝ) :
    IsOpen {v | 0 < nestedScalarTargetWSq t rc v} :=
  isOpen_lt continuous_const (nestedScalarTargetWSq_contDiff 0 t rc).continuous

theorem nestedScalarAngularKernel_contDiffOn (n : ℕ∞ω) (eps t rc : ℝ) :
    ContDiffOn ℝ n (nestedScalarAngularKernel eps t rc) {v | 0 < nestedScalarTargetWSq t rc v} :=
  fun v hv => (nestedScalarAngularKernel_contDiffAt n eps t rc v hv).contDiffWithinAt

theorem nestedScalarRadialKernel_contDiffOn (n : ℕ∞ω) (t rc : ℝ) :
    ContDiffOn ℝ n (nestedScalarRadialKernel t rc) {v | 0 < nestedScalarTargetWSq t rc v} :=
  fun v hv => (nestedScalarRadialKernel_contDiffAt n t rc v hv).contDiffWithinAt

def nestedScalarTargetPoint (t eta alpha : ℝ) (y : NestedChartVariables) (i : Fin 2) :
    NestedScalarTarget := (nestedChartRadii t eta alpha y (i.castAdd 2),
      (nestedOuterRadialGaps eta alpha y i, nestedOuterAngularGaps eta alpha y i))

theorem nestedScalarTargetWSq_substitution (t eta alpha : ℝ) (y : NestedChartVariables)
    (i : Fin 2) :
    nestedScalarTargetWSq t (nestedChartRadii t eta alpha y 2)
      (nestedScalarTargetPoint t eta alpha y i) = nestedOuterWSq t eta alpha y i := by
  rw [nestedOuterWSq_formula]
  rfl

theorem nestedScalarAngularKernel_substitution (eps t eta alpha : ℝ)
    (y : NestedChartVariables) (i : Fin 2) :
    nestedScalarAngularKernel eps t (nestedChartRadii t eta alpha y 2)
      (nestedScalarTargetPoint t eta alpha y i) = nestedOuterL eps t eta alpha y i := by
  rw [nestedOuterL_formula]
  unfold nestedScalarAngularKernel
  rw [nestedScalarTargetWSq_substitution]
  rfl

theorem nestedScalarRadialKernel_substitution (t eta alpha : ℝ)
    (y : NestedChartVariables) (i : Fin 2) :
    nestedScalarRadialKernel t (nestedChartRadii t eta alpha y 2)
      (nestedScalarTargetPoint t eta alpha y i) = nestedOuterN t eta alpha y i := by
  rw [nestedOuterN_formula]
  unfold nestedScalarRadialKernel
  rw [nestedScalarTargetWSq_substitution]
  rfl

def nestedOriginalScalarPath (t eta _alpha : ℝ) (y : NestedChartVariables)
    (s : ℝ) : NestedScalarTarget :=
  (y 1 - (1 - eta ^ 3) * t * y 2 + t * eta * s * y 3,
    (y 2 - eta * s * y 3, y 5 - eta * s * y 6))

theorem nestedOriginalScalarPath_endpoints (t eta alpha : ℝ) (y : NestedChartVariables) :
    nestedOriginalScalarPath t eta alpha y (-(1 - alpha)) = nestedScalarTargetPoint t eta alpha y 0 ∧
    nestedOriginalScalarPath t eta alpha y alpha = nestedScalarTargetPoint t eta alpha y 1 := by
  constructor <;> ext <;>
    dsimp [nestedOriginalScalarPath, nestedScalarTargetPoint, nestedChartRadii,
      nestedCoordinates, nestedOuterRadialGaps, nestedOuterAngularGaps] <;> ring

theorem nestedOriginalScalarPath_left_explicit (t eta alpha : ℝ) (y : NestedChartVariables) :
    (y 1 - (1 - eta ^ 3) * t * y 2 - t * eta * (1 - alpha) * y 3,
      (y 2 + eta * (1 - alpha) * y 3, y 5 + eta * (1 - alpha) * y 6)) =
      nestedScalarTargetPoint t eta alpha y 0 := by
  ext <;> dsimp [nestedScalarTargetPoint, nestedChartRadii,
    nestedCoordinates, nestedOuterRadialGaps, nestedOuterAngularGaps] <;> ring

theorem nestedOuterL_original_integral (eps t eta alpha : ℝ) (y : NestedChartVariables)
    (he : eta ≠ 0)
    (hsegment : ∀ s ∈ Icc (-(1 - alpha)) alpha,
      0 < nestedScalarTargetWSq t (nestedChartRadii t eta alpha y 2)
        (nestedOriginalScalarPath t eta alpha y s)) :
    (nestedOuterL eps t eta alpha y 1 - nestedOuterL eps t eta alpha y 0) / eta =
      ∫ s in (-(1 - alpha))..alpha,
        t * y 3 * (fderiv ℝ (nestedScalarAngularKernel eps t (nestedChartRadii t eta alpha y 2))
          (nestedOriginalScalarPath t eta alpha y s)) (1, (0, 0)) -
        y 3 * (fderiv ℝ (nestedScalarAngularKernel eps t (nestedChartRadii t eta alpha y 2))
          (nestedOriginalScalarPath t eta alpha y s)) (0, (1, 0)) -
        y 6 * (fderiv ℝ (nestedScalarAngularKernel eps t (nestedChartRadii t eta alpha y 2))
          (nestedOriginalScalarPath t eta alpha y s)) (0, (0, 1)) := by
  have H := nested_target_kernel_integral
    (nestedScalarAngularKernel eps t (nestedChartRadii t eta alpha y 2))
    {v | 0 < nestedScalarTargetWSq t (nestedChartRadii t eta alpha y 2) v}
    (nestedScalarKernel_domain_isOpen _ _) (nestedScalarAngularKernel_contDiffOn 1 _ _ _)
    (y 1 - (1 - eta ^ 3) * t * y 2) t eta alpha (y 2) (y 3) (y 5) (y 6) he hsegment
  rw [nestedOriginalScalarPath_left_explicit,
    ← show nestedOriginalScalarPath t eta alpha y alpha =
      (y 1 - (1 - eta ^ 3) * t * y 2 + t * eta * alpha * y 3,
        (y 2 - eta * alpha * y 3, y 5 - eta * alpha * y 6)) from rfl,
    (nestedOriginalScalarPath_endpoints t eta alpha y).2,
    nestedScalarAngularKernel_substitution, nestedScalarAngularKernel_substitution] at H
  exact H

theorem nestedOuterN_original_integral (t eta alpha : ℝ) (y : NestedChartVariables)
    (he : eta ≠ 0)
    (hsegment : ∀ s ∈ Icc (-(1 - alpha)) alpha,
      0 < nestedScalarTargetWSq t (nestedChartRadii t eta alpha y 2)
        (nestedOriginalScalarPath t eta alpha y s)) :
    (nestedOuterN t eta alpha y 1 - nestedOuterN t eta alpha y 0) / eta =
      ∫ s in (-(1 - alpha))..alpha,
        t * y 3 * (fderiv ℝ (nestedScalarRadialKernel t (nestedChartRadii t eta alpha y 2))
          (nestedOriginalScalarPath t eta alpha y s)) (1, (0, 0)) -
        y 3 * (fderiv ℝ (nestedScalarRadialKernel t (nestedChartRadii t eta alpha y 2))
          (nestedOriginalScalarPath t eta alpha y s)) (0, (1, 0)) -
        y 6 * (fderiv ℝ (nestedScalarRadialKernel t (nestedChartRadii t eta alpha y 2))
          (nestedOriginalScalarPath t eta alpha y s)) (0, (0, 1)) := by
  have H := nested_target_kernel_integral
    (nestedScalarRadialKernel t (nestedChartRadii t eta alpha y 2))
    {v | 0 < nestedScalarTargetWSq t (nestedChartRadii t eta alpha y 2) v}
    (nestedScalarKernel_domain_isOpen _ _) (nestedScalarRadialKernel_contDiffOn 1 _ _)
    (y 1 - (1 - eta ^ 3) * t * y 2) t eta alpha (y 2) (y 3) (y 5) (y 6) he hsegment
  rw [nestedOriginalScalarPath_left_explicit,
    ← show nestedOriginalScalarPath t eta alpha y alpha =
      (y 1 - (1 - eta ^ 3) * t * y 2 + t * eta * alpha * y 3,
        (y 2 - eta * alpha * y 3, y 5 - eta * alpha * y 6)) from rfl,
    (nestedOriginalScalarPath_endpoints t eta alpha y).2,
    nestedScalarRadialKernel_substitution, nestedScalarRadialKernel_substitution] at H
  exact H

/-- The original integral path is regular on a common signed-scale tube,
uniformly in the entire closed individual mass interval. Thus the segment
regularity used above is derived locally from the actual source base. -/
theorem nestedOriginalScalarPath_positive_common_tube (psi omega : ℝ)
    (hw : |omega| = 1) :
    ∃ delta : ℝ, 0 < delta ∧
      ∀ alpha0 ∈ Icc (0 : ℝ) 1, ∀ v : NestedJointVariables,
        dist v (nestedParameter 0 0 0 alpha0, nestedBasePoint psi omega) < delta →
        ∀ s ∈ Icc (-1 : ℝ) 1,
          0 < nestedScalarTargetWSq (v.1 1)
            (nestedChartRadii (v.1 1) (v.1 2) (v.1 3) v.2 2)
            (nestedOriginalScalarPath (v.1 1) (v.1 2) (v.1 3) v.2 s) := by
  let center (p : ℝ × ℝ) : NestedJointVariables × ℝ :=
    ((nestedParameter 0 0 0 p.1, nestedBasePoint psi omega), p.2)
  let K : Set (NestedJointVariables × ℝ) := center '' (Icc (0 : ℝ) 1 ×ˢ Icc (-1 : ℝ) 1)
  let val (v : NestedJointVariables × ℝ) : ℝ :=
    nestedScalarTargetWSq (v.1.1 1)
      (nestedChartRadii (v.1.1 1) (v.1.1 2) (v.1.1 3) v.1.2 2)
      (nestedOriginalScalarPath (v.1.1 1) (v.1.1 2) (v.1.1 3) v.1.2 v.2)
  let U : Set (NestedJointVariables × ℝ) := {v | 0 < val v}
  have hc : Continuous val := by
    unfold val nestedScalarTargetWSq nestedOriginalScalarPath nestedChartRadii nestedCoordinates
    fun_prop
  have hU : IsOpen U := isOpen_lt continuous_const hc
  have hK : IsCompact K := (isCompact_Icc.prod isCompact_Icc).image (by
    unfold center nestedParameter
    fun_prop)
  have hbase (a s : ℝ) : 0 < val (center (a, s)) := by
    have hZ := nestedBasePoint_outer_ne_zero omega hw
    simpa [val, center, nestedScalarTargetWSq, nestedOriginalScalarPath,
      nestedParameter, nestedChartRadii, nestedCoordinates, nestedBasePoint, nestedUnitPoint]
      using sq_pos_of_ne_zero hZ
  obtain ⟨delta, hd, htube⟩ := compact_uniform_neighborhood K U hK (by
    rintro x ⟨p, _, rfl⟩
    exact hU.mem_nhds (hbase p.1 p.2))
  refine ⟨delta, hd, ?_⟩
  intro a ha v hv s hs
  have hmem : center (a, s) ∈ K := ⟨(a,s), ⟨ha,hs⟩, rfl⟩
  have hdist : dist (v,s) (center (a,s)) < delta := by
    simpa only [center, dist_prod_same_right] using hv
  exact htube (center (a,s)) hmem (v,s) hdist

end DominantFiveBody
