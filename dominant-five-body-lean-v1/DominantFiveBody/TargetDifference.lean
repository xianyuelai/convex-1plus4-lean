import DominantFiveBody.SingleScaleKernel
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-! # The original fixed-target Hadamard identity

Source: §5 `eq:hadamard`. The derivative is taken along the whole moving
target segment. All continuity and integrability obligations are explicit.
This identity alone does not claim that a parameter-dependent graph root has
been held fixed or that differentiation under an integral needs no proof.
-/

noncomputable section
open Filter Set Topology
open scoped Interval BigOperators

namespace DominantFiveBody

def targetLine (p v : ℝ×ℝ) (t lambda : ℝ) : ℝ×ℝ := p+(lambda*t) • v

theorem targetLine_hasDerivAt (p v : ℝ×ℝ) (t lambda : ℝ) :
    HasDerivAt (targetLine p v t) (t • v) lambda := by
  convert! (((hasDerivAt_id lambda).mul_const t).smul_const v).const_add p using 1
  simp

theorem target_hadamard_identity (K : (ℝ×ℝ) → ℝ) (p v : ℝ×ℝ) (t : ℝ) (ht : t≠0)
    (hdiff : ∀ lambda ∈ Set.uIcc (0 : ℝ) 1,
      DifferentiableAt ℝ K (targetLine p v t lambda))
    (hcont : ContinuousOn (fun lambda => fderiv ℝ K (targetLine p v t lambda) v)
      (Set.uIcc (0 : ℝ) 1)) :
    (K (p+t • v)-K p)/t =
      ∫ lambda in (0 : ℝ)..1, fderiv ℝ K (targetLine p v t lambda) v := by
  have hd (lambda : ℝ) (hl : lambda ∈ Set.uIcc (0 : ℝ) 1) :
      HasDerivAt (fun s : ℝ => K (targetLine p v t s))
        (t*fderiv ℝ K (targetLine p v t lambda) v) lambda := by
    convert! (hdiff lambda hl).hasFDerivAt.comp_hasDerivAt lambda
      (targetLine_hasDerivAt p v t lambda) using 1
    simp only [map_smul, smul_eq_mul]
  have hi : IntervalIntegrable (fun lambda => t*fderiv ℝ K (targetLine p v t lambda) v)
      MeasureTheory.volume 0 1 :=
    (continuousOn_const.mul hcont).intervalIntegrable
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt hd hi
  rw [intervalIntegral.integral_const_mul] at hFTC
  simp only [targetLine, one_mul, zero_mul, zero_smul, add_zero] at hFTC
  rw [← hFTC]
  exact mul_div_cancel_left₀ _ ht

theorem targetDerivative_coordinates (K : (ℝ×ℝ) → ℝ) (p v : ℝ×ℝ) :
    fderiv ℝ K p v = v.1*fderiv ℝ K p (1,0)+v.2*fderiv ℝ K p (0,1) := by
  have heq : v=v.1 • ((1,0) : ℝ×ℝ)+v.2 • ((0,1) : ℝ×ℝ) := by
    ext <;> simp
  conv_lhs => rw [heq]
  rw [map_add, map_smul, map_smul]
  rfl

/-- The displayed coordinate integrand uKρ+zKv in the manuscript is the
actual differential applied to (u,z), at every point of the segment. -/
theorem target_hadamard_coordinate_identity (K : (ℝ×ℝ) → ℝ)
    (rho phi u z t : ℝ) (ht : t≠0)
    (hdiff : ∀ lambda ∈ Set.uIcc (0 : ℝ) 1,
      DifferentiableAt ℝ K (rho+lambda*t*u,phi+lambda*t*z))
    (hcont : ContinuousOn (fun lambda =>
      u*fderiv ℝ K (rho+lambda*t*u,phi+lambda*t*z) (1,0)+
        z*fderiv ℝ K (rho+lambda*t*u,phi+lambda*t*z) (0,1))
      (Set.uIcc (0 : ℝ) 1)) :
    (K (rho+t*u,phi+t*z)-K (rho,phi))/t =
      ∫ lambda in (0 : ℝ)..1,
        (u*fderiv ℝ K (rho+lambda*t*u,phi+lambda*t*z) (1,0)+
          z*fderiv ℝ K (rho+lambda*t*u,phi+lambda*t*z) (0,1)) := by
  have heq (lambda : ℝ) : targetLine (rho,phi) (u,z) t lambda=
      (rho+lambda*t*u,phi+lambda*t*z) := by rfl
  have hDf (lambda : ℝ) : fderiv ℝ K (targetLine (rho,phi) (u,z) t lambda) (u,z)=
      u*fderiv ℝ K (rho+lambda*t*u,phi+lambda*t*z) (1,0)+
        z*fderiv ℝ K (rho+lambda*t*u,phi+lambda*t*z) (0,1) := by
    rw [heq, targetDerivative_coordinates]
  have h := target_hadamard_identity K (rho,phi) (u,z) t ht
    (by simpa only [heq] using hdiff) (by simpa only [hDf] using hcont)
  simp_rw [hDf] at h
  simpa only [targetLine, Prod.smul_mk, smul_eq_mul, Prod.mk_add_mk] using h

end DominantFiveBody
