import DominantFiveBody.SlowTaylorOrders

/-! First-order expansion of the actual Newton field along the exact
polar curves. Smoothness of the signed divided Newton field proves the
quadratic remainder on a real neighborhood of scale zero. -/
noncomputable section
open scoped BigOperators ContDiff
open Filter Set Topology Asymptotics
namespace DominantFiveBody
set_option maxHeartbeats 1000000

local instance slowNewtonPlaneAddCommGroup : AddCommGroup Plane :=
  (inferInstance : NormedAddCommGroup Plane).toAddCommGroup
local instance slowNewtonPlaneModule : Module ℝ Plane :=
  (inferInstance : NormedSpace ℝ Plane).toModule

theorem newtonTargetField_affinePolar_Osquare (source : Plane) (R psi w z : ℝ)
    (hsep : source ≠ polarPoint R psi) :
    (fun t : ℝ => newtonTargetField source (affinePolarPoint R psi w z t) -
      newtonTargetField source (polarPoint R psi) -
      t • newtonTargetDerivative source (polarPoint R psi)
        (polarPointDerivative (R, psi) (w, z))) =O[𝓝 0] (fun t : ℝ => t ^ 2) := by
  let q0 := polarPoint R psi
  let q := affinePolarPoint R psi w z
  let D := affinePolarDirection R psi w z
  let C (t : ℝ) : Plane := dividedNewtonTargetField source q0 (q t) (D t)
  have hq0 : q 0 = q0 := by simp [q, q0, affinePolarPoint]
  have hD0 : D 0 = polarPointDerivative (R, psi) (w, z) := affinePolarDirection_zero R psi w z
  have hp : ContDiff ℝ 1 (fun t : ℝ => ((source, q0), (q t, D t))) :=
    contDiff_const.prodMk ((affinePolarPoint_contDiff 1 R psi w z).prodMk
      (affinePolarDirection_contDiff 1 R psi w z))
  have hfield := dividedNewtonTargetField_joint_contDiffAt 1 ((source, q0), (q 0, D 0))
    hsep (by rwa [hq0])
  have hcomposed := hfield.comp (f := fun t : ℝ => ((source, q0), (q t, D t))) 0 hp.contDiffAt
  have hC : ContDiffAt ℝ 1 C 0 := hcomposed
  have hCd : DifferentiableAt ℝ C 0 := hC.differentiableAt (by norm_num)
  have hCO := hCd.hasDerivAt.isBigO_sub
  simp only [sub_zero] at hCO
  have hmul := (isBigO_refl (fun t : ℝ => t) (𝓝 (0 : ℝ))).smul hCO
  have hC0 : C 0 = newtonTargetDerivative source q0 (polarPointDerivative (R, psi) (w, z)) := by
    dsimp only [C]
    rw [hq0, hD0, dividedNewtonTargetField_diagonal source q0 _ hsep,
      (newtonTargetField_hasFDerivAt source q0 hsep).fderiv]
  have hsepNear : ∀ᶠ t : ℝ in 𝓝 0, source ≠ q t :=
    (isClosed_eq continuous_const (affinePolarPoint_contDiff 0 R psi w z).continuous).isOpen_compl.mem_nhds
      (by change source ≠ q 0; rwa [hq0])
  have heq : (fun t : ℝ => newtonTargetField source (q t) - newtonTargetField source q0 -
      t • newtonTargetDerivative source q0 (polarPointDerivative (R, psi) (w, z))) =ᶠ[𝓝 0]
      (fun t => t • (C t - C 0)) := by
    filter_upwards [hsepNear] with t hs
    by_cases ht : t = 0
    · subst t
      simp [hq0]
    · have hd := dividedNewtonTargetField_eq source q0 (q t) (D t) t ht hsep hs
        (affinePolarPoint_divided_identity R psi w z t)
      have hi : newtonTargetField source (q t) - newtonTargetField source q0 = t • C t := by
        rw [show C t = t⁻¹ • (newtonTargetField source (q t) - newtonTargetField source q0) from hd,
          smul_smul, mul_inv_cancel₀ ht, one_smul]
      rw [hi, ← hC0]
      module
  exact hmul.congr' heq.symm (Eventually.of_forall (fun t => by simp [smul_eq_mul, pow_two]))

theorem backgroundProbeField_affinePolar_Osquare (eps tau w z : ℝ)
    (heps : 0 < 1 + eps) (htau : tau = 1 ∨ tau = -1) :
    (fun t : ℝ => backgroundProbeField eps
        (affinePolarPoint (backgroundRadius eps) (tau * Coorbital.h) w z t) -
      t • backgroundOperator eps tau
        (polarPointDerivative (backgroundRadius eps, tau * Coorbital.h) (w, z)))
      =O[𝓝 0] (fun t : ℝ => t ^ 2) := by
  let a := backgroundRadius eps
  let psi := tau * Coorbital.h
  let b := polarPointDerivative (a, psi) (w, z)
  have hzero : (0 : Plane) ≠ polarPoint a psi := by
    have ha := backgroundRadius_pos eps heps
    intro hz
    have hn := polarPoint_norm a psi
    rw [← hz, norm_zero, abs_of_pos ha] at hn
    linarith
  have hext : backgroundExterior eps ≠ polarPoint a psi := by
    have hh := backgroundExterior_ne_probeCenter eps tau heps htau
    rw [polarPoint_smul_one]
    exact hh
  have hq := affinePolarPoint_cartesian_Osquare a psi w z
  have hprimary := newtonTargetField_affinePolar_Osquare 0 a psi w z hzero
  have hexterior := (newtonTargetField_affinePolar_Osquare (backgroundExterior eps)
    a psi w z hext).const_smul_left eps
  have hsum := (hq.add hprimary).add hexterior
  have hvalue := backgroundProbeField_zero eps tau heps htau
  have hbase : polarPoint a psi = backgroundProbeCenter eps tau := by
    rw [polarPoint_smul_one]
    rfl
  have hB : backgroundOperator eps tau b = b + newtonTargetDerivative 0 (polarPoint a psi) b +
      eps • newtonTargetDerivative (backgroundExterior eps) (polarPoint a psi) b := by
    have hd := (((hasFDerivAt_id (polarPoint a psi)).add
      (newtonTargetField_hasFDerivAt 0 _ hzero)).add
      ((newtonTargetField_hasFDerivAt (backgroundExterior eps) _ hext).const_smul eps)).sub_const
        ((eps / a ^ 3) • backgroundExterior eps)
    have hb := backgroundProbeField_hasFDerivAt eps tau heps htau
    rw [← hbase] at hb
    have hh := hb.unique hd
    have hv := congrArg (fun L : Plane →L[ℝ] Plane => L b) hh
    simpa only [add_apply, smul_apply, ContinuousLinearMap.id_apply] using hv
  have heq : (fun t : ℝ => backgroundProbeField eps (affinePolarPoint a psi w z t) -
      t • backgroundOperator eps tau b) =
      (fun t : ℝ =>
        (affinePolarPoint a psi w z t - polarPoint a psi - t • b) +
        (newtonTargetField 0 (affinePolarPoint a psi w z t) - newtonTargetField 0 (polarPoint a psi) -
          t • newtonTargetDerivative 0 (polarPoint a psi) b) +
        eps • (newtonTargetField (backgroundExterior eps) (affinePolarPoint a psi w z t) -
          newtonTargetField (backgroundExterior eps) (polarPoint a psi) -
          t • newtonTargetDerivative (backgroundExterior eps) (polarPoint a psi) b)) := by
    funext t
    rw [hB]
    have hv : (eps / a ^ 3) • backgroundExterior eps = polarPoint a psi +
        newtonTargetField 0 (polarPoint a psi) +
        eps • newtonTargetField (backgroundExterior eps) (polarPoint a psi) := by
      have hh := sub_eq_zero.mp hvalue
      change _ = (eps / a ^ 3) • backgroundExterior eps at hh
      rw [← hbase] at hh
      exact hh.symm
    unfold backgroundProbeField
    rw [hv]
    module
  rw [heq]
  exact hsum

end DominantFiveBody
