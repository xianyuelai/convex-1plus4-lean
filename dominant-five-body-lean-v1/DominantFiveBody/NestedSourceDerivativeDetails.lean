import DominantFiveBody.NestedAngularMatrix

/-! Original scalar L0 and M0 derivative values, and independence of the
complete seven-dimensional boundary derivative from the pair fraction. -/
noncomputable section
open scoped BigOperators ContDiff
open Filter Set Topology
namespace DominantFiveBody
set_option maxHeartbeats 1000000

theorem nestedBoundaryKernel_unit_hasDerivAt (psi Z : ℝ) (hZ : Z ≠ 0) :
    HasDerivAt (fun r : ℝ => nestedBoundaryKernel 1 psi (0, r)) (-2 / |Z| ^ 3) Z := by
  exact (tripleScalarForce_hasDerivAt hZ).congr_of_eventuallyEq
    (Eventually.of_forall (fun r => nestedBoundaryKernel_unit psi r))

theorem nestedBoundaryKernel_unit_second_hasDerivAt (psi Z : ℝ) (hZ : Z ≠ 0) :
    HasDerivAt (fun r : ℝ => deriv (fun s : ℝ => nestedBoundaryKernel 1 psi (0, s)) r)
      (6 / (|Z| ^ 3 * Z)) Z := by
  have hnear : ∀ᶠ r : ℝ in 𝓝 Z, r ≠ 0 :=
    (isClosed_eq continuous_id continuous_const).isOpen_compl.mem_nhds hZ
  have heq : (fun r : ℝ => deriv (fun s : ℝ => nestedBoundaryKernel 1 psi (0, s)) r) =ᶠ[𝓝 Z]
      (fun r : ℝ => -(2 / |r| ^ 3)) := by
    filter_upwards [hnear] with r hr
    simpa only [neg_div] using (nestedBoundaryKernel_unit_hasDerivAt psi r hr).deriv
  convert! (twice_inverse_abs_cube_hasDerivAt Z hZ).neg.congr_of_eventuallyEq heq using 1
  ring

theorem nestedBoundaryKernel_original_derivatives (psi omega : ℝ) (hw : |omega| = 1) :
    let Z := omega * pairBoundaryScale tripleD0
    let z := pairBoundaryScale (3 * tripleD0)
    deriv (fun s : ℝ => nestedBoundaryKernel 1 psi (0, s)) Z = -2 * tripleD0 ∧
      deriv (fun r : ℝ => deriv (fun s : ℝ => nestedBoundaryKernel 1 psi (0, s)) r) Z =
        6 * tripleD0 / Z ∧
      deriv (fun s : ℝ => nestedBoundaryKernel 1 psi (0, s)) z = -6 * tripleD0 := by
  let Z := omega * pairBoundaryScale tripleD0
  let z := pairBoundaryScale (3 * tripleD0)
  have hZ : Z ≠ 0 := nestedBasePoint_outer_ne_zero omega hw
  have hz : z ≠ 0 := (pairBoundaryScale_pos (3 * tripleD0)
    (mul_pos (by norm_num) tripleD0_pos)).ne'
  obtain ⟨hZscale, hzscale⟩ := nestedBasePoint_diagonal_scales omega hw
  dsimp only
  refine ⟨?_, ?_, ?_⟩
  · rw [(nestedBoundaryKernel_unit_hasDerivAt psi Z hZ).deriv]
    rw [neg_div]
    rw [hZscale]
    ring
  · rw [(nestedBoundaryKernel_unit_second_hasDerivAt psi Z hZ).deriv]
    calc
      6 / (|Z| ^ 3 * Z) = 3 * (2 / |Z| ^ 3) / Z := by ring
      _ = _ := by rw [hZscale]; ring
  · rw [(nestedBoundaryKernel_unit_hasDerivAt psi z hz).deriv]
    rw [neg_div]
    rw [hzscale]
    ring

theorem nestedChartExtendedRows_boundary_alpha_independent (alpha beta : ℝ)
    (y : NestedChartVariables) (hsep : polarPoint (y 0) 0 ≠ polarPoint (y 1) (y 4))
    (hV : 0 < y 2 ^ 2 + y 1 ^ 2 * y 5 ^ 2) :
    nestedChartExtendedRows 0 0 0 alpha y = nestedChartExtendedRows 0 0 0 beta y := by
  ext i
  fin_cases i
  · simp [nestedChartExtendedRows, radialResidual, nestedChartRadii, nestedCoordinates]
  · change nestedRadialMean 0 0 0 alpha y = nestedRadialMean 0 0 0 beta y
    rw [nestedRadialMean_at_boundary, nestedRadialMean_at_boundary]
  · change nestedRadialOuterDifference 0 0 0 alpha y = nestedRadialOuterDifference 0 0 0 beta y
    rw [nestedRadialOuterDifference_at_boundary, nestedRadialOuterDifference_at_boundary]
  · change nestedRadialInnerDifference 0 0 0 alpha y = nestedRadialInnerDifference 0 0 0 beta y
    rw [nestedRadialInnerDifference_at_boundary, nestedRadialInnerDifference_at_boundary]
  · change nestedAngularMean 0 0 0 alpha y = nestedAngularMean 0 0 0 beta y
    rw [nestedAngularMean_at_boundary, nestedAngularMean_at_boundary]
  · change nestedAngularOuterDifference 0 0 0 alpha y = nestedAngularOuterDifference 0 0 0 beta y
    rw [nestedAngularOuterDifference_at_boundary alpha y hsep,
      nestedAngularOuterDifference_at_boundary beta y hsep]
  · change nestedAngularInnerDifference 0 0 0 alpha y = nestedAngularInnerDifference 0 0 0 beta y
    rw [nestedAngularInnerDifference_at_boundary alpha y hsep hV,
      nestedAngularInnerDifference_at_boundary beta y hsep hV]

/-- The entire actual derivative, including the radial-to-angular entries,
is the same for every alpha. This is stronger than determinant equality. -/
theorem nestedChartJacobian_boundary_alpha_independent (alpha beta psi omega : ℝ)
    (hangle : |psi| = Coorbital.h) (hw : |omega| = 1) :
    nestedChartJacobian 0 0 0 alpha (nestedBasePoint psi omega) =
      nestedChartJacobian 0 0 0 beta (nestedBasePoint psi omega) := by
  have hr := nestedBasePoint_regular alpha psi omega hangle hw
  have hsep : polarPoint (nestedBasePoint psi omega 0) 0 ≠
      polarPoint (nestedBasePoint psi omega 1) (nestedBasePoint psi omega 4) := by
    have hs := hr.2.2.2.2 0
    rw [nestedChartPoints_zero_exterior, nestedChartPoints_zero_cluster] at hs
    exact hs
  have hV : 0 < nestedBasePoint psi omega 2 ^ 2 +
      nestedBasePoint psi omega 1 ^ 2 * nestedBasePoint psi omega 5 ^ 2 := by
    simpa only [nestedOuterWSq_at_boundary] using hr.2.2.2.1 0
  have hsource : Continuous (fun y : NestedChartVariables => polarPoint (y 0) 0) :=
    (polarPoint_contDiff 0).continuous.comp (by fun_prop :
      Continuous (fun y : NestedChartVariables => (y 0, (0 : ℝ))))
  have htarget : Continuous (fun y : NestedChartVariables => polarPoint (y 1) (y 4)) :=
    (polarPoint_contDiff 0).continuous.comp (by fun_prop :
      Continuous (fun y : NestedChartVariables => (y 1, y 4)))
  have hsepNear : ∀ᶠ y : NestedChartVariables in 𝓝 (nestedBasePoint psi omega),
      polarPoint (y 0) 0 ≠ polarPoint (y 1) (y 4) :=
    (isClosed_eq hsource htarget).isOpen_compl.mem_nhds hsep
  have hVNear : ∀ᶠ y : NestedChartVariables in 𝓝 (nestedBasePoint psi omega),
      0 < y 2 ^ 2 + y 1 ^ 2 * y 5 ^ 2 :=
    (isOpen_lt continuous_const (by fun_prop)).mem_nhds hV
  have heq : nestedChartExtendedRows 0 0 0 alpha =ᶠ[𝓝 (nestedBasePoint psi omega)]
      nestedChartExtendedRows 0 0 0 beta := by
    filter_upwards [hsepNear, hVNear] with y hy hv
    exact nestedChartExtendedRows_boundary_alpha_independent alpha beta y hy hv
  exact heq.fderiv_eq

end DominantFiveBody
