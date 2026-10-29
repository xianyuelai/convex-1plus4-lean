import DominantFiveBody.SlowTaylorOrders
import DominantFiveBody.NestedSlowCoordinates

/-! Exact off-solution identities and the fixed-exterior cubic field defect.

The field defect is the paper's `Y - c_eps X`, rather than the previously
exported change of the action reaction vector.  No individual satellite mass
is divided out.  The cubic estimate is local at a nonzero cluster center;
it does not assume that the trial path solves the central equations.
-/

noncomputable section
open scoped BigOperators ContDiff
open Filter Set Topology Asymptotics
namespace DominantFiveBody
set_option maxHeartbeats 1000000

local instance v1BoundaryPlaneAddCommGroup : AddCommGroup Plane :=
  (inferInstance : NormedAddCommGroup Plane).toAddCommGroup
local instance v1BoundaryPlaneModule : Module ℝ Plane :=
  (inferInstance : NormedSpace ℝ Plane).toModule

/-- The off-solution defect `Y - c_eps X`. -/
def v1FieldDefect (eps : ℝ) (mu : MassRatio) (q : SatelliteConfiguration) : Plane :=
  relativeField mu q - (1 + eps)⁻¹ • relativeAverage mu q

/-- The mass-divided action row, before taking its polar projections. -/
def v1CorrectedVectorResidual (eps : ℝ) (mu : MassRatio)
    (q : SatelliteConfiguration) (i : Satellite) : Plane :=
  vectorResidual eps mu q i + eps • v1FieldDefect eps mu q

theorem v1CorrectedVectorResidual_eq (eps : ℝ) (mu : MassRatio)
    (q : SatelliteConfiguration) (i : Satellite) :
    v1CorrectedVectorResidual eps mu q i =
      q i - (‖q i‖ ^ 3)⁻¹ • q i + eps • satelliteInteraction mu q i -
        (eps / (1 + eps)) • relativeAverage mu q := by
  unfold v1CorrectedVectorResidual vectorResidual v1FieldDefect satelliteInteraction
  simp only [div_eq_mul_inv, smul_sub, smul_smul]
  module

/-- Exact radial identity off the solution set, including zero individual masses. -/
theorem v1_radialResidual_corrected_projection (eps : ℝ)
    (mu r theta : Satellite → ℝ) (hr : ∀ i, 0 < r i) (i : Satellite) :
    radialResidual eps mu r theta i =
      inner ℝ (v1CorrectedVectorResidual eps mu (polarSatellites r theta) i)
        (polarPoint 1 (theta i)) := by
  have hnorm : ‖polarSatellites r theta i‖ = r i := by
    simpa only [polarSatellites, abs_of_pos (hr i)] using polarPoint_norm (r i) (theta i)
  have hinner : inner ℝ (polarSatellites r theta i) (polarPoint 1 (theta i)) = r i := by
    simpa only [polarSatellites, sub_self, Real.cos_zero, mul_one] using
      polarPoint_inner_radial (r i) (theta i) (theta i)
  have hint : inner ℝ (satelliteInteraction mu (polarSatellites r theta) i)
      (polarPoint 1 (theta i)) =
      ∑ j ∈ Finset.univ.erase i, mu j * inner ℝ
        (newtonTargetField (polarSatellites r theta j) (polarSatellites r theta i))
          (polarPoint 1 (theta i)) := by
    simp only [satelliteInteraction, newtonTargetField, satelliteDistance,
      sum_inner, real_inner_smul_left, norm_sub_rev, div_eq_mul_inv, mul_assoc]
  have hrad : r i - (r i ^ 3)⁻¹ * r i = r i - (r i ^ 2)⁻¹ := by
    field_simp [ne_of_gt (hr i)]
  rw [v1CorrectedVectorResidual_eq]
  simp only [inner_sub_left, inner_add_left, real_inner_smul_left, hnorm, hinner, hint]
  rw [radialResidual_newton_projection]
  rw [hrad]

/-- The angular identity without dividing by either epsilon or an individual mass. -/
theorem v1CorrectedVectorResidual_angular (eps : ℝ)
    (mu r theta : Satellite → ℝ) (i : Satellite) :
    inner ℝ (v1CorrectedVectorResidual eps mu (polarSatellites r theta) i)
      (quarterTurn (polarSatellites r theta i)) = eps * angularResidual eps mu r theta i := by
  have hint : inner ℝ (satelliteInteraction mu (polarSatellites r theta) i)
      (quarterTurn (polarSatellites r theta i)) =
      ∑ j ∈ Finset.univ.erase i, mu j * r i * r j * Real.sin (theta j - theta i) /
        satelliteDistance (polarSatellites r theta) i j ^ 3 := by
    unfold satelliteInteraction
    simp only [sum_inner, real_inner_smul_left, inner_sub_left, quarterTurn_inner_self,
      sub_zero, polarSatellites, polarPoint_inner_rotation]
    apply Finset.sum_congr rfl
    intro j _
    ring
  have havg : inner ℝ (relativeAverage mu (polarSatellites r theta))
      (quarterTurn (polarSatellites r theta i)) =
      ∑ j ∈ Finset.univ.erase i, mu j * r i * r j * Real.sin (theta j - theta i) := by
    simp only [relativeAverage, sum_inner, real_inner_smul_left, polarSatellites,
      polarPoint_inner_rotation]
    rw [Finset.sum_erase_eq_sub (Finset.mem_univ i)]
    simp only [sub_self, Real.sin_zero, mul_zero, sub_zero]
    apply Finset.sum_congr rfl
    intro j _
    ring
  rw [v1CorrectedVectorResidual_eq]
  simp only [inner_sub_left, inner_add_left, real_inner_smul_left,
    quarterTurn_inner_self, mul_zero, sub_zero, zero_add, hint, havg]
  unfold angularResidual
  simp_rw [mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul]
  simp only [div_eq_mul_inv, mul_assoc]
  ring

/-- The exact unit-tangent form `eps T_i = rho_i <F_i+eps(Y-cX),e_i^perp>`. -/
theorem v1_epsilon_angularResidual_corrected_projection (eps : ℝ)
    (mu r theta : Satellite → ℝ) (i : Satellite) :
    eps * angularResidual eps mu r theta i =
      r i * inner ℝ (v1CorrectedVectorResidual eps mu (polarSatellites r theta) i)
        (quarterTurn (polarPoint 1 (theta i))) := by
  rw [← v1CorrectedVectorResidual_angular]
  change inner ℝ _ (quarterTurn (polarPoint (r i) (theta i))) = _
  have hrot : quarterTurn (r i • polarPoint 1 (theta i)) =
      r i • quarterTurn (polarPoint 1 (theta i)) :=
    quarterTurnLinear.map_smul (r i) (polarPoint 1 (theta i))
  rw [polarPoint_smul_one, hrot, real_inner_smul_right]

theorem v1_angularResidual_corrected_projection_div (eps : ℝ)
    (mu r theta : Satellite → ℝ) (heps : eps ≠ 0) (i : Satellite) :
    angularResidual eps mu r theta i =
      (r i / eps) * inner ℝ
        (v1CorrectedVectorResidual eps mu (polarSatellites r theta) i)
        (quarterTurn (polarPoint 1 (theta i))) := by
  have h := v1_epsilon_angularResidual_corrected_projection eps mu r theta i
  field_simp [heps]
  nlinarith only [h]

theorem v1FieldDefect_eq_sum (eps : ℝ) (mu : MassRatio) (q : SatelliteConfiguration) :
    v1FieldDefect eps mu q =
      ∑ i, mu i • ((‖q i‖ ^ 3)⁻¹ • q i - (1 + eps)⁻¹ • q i) := by
  unfold v1FieldDefect relativeField relativeAverage
  simp only [smul_sub, smul_smul, Finset.sum_sub_distrib, Finset.smul_sum, div_eq_mul_inv]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  rw [mul_comm]

theorem v1_backgroundExterior_norm_cube (eps : ℝ) (heps : 0 < 1 + eps) :
    ‖backgroundExterior eps‖ ^ 3 = 1 + eps := by
  have ha := backgroundRadius_pos eps heps
  rw [backgroundExterior, norm_smul, Real.norm_eq_abs, abs_of_pos ha,
    polarPoint_norm, abs_one, mul_one]
  exact backgroundRadius_cube eps heps.le

/-- Exact factorization on every fixed-exterior path with cluster masses `t^3 omega`.
The exterior mass need not be divided out or even assumed positive. -/
theorem v1FieldDefect_cubic_factor (eps t : ℝ) (mu : MassRatio)
    (q : SatelliteConfiguration) (omega : TripleVector) (heps : 0 < 1 + eps)
    (hmass : ∀ i : TripleLabel, mu i.castSucc = t ^ 3 * omega i)
    (hfixed : q 3 = backgroundExterior eps) :
    v1FieldDefect eps mu q =
      t ^ 3 • ∑ i : TripleLabel, omega i •
        ((‖q i.castSucc‖ ^ 3)⁻¹ • q i.castSucc - (1 + eps)⁻¹ • q i.castSucc) := by
  have hzero : (‖q 3‖ ^ 3)⁻¹ • q 3 - (1 + eps)⁻¹ • q 3 = 0 := by
    rw [hfixed, v1_backgroundExterior_norm_cube eps heps, sub_self]
  have hm0 : mu 0 = t ^ 3 * omega 0 := hmass 0
  have hm1 : mu 1 = t ^ 3 * omega 1 := hmass 1
  have hm2 : mu 2 = t ^ 3 * omega 2 := hmass 2
  rw [v1FieldDefect_eq_sum, Fin.sum_univ_four, Fin.sum_univ_three]
  rw [hm0, hm1, hm2, hzero]
  simp only [smul_zero, add_zero, smul_add, smul_smul]
  rfl

/-- Continuity away from the primary proves the actual cubic defect estimate.
No central-configuration or candidate-root premise is used. -/
theorem v1FieldDefect_Ocube_of_fixed_exterior (eps : ℝ) (omega : TripleVector)
    (mu : ℝ → MassRatio) (q : ℝ → SatelliteConfiguration) (heps : 0 < 1 + eps)
    (hmass : ∀ t (i : TripleLabel), mu t i.castSucc = t ^ 3 * omega i)
    (hfixed : ∀ t, q t 3 = backgroundExterior eps)
    (hcont : ∀ i : TripleLabel, ContinuousAt (fun t : ℝ => q t i.castSucc) 0)
    (hnonzero : ∀ i : TripleLabel, q 0 i.castSucc ≠ 0) :
    (fun t : ℝ => v1FieldDefect eps (mu t) (q t)) =O[𝓝 0] (fun t : ℝ => t ^ 3) := by
  let C (t : ℝ) : Plane := ∑ i : TripleLabel, omega i •
    ((‖q t i.castSucc‖ ^ 3)⁻¹ • q t i.castSucc - (1 + eps)⁻¹ • q t i.castSucc)
  have hC : ContinuousAt C 0 := by
    apply tendsto_finsetSum Finset.univ
    intro i _
    have hinv := ((hcont i).norm.pow 3).inv₀
      (pow_ne_zero 3 (norm_ne_zero_iff.mpr (hnonzero i)))
    exact ((hinv.smul (hcont i)).sub ((hcont i).const_smul (1 + eps)⁻¹)).const_smul (omega i)
  have hbound : C =O[𝓝 0] (fun _ : ℝ => (1 : ℝ)) :=
    isBigO_const_of_tendsto hC (by norm_num)
  have hmul := (isBigO_refl (fun t : ℝ => t ^ 3) (𝓝 (0 : ℝ))).smul hbound
  have heq : (fun t : ℝ => v1FieldDefect eps (mu t) (q t)) = (fun t => t ^ 3 • C t) := by
    funext t
    exact v1FieldDefect_cubic_factor eps t (mu t) (q t) omega heps (hmass t) (hfixed t)
  simpa only [heq, smul_eq_mul, mul_one] using hmul

theorem v1_tripleChartPoints_fixed_exterior (t : ℝ) (alpha : TripleVector)
    (y : TripleChartVariables) :
    tripleChartPoints t alpha y 3 = polarPoint (y 0) 0 := rfl

theorem v1_nestedChartPoints_fixed_exterior (t eta alpha : ℝ) (y : NestedChartVariables) :
    nestedChartPoints t eta alpha y 3 = polarPoint (y 0) 0 := rfl

theorem v1_tripleChart_fieldDefect_cubic_factor (eps t : ℝ) (alpha : TripleVector)
    (y : TripleChartVariables) (heps : 0 < 1 + eps) (hfixed : y 0 = backgroundRadius eps) :
    v1FieldDefect eps (tripleChartMass t alpha) (tripleChartPoints t alpha y) =
      t ^ 3 • ∑ i : TripleLabel, alpha i •
        ((‖tripleChartPoints t alpha y i.castSucc‖ ^ 3)⁻¹ •
          tripleChartPoints t alpha y i.castSucc -
            (1 + eps)⁻¹ • tripleChartPoints t alpha y i.castSucc) := by
  apply v1FieldDefect_cubic_factor eps t _ _ alpha heps
  · intro i
    fin_cases i <;> rfl
  · rw [v1_tripleChartPoints_fixed_exterior, hfixed, polarPoint_smul_one]
    rfl

theorem v1_tripleChart_fieldDefect_Ocube (eps : ℝ) (alpha : TripleVector)
    (y : TripleChartVariables) (heps : 0 < 1 + eps)
    (hfixed : y 0 = backgroundRadius eps) (hcenter : y 1 ≠ 0) :
    (fun t : ℝ => v1FieldDefect eps (tripleChartMass t alpha)
      (tripleChartPoints t alpha y)) =O[𝓝 0] (fun t : ℝ => t ^ 3) := by
  apply v1FieldDefect_Ocube_of_fixed_exterior eps alpha
    (fun t => tripleChartMass t alpha) (fun t => tripleChartPoints t alpha y) heps
  · intro t i
    fin_cases i <;> rfl
  · intro t
    rw [v1_tripleChartPoints_fixed_exterior, hfixed, polarPoint_smul_one]
    rfl
  · intro i
    have hp (t : ℝ) : tripleChartPoints t alpha y i.castSucc =
        affinePolarPoint (y 1) (y 4) (tripleChartRadialPositions alpha y i)
          (tripleChartAngularPositions alpha y i) t := by
      change polarPoint (tripleChartRadii t alpha y i.castSucc)
        (tripleChartAngles t alpha y i.castSucc) = _
      rw [tripleChartRadii_cluster, tripleChartAngles_cluster]
      rfl
    simpa only [hp] using (affinePolarPoint_contDiff 0 (y 1) (y 4)
      (tripleChartRadialPositions alpha y i) (tripleChartAngularPositions alpha y i)).continuous.continuousAt
  · intro i
    rw [tripleChartPoints_zero_cluster]
    intro hz
    have hn := polarPoint_norm (y 1) (y 4)
    rw [hz, norm_zero] at hn
    exact hcenter (abs_eq_zero.mp hn.symm)

theorem v1_nestedChart_fieldDefect_cubic_factor (eps t eta alpha : ℝ)
    (y : NestedChartVariables) (heps : 0 < 1 + eps) (hfixed : y 0 = backgroundRadius eps) :
    v1FieldDefect eps (nestedChartMass t eta alpha) (nestedChartPoints t eta alpha y) =
      t ^ 3 • ∑ i : TripleLabel, nestedTripleWeights eta alpha i •
        ((‖nestedChartPoints t eta alpha y i.castSucc‖ ^ 3)⁻¹ •
          nestedChartPoints t eta alpha y i.castSucc -
            (1 + eps)⁻¹ • nestedChartPoints t eta alpha y i.castSucc) := by
  have h := v1_tripleChart_fieldDefect_cubic_factor eps t (nestedTripleWeights eta alpha)
    (nestedToTripleVariables eta alpha y) heps (by simpa [nestedToTripleVariables] using hfixed)
  simpa only [nestedToTriple_mass, nestedToTriple_points] using h

theorem v1_nestedChart_fieldDefect_Ocube (eps eta alpha : ℝ) (y : NestedChartVariables)
    (heps : 0 < 1 + eps) (hfixed : y 0 = backgroundRadius eps) (hcenter : y 1 ≠ 0) :
    (fun t : ℝ => v1FieldDefect eps (nestedChartMass t eta alpha)
      (nestedChartPoints t eta alpha y)) =O[𝓝 0] (fun t : ℝ => t ^ 3) := by
  have h := v1_tripleChart_fieldDefect_Ocube eps (nestedTripleWeights eta alpha)
    (nestedToTripleVariables eta alpha y) heps
    (by simpa [nestedToTripleVariables] using hfixed)
    (by simpa [nestedToTripleVariables] using hcenter)
  simpa only [nestedToTriple_mass, nestedToTriple_points] using h

theorem v1_tripleSlowPoint_fieldDefect_Ocube (eps tau : ℝ) (alpha : TripleVector)
    (g : TripleGaps) (heps : 0 < 1 + eps) :
    (fun t : ℝ => v1FieldDefect eps (tripleChartMass t alpha)
      (tripleChartPoints t alpha (tripleSlowPoint eps tau g)))
        =O[𝓝 0] (fun t : ℝ => t ^ 3) := by
  exact v1_tripleChart_fieldDefect_Ocube eps alpha _ heps rfl
    (ne_of_gt (backgroundRadius_pos eps heps))

theorem v1_nestedSlowPoint_fieldDefect_Ocube (eps tau eta alpha Z z : ℝ)
    (heps : 0 < 1 + eps) :
    (fun t : ℝ => v1FieldDefect eps (nestedChartMass t eta alpha)
      (nestedChartPoints t eta alpha (nestedSlowPoint eps tau Z z)))
        =O[𝓝 0] (fun t : ℝ => t ^ 3) := by
  exact v1_nestedChart_fieldDefect_Ocube eps eta alpha _ heps rfl
    (ne_of_gt (backgroundRadius_pos eps heps))

end DominantFiveBody
