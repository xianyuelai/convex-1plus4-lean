import DominantFiveBody.TripleHessian
import DominantFiveBody.TripleZeroEndpoint
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-! # Inverse regular-triple coordinates for actual physical solutions

Source §5.3. Every positive physical mass vector and exterior-angle gauge
has explicit chart coordinates. Regularity and the actual extended root
equations are derived from genuine physical collision-free solutions.
-/

noncomputable section
open scoped BigOperators Matrix ContDiff

namespace DominantFiveBody
set_option maxHeartbeats 800000

def tripleRawSlice (r theta : Satellite → ℝ) : SliceCoordinates :=
  ![r 3, r 1, r 2, r 0, theta 1, theta 2, theta 0]

def tripleVariablesFromPolar (t : ℝ) (alpha : TripleVector) (r theta : Satellite → ℝ) :
    TripleChartVariables := tripleFromFixedSlice t alpha (tripleRawSlice r theta)

theorem tripleVariablesFromPolar_radii (t : ℝ) (alpha : TripleVector) (r theta : Satellite → ℝ)
    (ht : t ≠ 0) (ha : ∑ i, alpha i = 1) :
    tripleChartRadii t alpha (tripleVariablesFromPolar t alpha r theta) = r := by
  rw [← fixedAngleRadii_tripleToFixedSlice, tripleVariablesFromPolar,
    tripleToFixedSlice_tripleFromFixedSlice t alpha ht ha]
  ext i
  fin_cases i <;> rfl

theorem tripleVariablesFromPolar_angles (t : ℝ) (alpha : TripleVector) (r theta : Satellite → ℝ)
    (ht : t ≠ 0) (ha : ∑ i, alpha i = 1) (hfixed : theta 3 = 0) :
    tripleChartAngles t alpha (tripleVariablesFromPolar t alpha r theta) = theta := by
  rw [← fixedAngleAngles_tripleToFixedSlice, tripleVariablesFromPolar,
    tripleToFixedSlice_tripleFromFixedSlice t alpha ht ha]
  ext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact hfixed.symm

theorem tripleVariablesFromPolar_points (t : ℝ) (alpha : TripleVector) (r theta : Satellite → ℝ)
    (ht : t ≠ 0) (ha : ∑ i, alpha i = 1) (hfixed : theta 3 = 0) :
    tripleChartPoints t alpha (tripleVariablesFromPolar t alpha r theta) = polarSatellites r theta := by
  rw [tripleChartPoints, tripleVariablesFromPolar_radii t alpha r theta ht ha,
    tripleVariablesFromPolar_angles t alpha r theta ht ha hfixed]

def triplePhysicalClusterMass (mu : MassRatio) : ℝ := ∑ i : TripleLabel, mu i.castSucc

def triplePhysicalScale (mu : MassRatio) : ℝ := Real.rpow (triplePhysicalClusterMass mu) (1 / 3)

def triplePhysicalWeights (mu : MassRatio) : TripleVector :=
  fun i => mu i.castSucc / triplePhysicalClusterMass mu

theorem triplePhysicalClusterMass_pos (mu : MassRatio) (hm : PositiveRatio mu) :
    0 < triplePhysicalClusterMass mu := by
  unfold triplePhysicalClusterMass
  apply Finset.sum_pos
  · intro i _
    exact hm.1 i.castSucc
  · exact Finset.univ_nonempty

theorem triplePhysicalWeights_positive (mu : MassRatio) (hm : PositiveRatio mu) :
    ∀ i, 0 < triplePhysicalWeights mu i :=
  fun i => div_pos (hm.1 i.castSucc) (triplePhysicalClusterMass_pos mu hm)

theorem triplePhysicalWeights_sum (mu : MassRatio) (hm : PositiveRatio mu) :
    ∑ i, triplePhysicalWeights mu i = 1 := by
  simp only [triplePhysicalWeights]
  rw [← Finset.sum_div]
  exact div_self (triplePhysicalClusterMass_pos mu hm).ne'

theorem triplePhysicalScale_cube (mu : MassRatio) (hm : PositiveRatio mu) :
    triplePhysicalScale mu ^ 3 = triplePhysicalClusterMass mu := by
  simpa [triplePhysicalScale, one_div] using Real.rpow_inv_natCast_pow
    (triplePhysicalClusterMass_pos mu hm).le (by decide : (3 : ℕ) ≠ 0)

theorem triplePhysicalParameters_bounds (mu : MassRatio) (hm : PositiveRatio mu) :
    0 < triplePhysicalScale mu ∧ triplePhysicalScale mu < 1 ∧
      TripleWeights (triplePhysicalWeights mu) := by
  have hnu := triplePhysicalClusterMass_pos mu hm
  have ht : 0 < triplePhysicalScale mu := Real.rpow_pos_of_pos hnu _
  have hsum : triplePhysicalClusterMass mu + mu 3 = 1 := by
    simpa [triplePhysicalClusterMass, Fin.sum_univ_three, Fin.sum_univ_four] using hm.2
  have hcube := triplePhysicalScale_cube mu hm
  have ht1 : triplePhysicalScale mu < 1 := by
    by_contra hn
    have hle := le_of_not_gt hn
    nlinarith [hm.1 3, mul_nonneg (sub_nonneg.mpr hle) (sq_nonneg (triplePhysicalScale mu))]
  exact ⟨ht, ht1, fun i => (triplePhysicalWeights_positive mu hm i).le, triplePhysicalWeights_sum mu hm⟩

theorem triplePhysicalParameters_mass (mu : MassRatio) (hm : PositiveRatio mu) :
    tripleChartMass (triplePhysicalScale mu) (triplePhysicalWeights mu) = mu := by
  have hnu := (triplePhysicalClusterMass_pos mu hm).ne'
  have hsum : triplePhysicalClusterMass mu + mu 3 = 1 := by
    simpa [triplePhysicalClusterMass, Fin.sum_univ_three, Fin.sum_univ_four] using hm.2
  ext i
  fin_cases i
  all_goals simp [tripleChartMass, triplePhysicalScale_cube mu hm,
    triplePhysicalWeights]
  all_goals first
    | solve | field_simp
    | solve | linarith

theorem tripleChart_distance_sq (t : ℝ) (alpha : TripleVector) (y : TripleChartVariables)
    (i j : TripleLabel) :
    satelliteDistance (tripleChartPoints t alpha y) i.castSucc j.castSucc ^ 2 =
      t ^ 2 * tripleChartWSq t alpha y i j := by
  unfold satelliteDistance tripleChartPoints polarSatellites
  rw [tripleChartRadii_cluster, tripleChartRadii_cluster,
    tripleChartAngles_cluster, tripleChartAngles_cluster]
  exact singleScale_distance_sq (y 1) (y 4) t _ _ _ _

theorem tripleVariablesFromPolar_regular (eps t : ℝ) (alpha : TripleVector)
    (r theta : Satellite → ℝ) (heps : 1 + eps ≠ 0) (ht : 0 < t)
    (ha : ∑ i, alpha i = 1) (hr : ∀ i, 0 < r i) (hfixed : theta 3 = 0)
    (hcf : RelativeCollisionFree (polarSatellites r theta)) :
    TripleChartRegular eps t alpha (tripleVariablesFromPolar t alpha r theta) := by
  let y := tripleVariablesFromPolar t alpha r theta
  have hradii := tripleVariablesFromPolar_radii t alpha r theta ht.ne' ha
  have hpoints := tripleVariablesFromPolar_points t alpha r theta ht.ne' ha hfixed
  refine ⟨heps, ?_, ?_, ?_⟩
  · intro i
    rw [hradii]
    exact (hr i).ne'
  · intro i j hij
    have hd : 0 < satelliteDistance (tripleChartPoints t alpha y) i.castSucc j.castSucc := by
      rw [hpoints]
      apply norm_pos_iff.mpr
      apply sub_ne_zero.mpr
      apply hcf.2
      intro hc
      apply hij
      apply Fin.ext
      exact congrArg (fun k : Fin 4 => k.val) hc
    have he := tripleChart_distance_sq t alpha y i j
    have hmul : 0 < t ^ 2 * tripleChartWSq t alpha y i j := by rw [← he]; positivity
    exact (mul_pos_iff_of_pos_left (sq_pos_of_pos ht)).mp hmul
  · intro i
    rw [hpoints]
    exact hcf.2 3 i.castSucc (by fin_cases i <;> decide)

/-- Actual physical entry point. The chart equations follow from the
original normalized Newton equations and explicit inverse coordinates. -/
theorem triplePhysicalCoordinates_root (eps : ℝ) (mu : MassRatio) (heps : 0 < eps)
    (hm : PositiveRatio mu) (r theta : Satellite → ℝ) (hr : ∀ i, 0 < r i)
    (hfixed : theta 3 = 0) (hcf : RelativeCollisionFree (polarSatellites r theta))
    (hx : NormalizedCentralConfiguration (masses eps mu)
      (centeredFromRelative eps mu (polarSatellites r theta))) :
    tripleChartExtendedRows eps (triplePhysicalScale mu) (triplePhysicalWeights mu)
      (tripleVariablesFromPolar (triplePhysicalScale mu) (triplePhysicalWeights mu) r theta) = 0 := by
  have ht := (triplePhysicalParameters_bounds mu hm).1
  have ha := triplePhysicalWeights_sum mu hm
  have hmass := triplePhysicalParameters_mass mu hm
  have hradii := tripleVariablesFromPolar_radii (triplePhysicalScale mu) (triplePhysicalWeights mu) r theta ht.ne' ha
  have hpoints := tripleVariablesFromPolar_points (triplePhysicalScale mu) (triplePhysicalWeights mu) r theta ht.ne' ha hfixed
  have hreg := tripleVariablesFromPolar_regular eps (triplePhysicalScale mu) (triplePhysicalWeights mu)
    r theta (by linarith) ht ha hr hfixed hcf
  apply (tripleChartExtendedRows_zero_iff_normalized _ _ _ _ heps ht ha
    (by rwa [hmass]) hreg (by intro i; rw [hradii]; exact hr i)).mpr
  simpa only [hmass, hpoints] using hx

end DominantFiveBody
