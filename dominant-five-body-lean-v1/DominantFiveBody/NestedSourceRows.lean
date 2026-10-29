import DominantFiveBody.ChartScalarFields
import DominantFiveBody.NestedRegularization
import DominantFiveBody.OriginalNestedKernels

/-! Full original scalar rows, retaining the literal H/K differences,
L/N quotients and inner N/O kernels before taking either scale to zero. -/
noncomputable section
namespace DominantFiveBody
set_option maxHeartbeats 1000000

def nestedInnerN (t eta alpha : ℝ) (y : NestedChartVariables) : ℝ :=
  inner ℝ (nestedInnerNewton t eta alpha y) (polarPoint 1 (nestedChartAngles t eta alpha y 0))
def nestedInnerO (t eta alpha : ℝ) (y : NestedChartVariables) : ℝ :=
  inner ℝ (nestedInnerNewton t eta alpha y) (polarPoint 1 (nestedChartAngles t eta alpha y 1))

theorem nestedInnerN_source_formula (t eta alpha : ℝ) (y : NestedChartVariables) :
    nestedInnerN t eta alpha y = (y 3 - nestedChartRadii t eta alpha y 1 *
      singleScaleChi (t * eta) (y 6)) * (nestedInnerW t eta alpha y ^ 3)⁻¹ := by
  have h := pairPointDirection_radial_left (t * eta) alpha (nestedInnerVariables t eta y)
  have ha := (nestedInner_coordinates t eta alpha y 0).2
  have hb := (nestedInner_coordinates t eta alpha y 1).1
  change pairChartAngles (t * eta) alpha (nestedInnerVariables t eta y) 0 =
    nestedChartAngles t eta alpha y 0 at ha
  change pairChartRadii (t * eta) alpha (nestedInnerVariables t eta y) 1 =
    nestedChartRadii t eta alpha y 1 at hb
  rw [ha, hb] at h
  unfold nestedInnerN nestedInnerNewton scaledNewtonField
  rw [real_inner_smul_left, nestedInnerDirection_norm]
  change (nestedInnerW t eta alpha y ^ 3)⁻¹ *
    inner ℝ (pairPointDirection (t * eta) alpha (nestedInnerVariables t eta y))
      (polarPoint 1 (nestedChartAngles t eta alpha y 0)) = _
  rw [h]
  exact mul_comm _ _

theorem nestedInnerO_source_formula (t eta alpha : ℝ) (y : NestedChartVariables) :
    nestedInnerO t eta alpha y = (y 3 + nestedChartRadii t eta alpha y 0 *
      singleScaleChi (t * eta) (y 6)) * (nestedInnerW t eta alpha y ^ 3)⁻¹ := by
  have h := pairPointDirection_radial_right (t * eta) alpha (nestedInnerVariables t eta y)
  have ha := (nestedInner_coordinates t eta alpha y 1).2
  have hb := (nestedInner_coordinates t eta alpha y 0).1
  change pairChartAngles (t * eta) alpha (nestedInnerVariables t eta y) 1 =
    nestedChartAngles t eta alpha y 1 at ha
  change pairChartRadii (t * eta) alpha (nestedInnerVariables t eta y) 0 =
    nestedChartRadii t eta alpha y 0 at hb
  rw [ha, hb] at h
  unfold nestedInnerO nestedInnerNewton scaledNewtonField
  rw [real_inner_smul_left, nestedInnerDirection_norm]
  change (nestedInnerW t eta alpha y ^ 3)⁻¹ *
    inner ℝ (pairPointDirection (t * eta) alpha (nestedInnerVariables t eta y))
      (polarPoint 1 (nestedChartAngles t eta alpha y 1)) = _
  rw [h]
  exact mul_comm _ _

theorem nestedInner_radial_difference_source_formula (eps t eta alpha : ℝ)
    (y : NestedChartVariables) :
    pairInternalRadialDifference eps (t * eta) alpha (nestedInnerVariables t eta y) =
      -eps * (alpha * nestedInnerO t eta alpha y + (1 - alpha) * nestedInnerN t eta alpha y) := by
  rw [nestedInnerN_source_formula, nestedInnerO_source_formula]
  have ha := (nestedInner_coordinates t eta alpha y 0).1
  have hb := (nestedInner_coordinates t eta alpha y 1).1
  change pairChartRadii (t * eta) alpha (nestedInnerVariables t eta y) 0 =
    nestedChartRadii t eta alpha y 0 at ha
  change pairChartRadii (t * eta) alpha (nestedInnerVariables t eta y) 1 =
    nestedChartRadii t eta alpha y 1 at hb
  unfold pairInternalRadialDifference
  rw [ha, hb]
  change -eps * (y 3 + (alpha * nestedChartRadii t eta alpha y 0 -
    (1 - alpha) * nestedChartRadii t eta alpha y 1) * singleScaleChi (t * eta) (y 6)) *
      (nestedInnerW t eta alpha y ^ 3)⁻¹ = _
  ring

def nestedScalarTargetH (eps t eta alpha : ℝ) (y : NestedChartVariables) : Satellite → ℝ :=
  fun i => nestedScalarH eps t eta alpha y (nestedChartRadii t eta alpha y i)
    (nestedChartAngles t eta alpha y i)
def nestedScalarTargetK (eps t eta alpha : ℝ) (y : NestedChartVariables) : Satellite → ℝ :=
  fun i => nestedScalarK eps t eta alpha y (nestedChartRadii t eta alpha y i)
    (nestedChartAngles t eta alpha y i)

theorem nestedAngularRows_source_complete (eps t eta alpha : ℝ) (y : NestedChartVariables)
    (ht : 0 < t) (heta : 0 < eta) (heps : 1 + eps ≠ 0)
    (hW : 0 < nestedInnerWSq t eta alpha y) (hV : ∀ i, 0 < nestedOuterWSq t eta alpha y i) :
    let T := angularResidual eps (nestedChartMass t eta alpha) (nestedChartRadii t eta alpha y)
      (nestedChartAngles t eta alpha y)
    let H := nestedScalarTargetH eps t eta alpha y
    let L0 := alpha * nestedOuterL eps t eta alpha y 0 + (1 - alpha) * nestedOuterL eps t eta alpha y 1
    nestedRowAverage eta alpha T = eta ^ 3 * nestedPairAverage alpha H + (1 - eta ^ 3) * H 2 ∧
    nestedRowOuterDifference t alpha T = (H 2 - nestedPairAverage alpha H) / t - L0 ∧
    nestedRowInnerDifference t eta T = (H 1 - H 0) / (t * eta) +
      (1 - eta ^ 3) * (nestedOuterL eps t eta alpha y 1 - nestedOuterL eps t eta alpha y 0) / eta -
      nestedInnerM eps t eta alpha y := by
  let T := angularResidual eps (nestedChartMass t eta alpha) (nestedChartRadii t eta alpha y)
    (nestedChartAngles t eta alpha y)
  let H := nestedScalarTargetH eps t eta alpha y
  let I := nestedInternalAngular eps t eta alpha y
  have hT (i : Fin 3) : T i.castSucc = H i.castSucc + I i.castSucc :=
    nestedAngularExterior_recovery eps t eta alpha y i ht heta hW hV heps
  have hT0 : T 0 = H 0 + I 0 := hT 0
  have hT1 : T 1 = H 1 + I 1 := hT 1
  have hT2 : T 2 = H 2 + I 2 := hT 2
  have hA : nestedRowAverage eta alpha T = nestedRowAverage eta alpha H + nestedRowAverage eta alpha I := by
    unfold nestedRowAverage nestedPairAverage
    rw [hT0, hT1, hT2]
    ring
  have hB : nestedRowOuterDifference t alpha T = (H 2 - nestedPairAverage alpha H) / t +
      (I 2 - nestedPairAverage alpha I) / t := by
    unfold nestedRowOuterDifference nestedPairAverage
    rw [hT0, hT1, hT2]
    ring
  have hC : nestedRowInnerDifference t eta T = (H 1 - H 0) / (t * eta) + (I 1 - I 0) / (t * eta) := by
    unfold nestedRowInnerDifference
    rw [hT0, hT1]
    ring
  have hL : (nestedOuterL eps t eta alpha y 1 - nestedOuterL eps t eta alpha y 0) / eta =
      nestedOuterLDifference eps t eta alpha y := by
    rw [nestedOuterL_difference eps t eta alpha y hV]
    field_simp [heta.ne']
  dsimp only
  refine ⟨?_, ?_, ?_⟩
  · rw [hA, show nestedRowAverage eta alpha I = 0 from nestedInternalAngular_mean eps t eta alpha y]
    simp only [add_zero]
    rfl
  · rw [hB, show I 2 - nestedPairAverage alpha I = t *
      nestedInternalAngularOuterDifference eps t eta alpha y from
        nestedInternalAngular_outer_difference eps t eta alpha y]
    unfold nestedInternalAngularOuterDifference
    field_simp [ht.ne']
    ring
  · rw [hC, show I 1 - I 0 = (t * eta) * nestedInternalAngularInnerDifference eps t eta alpha y from
      nestedInternalAngular_inner_difference eps t eta alpha y hV]
    unfold nestedInternalAngularInnerDifference
    rw [← hL]
    field_simp [ht.ne', heta.ne']
    ring

theorem nestedRadialRows_source_complete (eps t eta alpha : ℝ) (y : NestedChartVariables)
    (ht : 0 < t) (heta : 0 < eta)
    (hW : 0 < nestedInnerWSq t eta alpha y) (hV : ∀ i, 0 < nestedOuterWSq t eta alpha y i) :
    let R := radialResidual eps (nestedChartMass t eta alpha) (nestedChartRadii t eta alpha y)
      (nestedChartAngles t eta alpha y)
    let K := nestedScalarTargetK eps t eta alpha y
    let N0 := alpha * nestedOuterN t eta alpha y 0 + (1 - alpha) * nestedOuterN t eta alpha y 1
    let O0 := alpha * nestedOuterO t eta alpha y 0 + (1 - alpha) * nestedOuterO t eta alpha y 1
    let J := nestedInnerJ eps t eta alpha y
    nestedRowAverage eta alpha R = eta ^ 3 * nestedPairAverage alpha K + (1 - eta ^ 3) * K 2 +
      eps * t * eta ^ 3 * (1 - eta ^ 3) * (N0 - O0) + eta ^ 3 * J ∧
    nestedRowOuterDifference t alpha R = (K 2 - nestedPairAverage alpha K) / t -
      eps * (eta ^ 3 * O0 + (1 - eta ^ 3) * N0) - J / t ∧
    nestedRowInnerDifference t eta R = (K 1 - K 0) / (t * eta) +
      eps * (1 - eta ^ 3) * (nestedOuterN t eta alpha y 1 - nestedOuterN t eta alpha y 0) / eta -
      eps * (alpha * nestedInnerO t eta alpha y + (1 - alpha) * nestedInnerN t eta alpha y) := by
  let R := radialResidual eps (nestedChartMass t eta alpha) (nestedChartRadii t eta alpha y)
    (nestedChartAngles t eta alpha y)
  let K := nestedScalarTargetK eps t eta alpha y
  let I := nestedInternalRadial eps t eta alpha y
  have hR (i : Fin 3) : R i.castSucc = K i.castSucc + I i.castSucc :=
    nestedRadialExterior_recovery eps t eta alpha y i ht heta hW hV
  have hR0 : R 0 = K 0 + I 0 := hR 0
  have hR1 : R 1 = K 1 + I 1 := hR 1
  have hR2 : R 2 = K 2 + I 2 := hR 2
  have hA : nestedRowAverage eta alpha R = nestedRowAverage eta alpha K + nestedRowAverage eta alpha I := by
    unfold nestedRowAverage nestedPairAverage
    rw [hR0, hR1, hR2]
    ring
  have hB : nestedRowOuterDifference t alpha R = (K 2 - nestedPairAverage alpha K) / t +
      (I 2 - nestedPairAverage alpha I) / t := by
    unfold nestedRowOuterDifference nestedPairAverage
    rw [hR0, hR1, hR2]
    ring
  have hC : nestedRowInnerDifference t eta R = (K 1 - K 0) / (t * eta) + (I 1 - I 0) / (t * eta) := by
    unfold nestedRowInnerDifference
    rw [hR0, hR1]
    ring
  have hN : (nestedOuterN t eta alpha y 1 - nestedOuterN t eta alpha y 0) / eta =
      nestedOuterNDifference t eta alpha y := by
    rw [nestedOuterN_difference t eta alpha y hV]
    field_simp [heta.ne']
  have hJ : nestedInnerJ eps t eta alpha y / t = nestedInnerJOverT eps t eta alpha y := by
    rw [nestedInnerJ_factor]
    field_simp [ht.ne']
  dsimp only
  refine ⟨?_, ?_, ?_⟩
  · rw [hA, show nestedRowAverage eta alpha I = nestedInternalRadialMean eps t eta alpha y from
      nestedInternalRadial_mean eps t eta alpha y]
    unfold nestedRowAverage nestedInternalRadialMean
    ring
  · rw [hB, show I 2 - nestedPairAverage alpha I = t *
      nestedInternalRadialOuterDifference eps t eta alpha y from
        nestedInternalRadial_outer_difference eps t eta alpha y]
    unfold nestedInternalRadialOuterDifference
    rw [← hJ]
    field_simp [ht.ne']
    ring
  · rw [hC, show I 1 - I 0 = (t * eta) * nestedInternalRadialInnerDifference eps t eta alpha y from
      nestedInternalRadial_inner_difference eps t eta alpha y hV]
    unfold nestedInternalRadialInnerDifference
    rw [nestedInner_radial_difference_source_formula, ← hN]
    field_simp [ht.ne', heta.ne']
    ring

theorem nestedBoundaryKernels_source_complete (R psi u1 u2 z1 z2 : ℝ)
    (hD1 : 0 < u1 ^ 2 + R ^ 2 * z1 ^ 2) (hD2 : 0 < u2 ^ 2 + R ^ 2 * z2 ^ 2) :
    nestedBoundaryKernel R psi (u1, z1) =
      R ^ 2 * z1 / (u1 ^ 2 + R ^ 2 * z1 ^ 2) ^ ((3 : ℝ) / 2) ∧
    nestedBoundaryKernel R psi (u2, z2) =
      R ^ 2 * z2 / (u2 ^ 2 + R ^ 2 * z2 ^ 2) ^ ((3 : ℝ) / 2) := by
  have hformula (u z : ℝ) (hD : 0 < u ^ 2 + R ^ 2 * z ^ 2) :
      nestedBoundaryKernel R psi (u, z) =
        R ^ 2 * z / (u ^ 2 + R ^ 2 * z ^ 2) ^ ((3 : ℝ) / 2) := by
    rw [nestedBoundaryKernel_formula]
    simp only [div_eq_mul_inv]
    rw [positive_sqrt_cube_inverse_rpow _ hD,
      show -(3 : ℝ) / 2 = -((3 : ℝ) / 2) from by ring, Real.rpow_neg hD.le]
    norm_num
  exact ⟨hformula u1 z1 hD1, hformula u2 z2 hD2⟩

end DominantFiveBody
