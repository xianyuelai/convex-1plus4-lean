import DominantFiveBody.TripleJacobian
import DominantFiveBody.TripleRecovery
import DominantFiveBody.PairHessian

/-! # Regular-triple Jacobian and the physical six-dimensional Hessian

The fixed exterior angle is satellite 3. The actual raw radial order
is `(3,1,2,0)`, and the retained angular order is `(1,2,0)`.
Both coordinate and row transformations have explicit inverses at t≠0.
-/

noncomputable section
open scoped BigOperators Matrix ContDiff
open Filter Set Topology

namespace DominantFiveBody
set_option maxHeartbeats 800000

def tripleVariableProjection (i : Fin 7) : TripleChartVariables →L[ℝ] ℝ := ContinuousLinearMap.proj i

def tripleToFixedSlice (t : ℝ) (alpha : TripleVector) : TripleChartVariables →L[ℝ] SliceCoordinates :=
  ContinuousLinearMap.pi ![
    tripleVariableProjection 0,
    tripleVariableProjection 1 + (t * alpha 0) • tripleVariableProjection 2 -
      (t * alpha 2) • tripleVariableProjection 3,
    tripleVariableProjection 1 + (t * alpha 0) • tripleVariableProjection 2 +
      (t * (alpha 0 + alpha 1)) • tripleVariableProjection 3,
    tripleVariableProjection 1 - (t * (alpha 1 + alpha 2)) • tripleVariableProjection 2 -
      (t * alpha 2) • tripleVariableProjection 3,
    tripleVariableProjection 4 + (t * alpha 0) • tripleVariableProjection 5 -
      (t * alpha 2) • tripleVariableProjection 6,
    tripleVariableProjection 4 + (t * alpha 0) • tripleVariableProjection 5 +
      (t * (alpha 0 + alpha 1)) • tripleVariableProjection 6,
    tripleVariableProjection 4 - (t * (alpha 1 + alpha 2)) • tripleVariableProjection 5 -
      (t * alpha 2) • tripleVariableProjection 6]

def tripleFromFixedSlice (t : ℝ) (alpha : TripleVector) : SliceCoordinates →L[ℝ] TripleChartVariables :=
  ContinuousLinearMap.pi ![
    tripleVariableProjection 0,
    alpha 0 • tripleVariableProjection 3 + alpha 1 • tripleVariableProjection 1 +
      alpha 2 • tripleVariableProjection 2,
    t⁻¹ • (tripleVariableProjection 1 - tripleVariableProjection 3),
    t⁻¹ • (tripleVariableProjection 2 - tripleVariableProjection 1),
    alpha 0 • tripleVariableProjection 6 + alpha 1 • tripleVariableProjection 4 +
      alpha 2 • tripleVariableProjection 5,
    t⁻¹ • (tripleVariableProjection 4 - tripleVariableProjection 6),
    t⁻¹ • (tripleVariableProjection 5 - tripleVariableProjection 4)]

theorem tripleFromFixedSlice_tripleToFixedSlice (t : ℝ) (alpha : TripleVector)
    (ht : t ≠ 0) (ha : ∑ i, alpha i = 1) (y : TripleChartVariables) :
    tripleFromFixedSlice t alpha (tripleToFixedSlice t alpha y) = y := by
  rw [Fin.sum_univ_three] at ha
  have ha2 : alpha 2 = 1 - alpha 0 - alpha 1 := by linarith
  ext i
  fin_cases i <;> simp [tripleFromFixedSlice, tripleToFixedSlice, tripleVariableProjection,
    smul_eq_mul, ha2]
  all_goals field_simp [ht]
  all_goals ring

theorem tripleToFixedSlice_tripleFromFixedSlice (t : ℝ) (alpha : TripleVector)
    (ht : t ≠ 0) (ha : ∑ i, alpha i = 1) (y : SliceCoordinates) :
    tripleToFixedSlice t alpha (tripleFromFixedSlice t alpha y) = y := by
  rw [Fin.sum_univ_three] at ha
  have ha2 : alpha 2 = 1 - alpha 0 - alpha 1 := by linarith
  ext i
  fin_cases i <;> simp [tripleFromFixedSlice, tripleToFixedSlice, tripleVariableProjection,
    smul_eq_mul, ha2]
  all_goals field_simp [ht]
  all_goals ring

theorem tripleToFixedSlice_isInvertible (t : ℝ) (alpha : TripleVector)
    (ht : t ≠ 0) (ha : ∑ i, alpha i = 1) : (tripleToFixedSlice t alpha).IsInvertible := by
  apply euclidean_clm_isInvertible_of_injective
  intro a b h
  have he := congrArg (tripleFromFixedSlice t alpha) h
  simpa only [tripleFromFixedSlice_tripleToFixedSlice t alpha ht ha] using he

theorem tripleFromFixedSlice_isInvertible (t : ℝ) (alpha : TripleVector)
    (ht : t ≠ 0) (ha : ∑ i, alpha i = 1) : (tripleFromFixedSlice t alpha).IsInvertible := by
  apply euclidean_clm_isInvertible_of_injective
  intro a b h
  have he := congrArg (tripleToFixedSlice t alpha) h
  simpa only [tripleToFixedSlice_tripleFromFixedSlice t alpha ht ha] using he

theorem fixedAngleRadii_tripleToFixedSlice (t : ℝ) (alpha : TripleVector) (y : TripleChartVariables) :
    fixedAngleRadii 3 (tripleToFixedSlice t alpha y) = tripleChartRadii t alpha y := by
  ext i
  fin_cases i
  all_goals first
    | change tripleToFixedSlice t alpha y 3 = tripleChartRadii t alpha y 0
    | change tripleToFixedSlice t alpha y 1 = tripleChartRadii t alpha y 1
    | change tripleToFixedSlice t alpha y 2 = tripleChartRadii t alpha y 2
    | change tripleToFixedSlice t alpha y 0 = tripleChartRadii t alpha y 3
  all_goals simp [tripleToFixedSlice,
    tripleVariableProjection, tripleChartRadii, tripleChartRadialPositions, tripleCenteringMatrix,
    tripleChartRadialGaps, Matrix.mulVec, dotProduct, Fin.sum_univ_two, smul_eq_mul]
  all_goals ring

theorem fixedAngleAngles_tripleToFixedSlice (t : ℝ) (alpha : TripleVector) (y : TripleChartVariables) :
    fixedAngleAngles 3 (tripleToFixedSlice t alpha y) = tripleChartAngles t alpha y := by
  ext i
  fin_cases i
  all_goals first
    | change tripleToFixedSlice t alpha y 6 = tripleChartAngles t alpha y 0
    | change tripleToFixedSlice t alpha y 4 = tripleChartAngles t alpha y 1
    | change tripleToFixedSlice t alpha y 5 = tripleChartAngles t alpha y 2
    | change 0 = tripleChartAngles t alpha y 3
  all_goals simp [tripleToFixedSlice,
    tripleVariableProjection, tripleChartAngles, tripleChartAngularPositions, tripleCenteringMatrix,
    tripleChartAngularGaps, Matrix.mulVec, dotProduct, Fin.sum_univ_two, smul_eq_mul]
  all_goals ring

theorem fixedAngleSatellites_tripleToFixedSlice (t : ℝ) (alpha : TripleVector) (y : TripleChartVariables) :
    fixedAngleSatellites 3 (tripleToFixedSlice t alpha y) = tripleChartPoints t alpha y := by
  rw [fixedAngleSatellites, fixedAngleRadii_tripleToFixedSlice, fixedAngleAngles_tripleToFixedSlice]
  rfl

theorem fixedAnglePhysicalConfiguration_tripleToFixedSlice (eps t : ℝ) (alpha : TripleVector)
    (y : TripleChartVariables) :
    fixedAnglePhysicalConfiguration (eps, tripleChartMass t alpha) 3 (tripleToFixedSlice t alpha y) =
      centeredFromRelative eps (tripleChartMass t alpha) (tripleChartPoints t alpha y) := by
  rw [fixedAnglePhysicalConfiguration, fixedAngleSatellites_tripleToFixedSlice]

theorem tripleChartPhysicalRows_eq_fixed_transform (eps t : ℝ) (alpha : TripleVector)
    (y : TripleChartVariables) : tripleChartPhysicalRows eps t alpha y =
      tripleFromFixedSlice t alpha
        (fixedAngleDeletedResidual (eps, tripleChartMass t alpha) 3 3 (tripleToFixedSlice t alpha y)) := by
  let R := radialResidual eps (tripleChartMass t alpha) (tripleChartRadii t alpha y) (tripleChartAngles t alpha y)
  let T := angularResidual eps (tripleChartMass t alpha) (tripleChartRadii t alpha y) (tripleChartAngles t alpha y)
  have hraw : fixedAngleDeletedResidual (eps, tripleChartMass t alpha) 3 3 (tripleToFixedSlice t alpha y) =
      ![R 3, R 1, R 2, R 0, T 1, T 2, T 0] := by
    simp only [fixedAngleDeletedResidual, fixedAngleRadii_tripleToFixedSlice, fixedAngleAngles_tripleToFixedSlice]
    ext i
    fin_cases i <;> rfl
  rw [hraw]
  ext i
  fin_cases i
  all_goals simp [tripleChartPhysicalRows, tripleFromFixedSlice, tripleVariableProjection,
    tripleRowAverage, tripleRowDifferences, tripleClusterRows, tripleGapMatrix,
    Matrix.mulVec, dotProduct, Fin.sum_univ_three, smul_eq_mul, div_eq_mul_inv]
  all_goals ring

theorem tripleToFixedSlice_regular (eps t : ℝ) (alpha : TripleVector) (y : TripleChartVariables)
    (heps : 0 < eps) (ht : 0 < t) (hreg : TripleChartRegular eps t alpha y)
    (hr : ∀ i, 0 < tripleChartRadii t alpha y i) :
    SliceRegular (eps, tripleChartMass t alpha ∘ fixedAnglePermutation 3) (tripleToFixedSlice t alpha y) := by
  let e := fixedAnglePermutation (3 : Satellite)
  have hq : sliceSatellites (tripleToFixedSlice t alpha y) = tripleChartPoints t alpha y ∘ e := by
    rw [← fixedAngleSatellites_tripleToFixedSlice]
    ext i k
    change polarPoint (sliceRadii (tripleToFixedSlice t alpha y) i)
      (sliceAngles (tripleToFixedSlice t alpha y) i) k =
      polarPoint (sliceRadii (tripleToFixedSlice t alpha y) (e.symm (e i)))
        (sliceAngles (tripleToFixedSlice t alpha y) (e.symm (e i))) k
    rw [Equiv.symm_apply_apply]
  have hcf := tripleChartPoints_relativeCollisionFree eps t alpha y ht hreg
  refine ⟨by linarith, ?_, ?_⟩
  · intro i
    have hri : 0 < fixedAngleRadii 3 (tripleToFixedSlice t alpha y) (e i) := by
      rw [fixedAngleRadii_tripleToFixedSlice]
      exact hr (e i)
    change 0 < sliceRadii (tripleToFixedSlice t alpha y) (e.symm (e i)) at hri
    simpa only [Equiv.symm_apply_apply] using hri
  · intro i j hij
    rw [hq]
    exact hcf.2 (e i) (e j) (e.injective.ne hij)

theorem tripleChartExtendedRows_eq_fixed_transform (eps t : ℝ) (alpha : TripleVector)
    (y : TripleChartVariables) (ht : 0 < t) (hreg : TripleChartRegular eps t alpha y) :
    tripleChartExtendedRows eps t alpha y = tripleFromFixedSlice t alpha
      (fixedAngleDeletedResidual (eps, tripleChartMass t alpha) 3 3 (tripleToFixedSlice t alpha y)) := by
  rw [tripleChartExtendedRows_eq_physical eps t alpha y ht hreg.1 hreg.2.2.1
    (fun i => hreg.2.1 i.castSucc) hreg.2.2.2]
  exact tripleChartPhysicalRows_eq_fixed_transform eps t alpha y

theorem tripleChartJacobian_eq_fixed_transform (eps t : ℝ) (alpha : TripleVector)
    (y : TripleChartVariables) (heps : 0 < eps) (ht : 0 < t)
    (hm : PositiveRatio (tripleChartMass t alpha)) (hreg : TripleChartRegular eps t alpha y)
    (hr : ∀ i, 0 < tripleChartRadii t alpha y i) :
    tripleChartJacobian eps t alpha y =
      ((tripleFromFixedSlice t alpha).comp
        (fderiv ℝ (fixedAngleDeletedResidual (eps, tripleChartMass t alpha) 3 3)
          (tripleToFixedSlice t alpha y))).comp (tripleToFixedSlice t alpha) := by
  have hs := tripleToFixedSlice_regular eps t alpha y heps ht hreg hr
  have hd := fixedAngleDeletedResidual_differentiableAt (eps, tripleChartMass t alpha) 3 3
    (tripleToFixedSlice t alpha y) hs hm
  let p : Fin 5 → ℝ := ![eps, t, alpha 0, alpha 1, alpha 2]
  have hp : tripleJointAlpha p = alpha := by ext i; fin_cases i <;> rfl
  have hjc : ContinuousAt (fun z : TripleChartVariables => (p, z)) y := by fun_prop
  have hregp : TripleChartRegular (p 0) (p 1) (tripleJointAlpha p) y := by
    simpa only [hp, show p 0 = eps from rfl, show p 1 = t from rfl] using hreg
  have hnear : ∀ᶠ z in 𝓝 y, TripleChartRegular eps t alpha z := by
    have he := hjc.eventually (tripleChartRegular_isOpen.mem_nhds hregp)
    simpa only [hp, show p 0 = eps from rfl, show p 1 = t from rfl] using he
  have heq : tripleChartExtendedRows eps t alpha =ᶠ[𝓝 y]
      (fun z => tripleFromFixedSlice t alpha
        (fixedAngleDeletedResidual (eps, tripleChartMass t alpha) 3 3 (tripleToFixedSlice t alpha z))) :=
    hnear.mono (fun z hz => tripleChartExtendedRows_eq_fixed_transform eps t alpha z ht hz)
  have hc := (tripleFromFixedSlice t alpha).hasFDerivAt.comp y
    (hd.hasFDerivAt.comp y (tripleToFixedSlice t alpha).hasFDerivAt)
  exact (hc.congr_of_eventuallyEq heq).fderiv

/-- Source Lemma 3.1 for this actual triple chart: invertibility of its
true derivative is equivalent to nondegeneracy of the original physical
six-dimensional shape Hessian, in the original labels. -/
theorem tripleChartJacobian_isInvertible_iff_shape (eps t : ℝ) (alpha : TripleVector)
    (y : TripleChartVariables) (heps : 0 < eps) (ht : 0 < t) (ha : ∑ i, alpha i = 1)
    (hm : PositiveRatio (tripleChartMass t alpha)) (hreg : TripleChartRegular eps t alpha y)
    (hr : ∀ i, 0 < tripleChartRadii t alpha y i) (hroot : tripleChartExtendedRows eps t alpha y = 0) :
    (tripleChartJacobian eps t alpha y).IsInvertible ↔
      ShapeHessianNondegenerate (masses eps (tripleChartMass t alpha)) 1
        (centeredFromRelative eps (tripleChartMass t alpha) (tripleChartPoints t alpha y)) := by
  have hs := tripleToFixedSlice_regular eps t alpha y heps ht hreg hr
  have hLi := tripleFromFixedSlice_isInvertible t alpha ht.ne' ha
  have hSi := tripleToFixedSlice_isInvertible t alpha ht.ne' ha
  have hfixed : fixedAngleDeletedResidual (eps, tripleChartMass t alpha) 3 3 (tripleToFixedSlice t alpha y) = 0 := by
    rw [tripleChartExtendedRows_eq_fixed_transform eps t alpha y ht hreg] at hroot
    exact hLi.injective.eq_iff' (map_zero _) |>.mp hroot
  rw [tripleChartJacobian_eq_fixed_transform eps t alpha y heps ht hm hreg hr]
  obtain ⟨eL, heL⟩ := hLi
  obtain ⟨eS, heS⟩ := hSi
  rw [← heL, ← heS, ContinuousLinearMap.isInvertible_comp_equiv,
    ContinuousLinearMap.isInvertible_equiv_comp]
  have he := fixedAngleDeletedJacobian_isInvertible_iff_shape (eps, tripleChartMass t alpha)
    3 3 (tripleToFixedSlice t alpha y) hs heps hm hfixed
  rw [heS]
  simpa only [fixedAnglePhysicalConfiguration_tripleToFixedSlice] using he

end DominantFiveBody
