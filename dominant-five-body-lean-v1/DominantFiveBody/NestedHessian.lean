import DominantFiveBody.NestedRecovery
import DominantFiveBody.PairHessian

/-! # The actual nested-chart derivative and physical shape Hessian

Both seven-dimensional coordinate and row maps have explicit inverses
whenever t and eta are nonzero, including both alpha endpoints.  The
result refers to the original mass-labelled six-dimensional shape space.
-/

noncomputable section
open scoped BigOperators Matrix ContDiff
open Filter Set Topology

namespace DominantFiveBody
set_option maxHeartbeats 800000

def nestedVariableProjection (i : Fin 7) : NestedChartVariables →L[ℝ] ℝ := ContinuousLinearMap.proj i

/-- The raw fixed-exterior-angle coordinates have order
`(r_p,r_b,r_c,r_a,theta_b,theta_c,theta_a)`. -/
def nestedToFixedSlice (t eta alpha : ℝ) : NestedChartVariables →L[ℝ] SliceCoordinates :=
  ContinuousLinearMap.pi ![
    nestedVariableProjection 0,
    nestedVariableProjection 1 - ((1-eta^3)*t) • nestedVariableProjection 2 +
      (alpha*t*eta) • nestedVariableProjection 3,
    nestedVariableProjection 1 + (eta^3*t) • nestedVariableProjection 2,
    nestedVariableProjection 1 - ((1-eta^3)*t) • nestedVariableProjection 2 -
      ((1-alpha)*t*eta) • nestedVariableProjection 3,
    nestedVariableProjection 4 - ((1-eta^3)*t) • nestedVariableProjection 5 +
      (alpha*t*eta) • nestedVariableProjection 6,
    nestedVariableProjection 4 + (eta^3*t) • nestedVariableProjection 5,
    nestedVariableProjection 4 - ((1-eta^3)*t) • nestedVariableProjection 5 -
      ((1-alpha)*t*eta) • nestedVariableProjection 6]

/-- The inverse is the true weighted center and the two independent
scale-divided differences; no division by any mass fraction occurs. -/
def nestedFromFixedSlice (t eta alpha : ℝ) : SliceCoordinates →L[ℝ] NestedChartVariables :=
  ContinuousLinearMap.pi ![
    nestedVariableProjection 0,
    (eta^3*alpha) • nestedVariableProjection 3 +
      (eta^3*(1-alpha)) • nestedVariableProjection 1 +
      (1-eta^3) • nestedVariableProjection 2,
    t⁻¹ • (nestedVariableProjection 2 - alpha • nestedVariableProjection 3 -
      (1-alpha) • nestedVariableProjection 1),
    (t*eta)⁻¹ • (nestedVariableProjection 1 - nestedVariableProjection 3),
    (eta^3*alpha) • nestedVariableProjection 6 +
      (eta^3*(1-alpha)) • nestedVariableProjection 4 +
      (1-eta^3) • nestedVariableProjection 5,
    t⁻¹ • (nestedVariableProjection 5 - alpha • nestedVariableProjection 6 -
      (1-alpha) • nestedVariableProjection 4),
    (t*eta)⁻¹ • (nestedVariableProjection 4 - nestedVariableProjection 6)]

theorem nestedFromFixedSlice_nestedToFixedSlice (t eta alpha : ℝ)
    (ht : t ≠ 0) (he : eta ≠ 0) (y : NestedChartVariables) :
    nestedFromFixedSlice t eta alpha (nestedToFixedSlice t eta alpha y) = y := by
  ext i
  fin_cases i <;> simp [nestedFromFixedSlice, nestedToFixedSlice, nestedVariableProjection, smul_eq_mul]
  all_goals field_simp
  all_goals ring

theorem nestedToFixedSlice_nestedFromFixedSlice (t eta alpha : ℝ)
    (ht : t ≠ 0) (he : eta ≠ 0) (y : SliceCoordinates) :
    nestedToFixedSlice t eta alpha (nestedFromFixedSlice t eta alpha y) = y := by
  ext i
  fin_cases i <;> simp [nestedFromFixedSlice, nestedToFixedSlice, nestedVariableProjection, smul_eq_mul]
  all_goals field_simp
  all_goals ring

theorem nestedToFixedSlice_isInvertible (t eta alpha : ℝ) (ht : t ≠ 0) (he : eta ≠ 0) :
    (nestedToFixedSlice t eta alpha).IsInvertible := by
  apply euclidean_clm_isInvertible_of_injective
  intro a b h
  have hi := congrArg (nestedFromFixedSlice t eta alpha) h
  simpa only [nestedFromFixedSlice_nestedToFixedSlice t eta alpha ht he] using hi

theorem nestedFromFixedSlice_isInvertible (t eta alpha : ℝ) (ht : t ≠ 0) (he : eta ≠ 0) :
    (nestedFromFixedSlice t eta alpha).IsInvertible := by
  apply euclidean_clm_isInvertible_of_injective
  intro a b h
  have hi := congrArg (nestedToFixedSlice t eta alpha) h
  simpa only [nestedToFixedSlice_nestedFromFixedSlice t eta alpha ht he] using hi

theorem fixedAngleRadii_nestedToFixedSlice (t eta alpha : ℝ) (y : NestedChartVariables) :
    fixedAngleRadii 3 (nestedToFixedSlice t eta alpha y) = nestedChartRadii t eta alpha y := by
  ext i
  fin_cases i
  all_goals first
    | change nestedToFixedSlice t eta alpha y 3 = nestedChartRadii t eta alpha y 0
    | change nestedToFixedSlice t eta alpha y 1 = nestedChartRadii t eta alpha y 1
    | change nestedToFixedSlice t eta alpha y 2 = nestedChartRadii t eta alpha y 2
    | change nestedToFixedSlice t eta alpha y 0 = nestedChartRadii t eta alpha y 3
  all_goals simp [nestedToFixedSlice, nestedVariableProjection, nestedChartRadii,
    nestedCoordinates, smul_eq_mul]

theorem fixedAngleAngles_nestedToFixedSlice (t eta alpha : ℝ) (y : NestedChartVariables) :
    fixedAngleAngles 3 (nestedToFixedSlice t eta alpha y) = nestedChartAngles t eta alpha y := by
  ext i
  fin_cases i
  all_goals first
    | change nestedToFixedSlice t eta alpha y 6 = nestedChartAngles t eta alpha y 0
    | change nestedToFixedSlice t eta alpha y 4 = nestedChartAngles t eta alpha y 1
    | change nestedToFixedSlice t eta alpha y 5 = nestedChartAngles t eta alpha y 2
    | change 0 = nestedChartAngles t eta alpha y 3
  all_goals simp [nestedToFixedSlice, nestedVariableProjection, nestedChartAngles,
    nestedCoordinates, smul_eq_mul]

theorem fixedAngleSatellites_nestedToFixedSlice (t eta alpha : ℝ) (y : NestedChartVariables) :
    fixedAngleSatellites 3 (nestedToFixedSlice t eta alpha y) = nestedChartPoints t eta alpha y := by
  rw [fixedAngleSatellites, fixedAngleRadii_nestedToFixedSlice, fixedAngleAngles_nestedToFixedSlice]
  rfl

theorem fixedAnglePhysicalConfiguration_nestedToFixedSlice (eps t eta alpha : ℝ)
    (y : NestedChartVariables) :
    fixedAnglePhysicalConfiguration (eps, nestedChartMass t eta alpha) 3 (nestedToFixedSlice t eta alpha y) =
      centeredFromRelative eps (nestedChartMass t eta alpha) (nestedChartPoints t eta alpha y) := by
  rw [fixedAnglePhysicalConfiguration, fixedAngleSatellites_nestedToFixedSlice]

theorem nestedChartPhysicalRows_eq_fixed_transform (eps t eta alpha : ℝ) (y : NestedChartVariables) :
    nestedChartPhysicalRows eps t eta alpha y = nestedFromFixedSlice t eta alpha
      (fixedAngleDeletedResidual (eps, nestedChartMass t eta alpha) 3 3 (nestedToFixedSlice t eta alpha y)) := by
  let R := radialResidual eps (nestedChartMass t eta alpha) (nestedChartRadii t eta alpha y)
    (nestedChartAngles t eta alpha y)
  let T := angularResidual eps (nestedChartMass t eta alpha) (nestedChartRadii t eta alpha y)
    (nestedChartAngles t eta alpha y)
  have hraw : fixedAngleDeletedResidual (eps, nestedChartMass t eta alpha) 3 3 (nestedToFixedSlice t eta alpha y) =
      ![R 3,R 1,R 2,R 0,T 1,T 2,T 0] := by
    simp only [fixedAngleDeletedResidual, fixedAngleRadii_nestedToFixedSlice,
      fixedAngleAngles_nestedToFixedSlice]
    ext i
    fin_cases i <;> rfl
  rw [hraw]
  ext i
  fin_cases i
  all_goals simp [nestedChartPhysicalRows, nestedFromFixedSlice, nestedVariableProjection,
    nestedRowAverage, nestedPairAverage, nestedRowOuterDifference, nestedRowInnerDifference,
    smul_eq_mul, div_eq_mul_inv]
  all_goals ring

theorem nestedToFixedSlice_regular (eps t eta alpha : ℝ) (y : NestedChartVariables)
    (heps : 0 < eps) (ht : 0 < t) (he : 0 < eta) (hreg : NestedChartRegular eps t eta alpha y)
    (hr : ∀ i, 0 < nestedChartRadii t eta alpha y i) :
    SliceRegular (eps, nestedChartMass t eta alpha ∘ fixedAnglePermutation 3)
      (nestedToFixedSlice t eta alpha y) := by
  let e := fixedAnglePermutation (3 : Satellite)
  have hq : sliceSatellites (nestedToFixedSlice t eta alpha y) = nestedChartPoints t eta alpha y ∘ e := by
    rw [← fixedAngleSatellites_nestedToFixedSlice]
    ext i k
    change polarPoint (sliceRadii (nestedToFixedSlice t eta alpha y) i)
      (sliceAngles (nestedToFixedSlice t eta alpha y) i) k =
      polarPoint (sliceRadii (nestedToFixedSlice t eta alpha y) (e.symm (e i)))
        (sliceAngles (nestedToFixedSlice t eta alpha y) (e.symm (e i))) k
    rw [Equiv.symm_apply_apply]
  have hcf := nestedChartPoints_relativeCollisionFree eps t eta alpha y ht he hreg
  refine ⟨by linarith, ?_, ?_⟩
  · intro i
    have hri : 0 < fixedAngleRadii 3 (nestedToFixedSlice t eta alpha y) (e i) := by
      rw [fixedAngleRadii_nestedToFixedSlice]
      exact hr (e i)
    change 0 < sliceRadii (nestedToFixedSlice t eta alpha y) (e.symm (e i)) at hri
    simpa only [Equiv.symm_apply_apply] using hri
  · intro i j hij
    rw [hq]
    exact hcf.2 (e i) (e j) (e.injective.ne hij)

theorem nestedChartExtendedRows_eq_fixed_transform (eps t eta alpha : ℝ) (y : NestedChartVariables)
    (ht : 0 < t) (he : 0 < eta) (hreg : NestedChartRegular eps t eta alpha y) :
    nestedChartExtendedRows eps t eta alpha y = nestedFromFixedSlice t eta alpha
      (fixedAngleDeletedResidual (eps, nestedChartMass t eta alpha) 3 3 (nestedToFixedSlice t eta alpha y)) := by
  rw [nestedChartExtendedRows_eq_physical eps t eta alpha y ht he hreg.1 hreg.2.1
    hreg.2.2.1 hreg.2.2.2.1 hreg.2.2.2.2]
  exact nestedChartPhysicalRows_eq_fixed_transform eps t eta alpha y

theorem nestedChartDerivative_eq_fixed_transform (eps t eta alpha : ℝ) (y : NestedChartVariables)
    (heps : 0 < eps) (ht : 0 < t) (he : 0 < eta)
    (hm : PositiveRatio (nestedChartMass t eta alpha)) (hreg : NestedChartRegular eps t eta alpha y)
    (hr : ∀ i, 0 < nestedChartRadii t eta alpha y i) :
    fderiv ℝ (nestedChartExtendedRows eps t eta alpha) y =
      ((nestedFromFixedSlice t eta alpha).comp
        (fderiv ℝ (fixedAngleDeletedResidual (eps, nestedChartMass t eta alpha) 3 3)
          (nestedToFixedSlice t eta alpha y))).comp (nestedToFixedSlice t eta alpha) := by
  have hs := nestedToFixedSlice_regular eps t eta alpha y heps ht he hreg hr
  have hd := fixedAngleDeletedResidual_differentiableAt (eps, nestedChartMass t eta alpha) 3 3
    (nestedToFixedSlice t eta alpha y) hs hm
  let p : NestedChartParameters := ![eps,t,eta,alpha]
  have hjc : ContinuousAt (fun z : NestedChartVariables => (p,z)) y := by fun_prop
  have hregp : NestedChartRegular (p 0) (p 1) (p 2) (p 3) y := hreg
  have hnear : ∀ᶠ z in 𝓝 y, NestedChartRegular eps t eta alpha z :=
    hjc.eventually (nestedChartRegular_isOpen.mem_nhds hregp)
  have heq : nestedChartExtendedRows eps t eta alpha =ᶠ[𝓝 y]
      (fun z => nestedFromFixedSlice t eta alpha
        (fixedAngleDeletedResidual (eps, nestedChartMass t eta alpha) 3 3 (nestedToFixedSlice t eta alpha z))) :=
    hnear.mono (fun z hz => nestedChartExtendedRows_eq_fixed_transform eps t eta alpha z ht he hz)
  have hc := (nestedFromFixedSlice t eta alpha).hasFDerivAt.comp y
    (hd.hasFDerivAt.comp y (nestedToFixedSlice t eta alpha).hasFDerivAt)
  exact (hc.congr_of_eventuallyEq heq).fderiv

/-- The derivative is taken from the genuine nested extension on an
open regular chart. Its invertibility is exactly the original physical
shape-Hessian nondegeneracy, not an auxiliary determinant criterion. -/
theorem nestedChartDerivative_isInvertible_iff_shape (eps t eta alpha : ℝ) (y : NestedChartVariables)
    (heps : 0 < eps) (ht : 0 < t) (he : 0 < eta)
    (hm : PositiveRatio (nestedChartMass t eta alpha)) (hreg : NestedChartRegular eps t eta alpha y)
    (hr : ∀ i, 0 < nestedChartRadii t eta alpha y i)
    (hroot : nestedChartExtendedRows eps t eta alpha y = 0) :
    (fderiv ℝ (nestedChartExtendedRows eps t eta alpha) y).IsInvertible ↔
      ShapeHessianNondegenerate (masses eps (nestedChartMass t eta alpha)) 1
        (centeredFromRelative eps (nestedChartMass t eta alpha) (nestedChartPoints t eta alpha y)) := by
  have hs := nestedToFixedSlice_regular eps t eta alpha y heps ht he hreg hr
  have hLi := nestedFromFixedSlice_isInvertible t eta alpha ht.ne' he.ne'
  have hSi := nestedToFixedSlice_isInvertible t eta alpha ht.ne' he.ne'
  have hfixed : fixedAngleDeletedResidual (eps, nestedChartMass t eta alpha) 3 3
      (nestedToFixedSlice t eta alpha y) = 0 := by
    rw [nestedChartExtendedRows_eq_fixed_transform eps t eta alpha y ht he hreg] at hroot
    exact hLi.injective.eq_iff' (map_zero _) |>.mp hroot
  rw [nestedChartDerivative_eq_fixed_transform eps t eta alpha y heps ht he hm hreg hr]
  obtain ⟨eL,heL⟩ := hLi
  obtain ⟨eS,heS⟩ := hSi
  rw [← heL,← heS,ContinuousLinearMap.isInvertible_comp_equiv,
    ContinuousLinearMap.isInvertible_equiv_comp]
  have hj := fixedAngleDeletedJacobian_isInvertible_iff_shape (eps,nestedChartMass t eta alpha)
    3 3 (nestedToFixedSlice t eta alpha y) hs heps hm hfixed
  rw [heS]
  simpa only [fixedAnglePhysicalConfiguration_nestedToFixedSlice] using hj

end DominantFiveBody
