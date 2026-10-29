import DominantFiveBody.RelativeMassMetric

/-! # Actual invertible polar differential and physical residual equivalence

The inverse uses orthogonal radial and angular projections at each of the
four satellites. Its denominators are actual positive radii, never masses.
-/

noncomputable section
open scoped BigOperators

namespace DominantFiveBody

/-- The exact real polar distance formula used by the actual collision
estimates and by the independently regularized charts (`eq:distance`). -/
theorem polar_distance_sq (r s a b : ℝ) :
    ‖polarPoint s b-polarPoint r a‖^2 =
      (s-r)^2 + 4*r*s*Real.sin ((b-a)/2)^2 := by
  rw [EuclideanSpace.real_norm_sq_eq,Fin.sum_univ_two]
  simp only [PiLp.sub_apply,polarPoint,point,Matrix.cons_val_zero,
    Matrix.cons_val_one,Matrix.cons_val_fin_one]
  have hc : Real.cos (b-a) = 1-2*Real.sin ((b-a)/2)^2 := by
    have heq : b-a=2*((b-a)/2) := by ring
    conv_lhs => rw [heq,Real.cos_two_mul]
    nlinarith [Real.sin_sq_add_cos_sq ((b-a)/2)]
  rw [Real.cos_sub] at hc
  calc
    _ = s^2*(Real.sin b^2+Real.cos b^2)+r^2*(Real.sin a^2+Real.cos a^2)-
        2*r*s*(Real.cos b*Real.cos a+Real.sin b*Real.sin a) := by ring
    _ = s^2+r^2-2*r*s*(1-2*Real.sin ((b-a)/2)^2) := by
      rw [Real.sin_sq_add_cos_sq a,Real.sin_sq_add_cos_sq b,hc]
      ring
    _ = _ := by ring

theorem polarPoint_smul_one (r theta : ℝ) :
    polarPoint r theta=r • polarPoint 1 theta := by
  ext k
  fin_cases k <;> simp [polarPoint, point]

theorem polarPoint_rotation_smul (r theta : ℝ) :
    quarterTurn (polarPoint r theta)=r • quarterTurn (polarPoint 1 theta) := by
  ext k
  fin_cases k <;> simp [polarPoint, quarterTurn, point]

theorem polarOrthonormal_decomposition (theta : ℝ) (v : Plane) :
    v=inner ℝ v (polarPoint 1 theta) • polarPoint 1 theta+
      inner ℝ v (quarterTurn (polarPoint 1 theta)) • quarterTurn (polarPoint 1 theta) := by
  ext k
  fin_cases k <;>
    simp [plane_inner_coordinates, polarPoint, quarterTurn, point]
  · nlinarith [congrArg (fun a : ℝ => v 0*a) (Real.cos_sq_add_sin_sq theta)]
  · nlinarith [congrArg (fun a : ℝ => v 1*a) (Real.cos_sq_add_sin_sq theta)]

theorem polarPoint_inner_same (r s theta : ℝ) :
    inner ℝ (polarPoint r theta) (polarPoint s theta)=r*s := by
  rw [polarPoint_smul_one s, real_inner_smul_right,
    polarPoint_inner_radial, sub_self, Real.cos_zero, mul_one]
  ring

def polarCoordinateInverse (p : PolarCoordinates) :
    SatelliteConfiguration →L[ℝ] PolarCoordinates :=
  (ContinuousLinearMap.pi fun i =>
    (innerSL ℝ (polarPoint 1 (p.2 i))).comp (ContinuousLinearMap.proj i)).prod
    (ContinuousLinearMap.pi fun i =>
      ((p.1 i^2)⁻¹) • ((innerSL ℝ (quarterTurn (polarPoint (p.1 i) (p.2 i)))).comp
        (ContinuousLinearMap.proj i)))

theorem polarCoordinateInverse_apply (p : PolarCoordinates) (v : SatelliteConfiguration) :
    polarCoordinateInverse p v =
      ((fun i => inner ℝ (v i) (polarPoint 1 (p.2 i))),
        (fun i => (p.1 i^2)⁻¹*inner ℝ (v i) (quarterTurn (polarPoint (p.1 i) (p.2 i))))) := by
  apply Prod.ext
  · funext i
    change inner ℝ (polarPoint 1 (p.2 i)) (v i)=inner ℝ (v i) (polarPoint 1 (p.2 i))
    exact real_inner_comm _ _
  · funext i
    change (p.1 i^2)⁻¹*inner ℝ (quarterTurn (polarPoint (p.1 i) (p.2 i))) (v i)=
      (p.1 i^2)⁻¹*inner ℝ (v i) (quarterTurn (polarPoint (p.1 i) (p.2 i)))
    rw [real_inner_comm]

theorem polarCoordinateInverse_left (p v : PolarCoordinates) (hr : ∀ i, p.1 i≠0) :
    polarCoordinateInverse p (polarCoordinateDerivative p v)=v := by
  rw [polarCoordinateInverse_apply]
  apply Prod.ext <;> funext i
  · change inner ℝ (polarCoordinateDerivative p v i) (polarPoint 1 (p.2 i))=v.1 i
    have hrot : inner ℝ (quarterTurn (polarPoint (p.1 i) (p.2 i))) (polarPoint 1 (p.2 i))=0 := by
      rw [real_inner_comm, polarPoint_inner_rotation, sub_self, Real.sin_zero]
      ring
    rw [polarCoordinateDerivative_apply, inner_add_left, real_inner_smul_left,
      real_inner_smul_left, polarPoint_inner_same, hrot]
    ring
  · change (p.1 i^2)⁻¹*inner ℝ (polarCoordinateDerivative p v i)
        (quarterTurn (polarPoint (p.1 i) (p.2 i)))=v.2 i
    rw [polarCoordinateDerivative_apply, inner_add_left, real_inner_smul_left,
      real_inner_smul_left, polarPoint_inner_rotation, sub_self, Real.sin_zero,
      quarterTurn_inner_quarterTurn, polarPoint_inner_same]
    field_simp [hr i]
    ring

theorem polarCoordinateInverse_right (p : PolarCoordinates) (v : SatelliteConfiguration) :
    (∀ i, p.1 i≠0) → polarCoordinateDerivative p (polarCoordinateInverse p v)=v := by
  intro hr
  apply funext
  intro i
  rw [polarCoordinateDerivative_apply, polarCoordinateInverse_apply]
  change inner ℝ (v i) (polarPoint 1 (p.2 i)) • polarPoint 1 (p.2 i)+
    ((p.1 i^2)⁻¹*inner ℝ (v i) (quarterTurn (polarPoint (p.1 i) (p.2 i)))) •
      quarterTurn (polarPoint (p.1 i) (p.2 i))=v i
  simp_rw [polarPoint_rotation_smul (p.1 i) (p.2 i)]
  rw [real_inner_smul_right, smul_smul]
  have heq : (p.1 i^2)⁻¹*(p.1 i*inner ℝ (v i) (quarterTurn (polarPoint 1 (p.2 i))))*p.1 i =
      inner ℝ (v i) (quarterTurn (polarPoint 1 (p.2 i))) := by field_simp [hr i]
  rw [heq]
  exact (polarOrthonormal_decomposition (p.2 i) (v i)).symm

def polarCoordinateLinearEquiv (p : PolarCoordinates) (hr : ∀ i, p.1 i≠0) :
    PolarCoordinates ≃L[ℝ] SatelliteConfiguration :=
  ContinuousLinearEquiv.equivOfInverse (polarCoordinateDerivative p) (polarCoordinateInverse p)
    (fun v => polarCoordinateInverse_left p v hr)
    (fun v => polarCoordinateInverse_right p v hr)

/-- The actual Fréchet derivative of the polar coordinate map is invertible
whenever all radii are nonzero. -/
theorem polarCoordinateMap_fderiv_isInvertible (p : PolarCoordinates)
    (hr : ∀ i, p.1 i≠0) : (fderiv ℝ polarCoordinateMap p).IsInvertible := by
  rw [(polarCoordinateMap_hasFDerivAt p).fderiv]
  exact ⟨polarCoordinateLinearEquiv p hr, rfl⟩

theorem polarResiduals_zero_iff_vectorRoot (eps : ℝ) (mu : MassRatio)
    (p : PolarCoordinates) (heps : 0<eps) (hm : PositiveRatio mu)
    (hr : ∀ i, 0<p.1 i) :
    ((∀ i, radialResidual eps mu p.1 p.2 i=0) ∧
      (∀ i, angularResidual eps mu p.1 p.2 i=0)) ↔
        (∀ i, vectorResidual eps mu (polarCoordinateMap p) i=0) := by
  constructor
  · rintro ⟨hR,hT⟩
    have hpolar : polarActionDerivative eps mu p=0 := by
      apply ContinuousLinearMap.ext
      intro v
      rw [polarActionDerivative_apply eps mu p v hr]
      simp only [hR, hT, mul_zero, zero_mul, Finset.sum_const_zero, zero_add, zero_apply]
    have hrelative : relativeActionDerivative eps mu (polarCoordinateMap p)=0 := by
      apply ContinuousLinearMap.ext
      intro v
      have h := congrArg (fun L : PolarCoordinates →L[ℝ] ℝ => L (polarCoordinateInverse p v)) hpolar
      rw [polarActionDerivative, ContinuousLinearMap.comp_apply,
        polarCoordinateInverse_right p v (fun i => ne_of_gt (hr i))] at h
      simpa only [zero_apply] using h
    exact (relativeActionVectorGradient_zero_iff eps mu (by linarith) hm _).mp
      ((relativeActionDerivative_zero_iff_gradient eps mu _).mp hrelative)
  · intro hroot
    exact polarResiduals_zero_of_vectorResidual_zero eps mu p.1 p.2 hm heps hr hroot

theorem reducedPolarResiduals_zero_iff_vectorRoot (eps : ℝ) (mu : MassRatio)
    (p : PolarCoordinates) (heps : 0<eps) (hm : PositiveRatio mu)
    (hr : ∀ i, 0<p.1 i) (omitted : Satellite) :
    ((∀ i, radialResidual eps mu p.1 p.2 i=0) ∧
      (∀ i, i≠omitted → angularResidual eps mu p.1 p.2 i=0)) ↔
        (∀ i, vectorResidual eps mu (polarCoordinateMap p) i=0) := by
  rw [← polarResiduals_zero_iff_vectorRoot eps mu p heps hm hr]
  constructor
  · rintro ⟨hR,hT⟩
    refine ⟨hR,fun i => ?_⟩
    by_cases hi : i=omitted
    · subst i
      exact angularResidual_omitted_row eps mu p.1 p.2 omitted (ne_of_gt (hm.1 omitted)) hT
    · exact hT i hi
  · rintro ⟨hR,hT⟩
    exact ⟨hR,fun i _ => hT i⟩

end DominantFiveBody
