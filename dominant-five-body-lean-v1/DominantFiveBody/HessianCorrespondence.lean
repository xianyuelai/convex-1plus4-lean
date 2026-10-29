import DominantFiveBody.PotentialDerivatives
import DominantFiveBody.RelativeAction

/-!
# Radial and rotational identities for the actual Hessian

Source: §3 `lem:hessian`. The identities below use the actual Fréchet
derivative of the Newtonian augmented potential. No residual Jacobian is
substituted for a Hessian, and central equations are actual hypotheses.
-/

noncomputable section
open scoped BigOperators
open Filter Set Topology

namespace DominantFiveBody

@[simp] theorem quarterTurn_sub (v w : Plane) :
    quarterTurn (v - w) = quarterTurn v - quarterTurn w :=
  quarterTurnLinear.map_sub v w

theorem quarterTurn_inner_left (v w : Plane) :
    inner ℝ (quarterTurn v) w = -inner ℝ v (quarterTurn w) := by
  simp [plane_inner_coordinates, quarterTurn, point]

theorem massInner_rotation_left (m : MassVector) (v w : Configuration) :
    massInner m (rotationDirection v) w = -massInner m v (rotationDirection w) := by
  simp [massInner, rotationDirection, quarterTurn_inner_left, Finset.sum_neg_distrib]

theorem potentialHessianMap_radial (m : MassVector) (x : Configuration)
    (hx : CollisionFree x) (w : Configuration) :
    potentialHessianMap m x x w = -2 * potentialDerivative m x w := by
  simp only [potentialHessianMap, potentialDerivative, sum_apply, add_apply, smul_apply,
    ContinuousLinearMap.smulRight_apply, pairMetric_apply, real_inner_self_eq_norm_sq,
    smul_eq_mul]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro p hp
  have hij : p.1 ≠ p.2 := ne_of_lt ((Finset.mem_filter.mp hp).2)
  have hn : ‖x p.1 - x p.2‖ ≠ 0 := norm_ne_zero_iff.mpr (sub_ne_zero.mpr (hx _ _ hij))
  unfold pairDistance
  field_simp [hn]
  ring

/-- Homogeneity identity at every collision-free position, before imposing
the root equations. The critical-gradient term is retained explicitly. -/
theorem physicalHessian_radial_general (m : MassVector) (lam : ℝ)
    (x : Configuration) (hx : CollisionFree x) (w : Configuration) :
    physicalHessian m lam x x w =
      -2 * (fderiv ℝ (augmentedPotential m lam) x) w + 3 * lam * massInner m x w := by
  rw [physicalHessian_eq_map m lam x hx, fderiv_augmentedPotential m lam x hx]
  simp only [augmentedPotentialHessianMap, augmentedPotentialDerivative,
    add_apply, smul_apply, massMetric_apply, smul_eq_mul, potentialHessianMap_radial m x hx]
  ring

/-- §3 `lem:hessian`: the paper's `D²G(x)x = 3Mx` at a genuine
multiplier-one root, stated as equality against every test variation. -/
theorem physicalHessian_radial_of_normalizedCC (m : MassVector)
    (x : Configuration) (hx : NormalizedCentralConfiguration m x) (w : Configuration) :
    physicalHessian m 1 x x w = 3 * massInner m x w := by
  rw [physicalHessian_radial_general m 1 x hx.1,
    normalizedCC_fderiv_augmentedPotential_zero m x hx]
  simp

theorem potentialHessianMap_rotation (m : MassVector) (x w : Configuration) :
    potentialHessianMap m x (rotationDirection x) w =
      -potentialDerivative m x (rotationDirection w) := by
  simp only [potentialHessianMap, potentialDerivative, sum_apply, add_apply, smul_apply,
    ContinuousLinearMap.smulRight_apply, pairMetric_apply, rotationDirection,
    ← quarterTurn_sub, quarterTurn_inner_self, quarterTurn_inner_left, smul_eq_mul,
    mul_zero, zero_mul, add_zero]
  rw [← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro p hp
  ring

/-- Rotation covariance of the full actual Hessian, retaining the
critical-gradient term away from a root. -/
theorem physicalHessian_rotation_general (m : MassVector) (lam : ℝ)
    (x : Configuration) (hx : CollisionFree x) (w : Configuration) :
    physicalHessian m lam x (rotationDirection x) w =
      -(fderiv ℝ (augmentedPotential m lam) x) (rotationDirection w) := by
  rw [physicalHessian_eq_map m lam x hx, fderiv_augmentedPotential m lam x hx]
  simp only [augmentedPotentialHessianMap, augmentedPotentialDerivative,
    add_apply, smul_apply, massMetric_apply, smul_eq_mul,
    potentialHessianMap_rotation, massInner_rotation_left]
  ring

/-- §3 `lem:hessian`: the rotation direction belongs to the actual
Hessian kernel at a multiplier-one central configuration. -/
theorem physicalHessian_rotation_of_normalizedCC (m : MassVector)
    (x : Configuration) (hx : NormalizedCentralConfiguration m x) (w : Configuration) :
    physicalHessian m 1 x (rotationDirection x) w = 0 := by
  rw [physicalHessian_rotation_general m 1 x hx.1,
    normalizedCC_fderiv_augmentedPotential_zero m x hx]
  simp

theorem centered_eq_of_weightedPosition_zero (m : MassVector) (x : Configuration)
    (hx : weightedPosition m x = 0) : centered m x = x := by
  funext i
  simp [centered, massCenter, hx]

theorem massInner_sub_right (m : MassVector) (v w z : Configuration) :
    massInner m v (w - z) = massInner m v w - massInner m v z := by
  simpa only [massInnerRight_apply] using (massInnerRight m v).map_sub w z

theorem massInner_smul_right (m : MassVector) (v w : Configuration) (a : ℝ) :
    massInner m v (a • w) = a * massInner m v w := by
  simpa only [massInnerRight_apply, smul_eq_mul] using (massInnerRight m v).map_smul a w

theorem physicalHessian_sub_right (m : MassVector) (lam : ℝ) (x : Configuration)
    (hx : CollisionFree x) (v w z : Configuration) :
    physicalHessian m lam x v (w - z) =
      physicalHessian m lam x v w - physicalHessian m lam x v z := by
  simp only [physicalHessian_eq_map m lam x hx, map_sub]

theorem physicalHessian_smul_right (m : MassVector) (lam : ℝ) (x : Configuration)
    (hx : CollisionFree x) (v w : Configuration) (a : ℝ) :
    physicalHessian m lam x v (a • w) = a * physicalHessian m lam x v w := by
  simp only [physicalHessian_eq_map m lam x hx, map_smul, smul_eq_mul]

/-- The mass-orthogonal rotation slice in the centered variations.
It is an actual seven-dimensional geometric subspace. Equivalence with
the paper's fixed-angle coordinate slice is a separate conversion step. -/
def rotationSliceSpace (m : MassVector) (x : Configuration) : Submodule ℝ Configuration :=
  (weightedPositionLinear m).ker ⊓
    (massInnerRight m (rotationDirection (centered m x))).ker

theorem mem_rotationSliceSpace_iff (m : MassVector) (x v : Configuration) :
    v ∈ rotationSliceSpace m x ↔ weightedPosition m v = 0 ∧
      massInner m (rotationDirection (centered m x)) v = 0 := by
  simp [rotationSliceSpace, weightedPositionLinear_apply, massInnerRight_apply]

theorem shapeSpace_le_rotationSliceSpace (m : MassVector) (x : Configuration) :
    shapeSpace m x ≤ rotationSliceSpace m x := by
  intro v hv
  rcases (mem_shapeSpace_iff m x v).mp hv with ⟨hc, _, hr⟩
  exact (mem_rotationSliceSpace_iff m x v).mpr ⟨hc, hr⟩

def rotationSliceConstraints (m : MassVector) (x : Configuration) :
    Configuration →ₗ[ℝ] Plane × ℝ :=
  (weightedPositionLinear m).prod (massInnerRight m (rotationDirection (centered m x)))

theorem rotationSliceConstraints_apply (m : MassVector) (x w : Configuration) :
    rotationSliceConstraints m x w =
      (weightedPosition m w, massInner m (rotationDirection (centered m x)) w) := by
  simp [rotationSliceConstraints, weightedPositionLinear_apply, massInnerRight_apply]

theorem rotationSliceConstraints_surjective (m : MassVector) (hm : PositiveMasses m)
    (x : Configuration) (hx : CollisionFree x) :
    Function.Surjective (rotationSliceConstraints m x) := by
  rintro ⟨b, s⟩
  obtain ⟨w, hw⟩ := shapeConstraints_surjective m hm x hx (b, (0, s))
  refine ⟨w, ?_⟩
  have h := congrArg (fun z : Plane × (ℝ × ℝ) => (z.1, z.2.2)) hw
  simpa only [shapeConstraints_apply, rotationSliceConstraints_apply] using h

theorem ker_rotationSliceConstraints (m : MassVector) (x : Configuration) :
    (rotationSliceConstraints m x).ker = rotationSliceSpace m x := by
  simp only [rotationSliceConstraints, LinearMap.ker_prod, rotationSliceSpace]

/-- The seven-dimensional rotation slice has not removed the radial
direction; the six-dimensional shape space removes that last direction. -/
theorem finrank_rotationSliceSpace (m : MassVector) (hm : PositiveMasses m)
    (x : Configuration) (hx : CollisionFree x) :
    Module.finrank ℝ (rotationSliceSpace m x) = 7 := by
  have hr : Module.finrank ℝ (LinearMap.range (rotationSliceConstraints m x)) = 3 := by
    rw [LinearMap.range_eq_top.mpr (rotationSliceConstraints_surjective m hm x hx), finrank_top]
    simp [Module.finrank_prod]
  have h := (rotationSliceConstraints m x).finrank_range_add_finrank_ker
  rw [hr, ker_rotationSliceConstraints, finrank_configuration] at h
  omega

/-- The true bilinear kernel condition on the seven-dimensional rotation
slice. It is compared below with the existing six-dimensional predicate. -/
def RotationSliceHessianNondegenerate (m : MassVector) (lam : ℝ)
    (x : Configuration) : Prop :=
  ∀ v ∈ rotationSliceSpace m x,
    (∀ w ∈ rotationSliceSpace m x, physicalHessian m lam x v w = 0) → v = 0

def radialRemoval (m : MassVector) (x w : Configuration) : Configuration :=
  w - (massInner m x w / massInner m x x) • x

theorem radial_mem_rotationSliceSpace (m : MassVector) (x : Configuration)
    (hx : NormalizedCentralConfiguration m x) : x ∈ rotationSliceSpace m x := by
  rw [mem_rotationSliceSpace_iff, centered_eq_of_weightedPosition_zero m x hx.2.1]
  exact ⟨hx.2.1, by rw [massInner_comm, massInner_rotation_self]⟩

/-- Actual radial removal: any seven-slice variation decomposes into its
radial component and a variation in the original six-dimensional space. -/
theorem radialRemoval_mem_shapeSpace (m : MassVector) (hm : PositiveMasses m)
    (x : Configuration) (hx : NormalizedCentralConfiguration m x)
    (w : Configuration) (hw : w ∈ rotationSliceSpace m x) :
    radialRemoval m x w ∈ shapeSpace m x := by
  have hcenter := centered_eq_of_weightedPosition_zero m x hx.2.1
  obtain ⟨hwc, hwr⟩ := (mem_rotationSliceSpace_iff m x w).mp hw
  rw [hcenter] at hwr
  have hI : massInner m x x ≠ 0 := ne_of_gt
    (massInner_self_pos m hm x (collisionFree_ne_zero x hx.1))
  rw [mem_shapeSpace_iff, hcenter]
  refine ⟨?_, ?_, ?_⟩
  · change weightedPositionLinear m (w - (massInner m x w / massInner m x x) • x) = 0
    rw [map_sub, map_smul, weightedPositionLinear_apply, weightedPositionLinear_apply,
      hwc, hx.2.1, smul_zero, sub_self]
  · rw [radialRemoval, massInner_sub_right, massInner_smul_right, div_mul_cancel₀ _ hI, sub_self]
  · rw [radialRemoval, massInner_sub_right, massInner_smul_right, hwr,
      massInner_comm m (rotationDirection x) x, massInner_rotation_self]
    simp

/-- §3 `lem:hessian`: the nonzero radial block is actually removed. This
establishes the seven-dimensional geometric slice Hessian iff the original
six-dimensional constrained shape Hessian at a genuine normalized root.
The remaining step to the *residual Jacobian* requires the polar-gradient
coordinate identities and is not asserted by this theorem. -/
theorem rotationSliceHessian_nondegenerate_iff_shape (m : MassVector) (hm : PositiveMasses m)
    (x : Configuration) (hx : NormalizedCentralConfiguration m x) :
    RotationSliceHessianNondegenerate m 1 x ↔ ShapeHessianNondegenerate m 1 x := by
  have hcenter := centered_eq_of_weightedPosition_zero m x hx.2.1
  constructor
  · intro hs v hv hk
    have hvin : massInner m x v = 0 := by
      have h := ((mem_shapeSpace_iff m x v).mp hv).2.1
      rwa [hcenter] at h
    have hvx : physicalHessian m 1 x v x = 0 := by
      rw [physicalHessian_comm m 1 x hx.1, physicalHessian_radial_of_normalizedCC m x hx, hvin,
        mul_zero]
    apply hs v (shapeSpace_le_rotationSliceSpace m x hv)
    intro w hw
    have h := hk (radialRemoval m x w) (radialRemoval_mem_shapeSpace m hm x hx w hw)
    change physicalHessian m 1 x v (w - (massInner m x w / massInner m x x) • x) = 0 at h
    rwa [physicalHessian_sub_right m 1 x hx.1, physicalHessian_smul_right m 1 x hx.1,
      hvx, mul_zero, sub_zero] at h
  · intro hs v hv hk
    obtain ⟨hvc, hvr⟩ := (mem_rotationSliceSpace_iff m x v).mp hv
    have hvx := hk x (radial_mem_rotationSliceSpace m x hx)
    rw [physicalHessian_comm m 1 x hx.1, physicalHessian_radial_of_normalizedCC m x hx] at hvx
    have hvin : massInner m x v = 0 := (mul_eq_zero.mp hvx).resolve_left (by norm_num)
    have hvshape : v ∈ shapeSpace m x := by
      rw [mem_shapeSpace_iff, hcenter] at *
      exact ⟨hvc, hvin, hvr⟩
    exact hs v hvshape (fun w hw => hk w (shapeSpace_le_rotationSliceSpace m x hw))

/-- The actual bilinear Hessian restricted in both variables to the
seven-dimensional geometric rotation slice, regarded as an operator to
the continuous dual of that same slice. -/
def rotationSliceHessianOperator (m : MassVector) (lam : ℝ) (x : Configuration) :
    rotationSliceSpace m x →L[ℝ] (rotationSliceSpace m x →L[ℝ] ℝ) :=
  ((ContinuousLinearMap.compL ℝ (rotationSliceSpace m x) Configuration ℝ).flip
      (rotationSliceSpace m x).subtypeL).comp
    ((augmentedPotentialHessianMap m lam x).comp (rotationSliceSpace m x).subtypeL)

@[simp] theorem rotationSliceHessianOperator_apply (m : MassVector) (lam : ℝ)
    (x : Configuration) (v w : rotationSliceSpace m x) :
    rotationSliceHessianOperator m lam x v w = augmentedPotentialHessianMap m lam x v w := rfl

theorem rotationSliceHessianOperator_injective_iff (m : MassVector) (lam : ℝ)
    (x : Configuration) (hx : CollisionFree x) :
    Function.Injective (rotationSliceHessianOperator m lam x) ↔
      RotationSliceHessianNondegenerate m lam x := by
  let A := rotationSliceHessianOperator m lam x
  have hker : Function.Injective A ↔ ∀ v, A v = 0 → v = 0 := by
    convert! (LinearMap.ker_eq_bot (f := A.toLinearMap)).symm.trans
      (LinearMap.ker_eq_bot' (f := A.toLinearMap)) using 1
  rw [hker]
  constructor
  · intro hi v hv hk
    have hvzero : A ⟨v, hv⟩ = 0 := by
      ext w
      change augmentedPotentialHessianMap m lam x v w = 0
      rw [← physicalHessian_eq_map m lam x hx]
      exact hk w w.property
    have h := hi ⟨v, hv⟩ hvzero
    exact congrArg Subtype.val h
  · intro hn v hv
    apply Subtype.ext
    change (v : Configuration) = 0
    apply hn v v.property
    intro w hw
    have h := congrArg (fun f : rotationSliceSpace m x →L[ℝ] ℝ => f ⟨w, hw⟩) hv
    simpa only [A, rotationSliceHessianOperator_apply, zero_apply,
      physicalHessian_eq_map m lam x hx] using h

/-- Finite-dimensional duality upgrades the actual kernel condition to a
continuous linear equivalence. This contains no assumption of an inverse
or a residual/Hessian identification. -/
theorem rotationSliceHessianOperator_isInvertible_iff (m : MassVector) (lam : ℝ)
    (x : Configuration) (hx : CollisionFree x) :
    (rotationSliceHessianOperator m lam x).IsInvertible ↔
      RotationSliceHessianNondegenerate m lam x := by
  constructor
  · intro h
    exact (rotationSliceHessianOperator_injective_iff m lam x hx).mp h.injective
  · intro h
    let S := rotationSliceSpace m x
    let A := rotationSliceHessianOperator m lam x
    let _ : FiniteDimensional ℝ (S →L[ℝ] ℝ) :=
      (LinearMap.toContinuousLinearMap : (S →ₗ[ℝ] ℝ) ≃ₗ[ℝ] (S →L[ℝ] ℝ)).finiteDimensional
    have hdim : Module.finrank ℝ S = Module.finrank ℝ (S →L[ℝ] ℝ) := by
      rw [← (LinearMap.toContinuousLinearMap : (S →ₗ[ℝ] ℝ) ≃ₗ[ℝ] (S →L[ℝ] ℝ)).finrank_eq]
      exact Subspace.dual_finrank_eq.symm
    have hi : Function.Injective A :=
      (rotationSliceHessianOperator_injective_iff m lam x hx).mpr h
    have hi' : Function.Injective A.toLinearMap := hi
    have hsur : Function.Surjective A.toLinearMap := by
      apply (LinearMap.injective_iff_surjective_of_finrank_eq_finrank ?_).mp hi'
      convert! hdim
    let e : S ≃ₗ[ℝ] (S →L[ℝ] ℝ) := LinearEquiv.ofBijective A.toLinearMap ⟨hi', hsur⟩
    let e' : S ≃L[ℝ] (S →L[ℝ] ℝ) :=
      { e with
        continuous_toFun := A.continuous
        continuous_invFun := by
          exact LinearMap.continuous_of_finiteDimensional
            (𝕜 := ℝ) (E := S →L[ℝ] ℝ) (F' := S) e.symm.toLinearMap }
    refine ⟨e', ?_⟩
    ext v w
    rfl

/-- The operator on the actual seven-dimensional rotation slice is
invertible exactly when the paper's original six-dimensional physical
shape Hessian is nondegenerate at a normalized central configuration. -/
theorem rotationSliceHessianOperator_isInvertible_iff_shape (m : MassVector)
    (hm : PositiveMasses m) (x : Configuration) (hx : NormalizedCentralConfiguration m x) :
    (rotationSliceHessianOperator m 1 x).IsInvertible ↔ ShapeHessianNondegenerate m 1 x :=
  (rotationSliceHessianOperator_isInvertible_iff m 1 x hx.1).trans
    (rotationSliceHessian_nondegenerate_iff_shape m hm x hx)

/-- A finite-dimensional continuous linear map between equal-dimensional
real spaces is invertible as soon as its actual function is injective. -/
theorem clm_isInvertible_of_injective_of_finrank_eq
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    [FiniteDimensional ℝ E] [FiniteDimensional ℝ F]
    (A : E →L[ℝ] F) (hi : Function.Injective A)
    (hdim : Module.finrank ℝ E = Module.finrank ℝ F) : A.IsInvertible := by
  have hs : Function.Surjective A.toLinearMap :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank (f := A.toLinearMap) hdim).mp hi
  let e : E ≃ₗ[ℝ] F := LinearEquiv.ofBijective A.toLinearMap ⟨hi, hs⟩
  let e' : E ≃L[ℝ] F :=
    { e with
      continuous_toFun := A.continuous
      continuous_invFun := LinearMap.continuous_of_finiteDimensional
        (𝕜 := ℝ) (E := F) (F' := E) e.symm.toLinearMap }
  exact ⟨e', rfl⟩

/-- The actual centered variation space before removing rotation or scale. -/
def centeredVariationSpace (m : MassVector) : Submodule ℝ Configuration :=
  (weightedPositionLinear m).ker

def liftRelativeContinuous : SatelliteConfiguration →L[ℝ] Configuration :=
  ContinuousLinearMap.pi (fun i => Fin.cases 0
    (fun j : Satellite => ContinuousLinearMap.proj j) i)

@[simp] theorem liftRelativeContinuous_apply (q : SatelliteConfiguration) :
    liftRelativeContinuous q = liftRelative q := by
  funext i
  refine Fin.cases ?_ (fun j : Satellite => ?_) i <;>
    simp [liftRelativeContinuous, liftRelative]

def satellitesRelativeContinuous : Configuration →L[ℝ] SatelliteConfiguration :=
  ContinuousLinearMap.pi (fun i =>
    (ContinuousLinearMap.proj i.succ : Configuration →L[ℝ] Plane) - ContinuousLinearMap.proj 0)

@[simp] theorem satellitesRelativeContinuous_apply (x : Configuration) :
    satellitesRelativeContinuous x = satellitesRelative x := rfl

def relativeCenteredContinuous (ε : ℝ) (μ : MassRatio) :
    SatelliteConfiguration →L[ℝ] Configuration :=
  liftRelativeContinuous - ContinuousLinearMap.pi
    (fun _ : Label => (ε / (1 + ε)) • relativeAverageLinear μ)

@[simp] theorem relativeCenteredContinuous_apply (ε : ℝ) (μ : MassRatio)
    (q : SatelliteConfiguration) : relativeCenteredContinuous ε μ q = centeredFromRelative ε μ q := by
  ext i
  simp [relativeCenteredContinuous, centeredFromRelative, relativeAverageLinear_apply]

theorem totalMass_masses_of_sum (ε : ℝ) (μ : MassRatio) (hsum : ∑ i, μ i = 1) :
    totalMass (masses ε μ) = 1 + ε := by
  simp [totalMass, Fin.sum_univ_succ, ← Finset.mul_sum, hsum]

theorem centeredFromRelative_weightedPosition_zero_of_sum (ε : ℝ) (μ : MassRatio)
    (hsum : ∑ i, μ i = 1) (hden : 1 + ε ≠ 0) (q : SatelliteConfiguration) :
    weightedPosition (masses ε μ) (centeredFromRelative ε μ q) = 0 := by
  change weightedPosition (masses ε μ)
    (fun i => liftRelative q i - (ε / (1 + ε)) • relativeAverage μ q) = 0
  rw [weightedPosition_translate, weightedPosition_liftRelative, totalMass_masses_of_sum ε μ hsum,
    smul_smul]
  have hc : (1 + ε) * (ε / (1 + ε)) = ε := by field_simp [hden]
  rw [hc, sub_self]

theorem centered_liftRelative_of_sum (ε : ℝ) (μ : MassRatio) (hsum : ∑ i, μ i = 1)
    (q : SatelliteConfiguration) :
    centered (masses ε μ) (liftRelative q) = centeredFromRelative ε μ q := by
  ext i
  simp [centered, massCenter, totalMass_masses_of_sum ε μ hsum,
    weightedPosition_liftRelative, centeredFromRelative, div_eq_mul_inv, smul_smul, mul_comm]

theorem lift_satellitesRelative (x : Configuration) :
    liftRelative (satellitesRelative x) = primaryRelative x := by
  funext i
  refine Fin.cases ?_ (fun j : Satellite => ?_) i
  · simp [liftRelative, primaryRelative]
  · rfl

theorem centered_primaryRelative_of_centered (m : MassVector) (x : Configuration)
    (hM : totalMass m ≠ 0) (hx : weightedPosition m x = 0) :
    centered m (primaryRelative x) = x := by
  have hp : weightedPosition m (primaryRelative x) = -(totalMass m • x 0) := by
    convert! weightedPosition_translate m x (x 0) using 1
    simp only [hx, zero_sub]
  funext i
  simp [centered, massCenter, primaryRelative, hp, smul_smul, hM]

theorem centeredFromRelative_satellitesRelative (ε : ℝ) (μ : MassRatio)
    (hsum : ∑ i, μ i = 1) (hden : 1 + ε ≠ 0) (x : Configuration)
    (hx : weightedPosition (masses ε μ) x = 0) :
    centeredFromRelative ε μ (satellitesRelative x) = x := by
  rw [← centered_liftRelative_of_sum ε μ hsum, lift_satellitesRelative]
  exact centered_primaryRelative_of_centered _ x
    (by simpa only [totalMass_masses_of_sum ε μ hsum] using hden) hx

/-- Primary-relative coordinates are an actual continuous linear
isomorphism onto the centered variations. It uses only Σμ=1 and
1+ε≠0, so zero mass faces are not excluded. -/
def relativeCenteredEquiv (ε : ℝ) (μ : MassRatio) (hsum : ∑ i, μ i = 1)
    (hden : 1 + ε ≠ 0) :
    SatelliteConfiguration ≃L[ℝ] centeredVariationSpace (masses ε μ) :=
  ContinuousLinearEquiv.equivOfInverse
    ((relativeCenteredContinuous ε μ).codRestrict (centeredVariationSpace (masses ε μ))
      (fun q => by
        change weightedPositionLinear (masses ε μ) (relativeCenteredContinuous ε μ q) = 0
        rw [weightedPositionLinear_apply, relativeCenteredContinuous_apply]
        exact centeredFromRelative_weightedPosition_zero_of_sum ε μ hsum hden q))
    (satellitesRelativeContinuous.comp (centeredVariationSpace (masses ε μ)).subtypeL)
    (by
      intro q
      change satellitesRelative (centeredFromRelative ε μ q) = q
      exact satellitesRelative_centeredFromRelative ε μ q)
    (by
      intro x
      apply Subtype.ext
      simp only [ContinuousLinearMap.coe_codRestrict_apply, ContinuousLinearMap.comp_apply,
        Submodule.subtypeL_apply, relativeCenteredContinuous_apply, satellitesRelativeContinuous_apply]
      apply centeredFromRelative_satellitesRelative ε μ hsum hden x
      simpa only [centeredVariationSpace, LinearMap.mem_ker, weightedPositionLinear_apply] using x.property)

@[simp] theorem relativeCenteredEquiv_apply (ε : ℝ) (μ : MassRatio)
    (hsum : ∑ i, μ i = 1) (hden : 1 + ε ≠ 0) (q : SatelliteConfiguration) :
    (relativeCenteredEquiv ε μ hsum hden q : Configuration) = centeredFromRelative ε μ q := by
  simp only [relativeCenteredEquiv, ContinuousLinearEquiv.equivOfInverse_apply,
    ContinuousLinearMap.coe_codRestrict_apply, relativeCenteredContinuous_apply]

/-- At a true critical point, the full second-derivative coordinate
chain rule has no first-gradient curvature term. This is the actual
nested Fréchet derivative, with both variable-dependent first derivatives
differentiated before the critical equation is applied. -/
theorem second_fderiv_comp_at_critical
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (g : F → ℝ) (Ψ : E → F) (y : E)
    (hΨ : ContDiffAt ℝ 2 Ψ y) (hg : ContDiffAt ℝ 2 g (Ψ y))
    (hcrit : fderiv ℝ g (Ψ y) = 0) :
    fderiv ℝ (fderiv ℝ (g ∘ Ψ)) y =
      ((ContinuousLinearMap.compL ℝ E F ℝ).flip (fderiv ℝ Ψ y)).comp
        ((fderiv ℝ (fderiv ℝ g) (Ψ y)).comp (fderiv ℝ Ψ y)) := by
  have hΨd := hΨ.differentiableAt (by norm_num)
  have hΨdd := (hΨ.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have hgdd := (hg.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have hfirst := hgdd.hasFDerivAt.comp y hΨd.hasFDerivAt
  have hproduct := hfirst.clm_comp hΨdd.hasFDerivAt
  have hnearΨ : ∀ᶠ z in nhds y, ContDiffAt ℝ 2 Ψ z := hΨ.eventually (by norm_num)
  have hnearg : ∀ᶠ z in nhds y, ContDiffAt ℝ 2 g (Ψ z) :=
    hΨ.continuousAt.tendsto.eventually (hg.eventually (by norm_num))
  have heq : fderiv ℝ (g ∘ Ψ) =ᶠ[nhds y]
      (fun z => (fderiv ℝ g (Ψ z)).comp (fderiv ℝ Ψ z)) := by
    filter_upwards [hnearΨ, hnearg] with z hzΨ hzg
    exact fderiv_comp z (hzg.differentiableAt (by norm_num)) (hzΨ.differentiableAt (by norm_num))
  have h := (hproduct.congr_of_eventuallyEq heq).fderiv
  simpa only [Function.comp_apply, hcrit, map_zero, ContinuousLinearMap.zero_comp, zero_add] using h

def BilinearNondegenerateOn {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (B : V →L[ℝ] V →L[ℝ] ℝ) (S : Submodule ℝ V) : Prop :=
  ∀ v ∈ S, (∀ w ∈ S, B v w = 0) → v = 0

/-- Restricting a bilinear form with an exact one-direction symmetry
kernel to either transverse hyperplane gives the same nondegeneracy
condition. Both kernel identities are explicit inputs to this elementary
linear-algebra lemma. -/
theorem bilinearNondegenerateOn_transverse_imp
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (B : V →L[ℝ] V →L[ℝ] ℝ) (k : V)
    (hk : ∀ w, B k w = 0) (hkr : ∀ v, B v k = 0)
    (L₁ L₂ : V →L[ℝ] ℝ) (h₁ : L₁ k ≠ 0) (h₂ : L₂ k ≠ 0)
    (hn : BilinearNondegenerateOn B L₁.toLinearMap.ker) :
    BilinearNondegenerateOn B L₂.toLinearMap.ker := by
  intro v hv hvker
  have hvL : L₂ v = 0 := hv
  let a := L₁ v / L₁ k
  let v₁ := v - a • k
  have hv₁ : v₁ ∈ L₁.toLinearMap.ker := by
    change L₁ (v - a • k) = 0
    simp only [map_sub, map_smul, smul_eq_mul, a, div_mul_cancel₀ _ h₁, sub_self]
  have hv₁ker : ∀ w ∈ L₁.toLinearMap.ker, B v₁ w = 0 := by
    intro w _
    let w₂ := w - (L₂ w / L₂ k) • k
    have hw₂ : w₂ ∈ L₂.toLinearMap.ker := by
      change L₂ (w - (L₂ w / L₂ k) • k) = 0
      simp only [map_sub, map_smul, smul_eq_mul, div_mul_cancel₀ _ h₂, sub_self]
    have h := hvker w₂ hw₂
    have hvw : B v w = 0 := by
      simpa only [w₂, map_sub, map_smul, smul_eq_mul, hkr v, mul_zero, sub_zero] using h
    simp only [v₁, map_sub, map_smul, sub_apply, smul_apply, smul_eq_mul, hk w, mul_zero,
      sub_zero, hvw]
  have heq : v = a • k := sub_eq_zero.mp (hn v₁ hv₁ hv₁ker)
  have ha : a = 0 := by
    rw [heq, map_smul, smul_eq_mul] at hvL
    exact (mul_eq_zero.mp hvL).resolve_right h₂
  simp only [heq, ha, zero_smul]

theorem bilinearNondegenerateOn_transverse_iff
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (B : V →L[ℝ] V →L[ℝ] ℝ) (k : V)
    (hk : ∀ w, B k w = 0) (hkr : ∀ v, B v k = 0)
    (L₁ L₂ : V →L[ℝ] ℝ) (h₁ : L₁ k ≠ 0) (h₂ : L₂ k ≠ 0) :
    BilinearNondegenerateOn B L₁.toLinearMap.ker ↔
      BilinearNondegenerateOn B L₂.toLinearMap.ker :=
  ⟨bilinearNondegenerateOn_transverse_imp B k hk hkr L₁ L₂ h₁ h₂,
    bilinearNondegenerateOn_transverse_imp B k hk hkr L₂ L₁ h₂ h₁⟩

def centeredHessianOperator (m : MassVector) (lam : ℝ) (x : Configuration) :
    centeredVariationSpace m →L[ℝ] (centeredVariationSpace m →L[ℝ] ℝ) :=
  ((ContinuousLinearMap.compL ℝ (centeredVariationSpace m) Configuration ℝ).flip
      (centeredVariationSpace m).subtypeL).comp
    ((augmentedPotentialHessianMap m lam x).comp (centeredVariationSpace m).subtypeL)

@[simp] theorem centeredHessianOperator_apply (m : MassVector) (lam : ℝ)
    (x : Configuration) (v w : centeredVariationSpace m) :
    centeredHessianOperator m lam x v w = augmentedPotentialHessianMap m lam x v w := rfl

def centeredRotationConstraint (m : MassVector) (x : Configuration) :
    centeredVariationSpace m →L[ℝ] ℝ :=
  (massMetric m (rotationDirection (centered m x))).comp (centeredVariationSpace m).subtypeL

@[simp] theorem centeredRotationConstraint_apply (m : MassVector) (x : Configuration)
    (v : centeredVariationSpace m) :
    centeredRotationConstraint m x v = massInner m (rotationDirection (centered m x)) v := by
  simp only [centeredRotationConstraint, ContinuousLinearMap.comp_apply,
    Submodule.subtypeL_apply, massMetric_apply]

theorem centeredRotationConstraint_nondegenerate_iff_rotationSlice (m : MassVector)
    (lam : ℝ) (x : Configuration) (hx : CollisionFree x) :
    BilinearNondegenerateOn (centeredHessianOperator m lam x)
      (centeredRotationConstraint m x).toLinearMap.ker ↔ RotationSliceHessianNondegenerate m lam x := by
  constructor
  · intro hn v hv hk
    obtain ⟨hc, hr⟩ := (mem_rotationSliceSpace_iff m x v).mp hv
    let vE : centeredVariationSpace m := ⟨v, by
      simpa only [centeredVariationSpace, LinearMap.mem_ker, weightedPositionLinear_apply] using hc⟩
    have hvin : vE ∈ (centeredRotationConstraint m x).toLinearMap.ker := by
      simpa only [LinearMap.mem_ker, ContinuousLinearMap.coe_coe,
        centeredRotationConstraint_apply] using hr
    have hzero := hn vE hvin (by
      intro w hw
      rw [centeredHessianOperator_apply, ← physicalHessian_eq_map m lam x hx]
      apply hk w
      rw [mem_rotationSliceSpace_iff]
      constructor
      · simpa only [centeredVariationSpace, LinearMap.mem_ker, weightedPositionLinear_apply] using w.property
      · simpa only [LinearMap.mem_ker, ContinuousLinearMap.coe_coe,
          centeredRotationConstraint_apply] using hw)
    exact congrArg Subtype.val hzero
  · intro hn v hv hk
    apply Subtype.ext
    apply hn v
    · rw [mem_rotationSliceSpace_iff]
      constructor
      · simpa only [centeredVariationSpace, LinearMap.mem_ker, weightedPositionLinear_apply] using v.property
      · simpa only [LinearMap.mem_ker, ContinuousLinearMap.coe_coe,
          centeredRotationConstraint_apply] using hv
    · intro w hw
      obtain ⟨hc, hr⟩ := (mem_rotationSliceSpace_iff m x w).mp hw
      let wE : centeredVariationSpace m := ⟨w, by
        simpa only [centeredVariationSpace, LinearMap.mem_ker, weightedPositionLinear_apply] using hc⟩
      have hwE : wE ∈ (centeredRotationConstraint m x).toLinearMap.ker := by
        simpa only [LinearMap.mem_ker, ContinuousLinearMap.coe_coe,
          centeredRotationConstraint_apply] using hr
      have h := hk wE hwE
      simpa only [centeredHessianOperator_apply, physicalHessian_eq_map m lam x hx] using h

def centeredRotationVector (m : MassVector) (x : Configuration)
    (hx : NormalizedCentralConfiguration m x) : centeredVariationSpace m :=
  ⟨rotationDirection x, by
    change weightedPositionLinear m (rotationDirection x) = 0
    rw [weightedPositionLinear_apply]
    exact weightedPosition_rotation_eq_zero m x hx.2.1⟩

/-- Every actual centered hyperplane transverse to rotation has the same
physical Hessian nondegeneracy as the original six-dimensional shape
space. The transverse functional's nonzero value is a concrete
linear-algebra condition to be checked by the coordinate map. -/
theorem transverseCenteredHessian_nondegenerate_iff_shape (m : MassVector)
    (hm : PositiveMasses m) (x : Configuration) (hx : NormalizedCentralConfiguration m x)
    (L : centeredVariationSpace m →L[ℝ] ℝ)
    (hL : L (centeredRotationVector m x hx) ≠ 0) :
    BilinearNondegenerateOn (centeredHessianOperator m 1 x) L.toLinearMap.ker ↔
      ShapeHessianNondegenerate m 1 x := by
  let k := centeredRotationVector m x hx
  have hk : ∀ w, centeredHessianOperator m 1 x k w = 0 := by
    intro w
    rw [centeredHessianOperator_apply, ← physicalHessian_eq_map m 1 x hx.1]
    exact physicalHessian_rotation_of_normalizedCC m x hx w
  have hkr : ∀ v, centeredHessianOperator m 1 x v k = 0 := by
    intro v
    rw [centeredHessianOperator_apply, ← physicalHessian_eq_map m 1 x hx.1,
      physicalHessian_comm m 1 x hx.1]
    exact physicalHessian_rotation_of_normalizedCC m x hx v
  have hrot : centeredRotationConstraint m x k ≠ 0 := by
    rw [centeredRotationConstraint_apply, centered_eq_of_weightedPosition_zero m x hx.2.1]
    change massInner m (rotationDirection x) (rotationDirection x) ≠ 0
    rw [massInner_rotation_rotation]
    exact ne_of_gt (massInner_self_pos m hm x (collisionFree_ne_zero x hx.1))
  exact (bilinearNondegenerateOn_transverse_iff (centeredHessianOperator m 1 x) k
    hk hkr L (centeredRotationConstraint m x) hL hrot).trans
      ((centeredRotationConstraint_nondegenerate_iff_rotationSlice m 1 x hx.1).trans
        (rotationSliceHessian_nondegenerate_iff_shape m hm x hx))

/-- The genuine physical Hessian pulls back through a smooth coordinate
map at a normalized central configuration. This explicitly uses the
critical equation; away from roots the coordinate-curvature term cannot
be dropped. -/
theorem physicalHessian_comp_at_normalizedCC
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (m : MassVector) (Ψ : E → Configuration) (y : E)
    (hΨ : ContDiffAt ℝ 2 Ψ y) (hx : NormalizedCentralConfiguration m (Ψ y))
    (v w : E) :
    fderiv ℝ (fderiv ℝ (augmentedPotential m 1 ∘ Ψ)) y v w =
      physicalHessian m 1 (Ψ y) ((fderiv ℝ Ψ y) v) ((fderiv ℝ Ψ y) w) := by
  have h := second_fderiv_comp_at_critical (augmentedPotential m 1) Ψ y hΨ
    (augmentedPotential_contDiffAt 2 m 1 (Ψ y) hx.1)
    (normalizedCC_fderiv_augmentedPotential_zero m (Ψ y) hx)
  have hvw := congrArg (fun B : E →L[ℝ] E →L[ℝ] ℝ => B v w) h
  simpa only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.flip_apply,
    ContinuousLinearMap.compL_apply, physicalHessian] using hvw

end DominantFiveBody
