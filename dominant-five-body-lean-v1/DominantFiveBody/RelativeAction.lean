import DominantFiveBody.PotentialDerivatives
import DominantFiveBody.Residuals
import DominantFiveBody.CoorbitalModel

/-! # The actual primary-relative action and its polar gradient

Source: §3, equations `eq:action` and `eq:polar-gradient`. The explicit action
is defined before setting ε or any individual mass ratio to zero. Equality
with G/ε requires ε ≠ 0; the explicit expression supplies the extension.
-/

noncomputable section
open scoped BigOperators
open Filter Set Topology

namespace DominantFiveBody

def relativePairPotential (mu : MassRatio) (q : SatelliteConfiguration) : ℝ :=
  ∑ p ∈ satellitePairs, mu p.1*mu p.2/satelliteDistance q p.1 p.2

def relativeAction (eps : ℝ) (mu : MassRatio) (q : SatelliteConfiguration) : ℝ :=
  (∑ i, mu i*((‖q i‖)⁻¹+‖q i‖^2/2)) + eps*relativePairPotential mu q -
    eps/(1+eps)/2*‖relativeAverage mu q‖^2

theorem pairDistance_centeredFromRelative (eps : ℝ) (mu : MassRatio)
    (q : SatelliteConfiguration) (i j : Label) :
    pairDistance (centeredFromRelative eps mu q) i j=pairDistance (liftRelative q) i j := by
  unfold pairDistance centeredFromRelative
  congr 1
  abel

theorem potential_centeredFromRelative (eps : ℝ) (mu : MassRatio)
    (q : SatelliteConfiguration) :
    potential (masses eps mu) (centeredFromRelative eps mu q)=potential (masses eps mu) (liftRelative q) := by
  unfold potential
  simp_rw [pairDistance_centeredFromRelative]

/-- All four primary interactions and all six satellite interactions of U. -/
theorem potential_liftRelative (eps : ℝ) (mu : MassRatio) (q : SatelliteConfiguration) :
    potential (masses eps mu) (liftRelative q) =
      eps*(∑ i, mu i/‖q i‖)+eps^2*relativePairPotential mu q := by
  simp only [potential, pairs, relativePairPotential, satellitePairs,
    Finset.sum_filter, Fintype.sum_prod_type, Fin.sum_univ_succ]
  simp [Fin.succ_lt_succ_iff,
    masses_primary, masses_satellite, pairDistance, liftRelative, Fin.cases_zero,
    Fin.cases_succ, zero_sub, norm_neg, satelliteDistance]
  simp only [show (1 : Label)=(0 : Satellite).succ from rfl,
    show (2 : Label)=(1 : Satellite).succ from rfl,
    show (3 : Label)=(2 : Satellite).succ from rfl,
    show (4 : Label)=(3 : Satellite).succ from rfl, masses_satellite, Fin.cases_succ]
  ring

theorem inertia_translate (m : MassVector) (x : Configuration) (b : Plane) :
    inertia m (fun i => x i-b)=inertia m x -2*inner ℝ (weightedPosition m x) b +
      totalMass m*‖b‖^2 := by
  unfold inertia weightedPosition totalMass
  simp_rw [norm_sub_sq_real]
  simp only [sum_inner, real_inner_smul_left]
  simp_rw [mul_add, mul_sub, Finset.sum_add_distrib, Finset.sum_sub_distrib]
  rw [Finset.sum_mul, Finset.mul_sum]
  ring_nf
  simp only [mul_comm (‖b‖^2)]

theorem inertia_liftRelative (eps : ℝ) (mu : MassRatio) (q : SatelliteConfiguration) :
    inertia (masses eps mu) (liftRelative q)=eps*(∑ i, mu i*‖q i‖^2) := by
  simp [inertia, Fin.sum_univ_succ, liftRelative, ← Finset.mul_sum, mul_assoc]

theorem totalMass_masses_of_sum_one (eps : ℝ) (mu : MassRatio) (hsum : ∑ i, mu i=1) :
    totalMass (masses eps mu)=1+eps := by
  simp [totalMass, Fin.sum_univ_succ, ← Finset.mul_sum, hsum]

/-- The exact inertia reduction, also at zero mass ratios. -/
theorem inertia_centeredFromRelative (eps : ℝ) (mu : MassRatio) (hsum : ∑ i, mu i=1)
    (heps : 1+eps ≠ 0) (q : SatelliteConfiguration) :
    inertia (masses eps mu) (centeredFromRelative eps mu q)=
      eps*(∑ i, mu i*‖q i‖^2)-eps^2/(1+eps)*‖relativeAverage mu q‖^2 := by
  unfold centeredFromRelative
  rw [inertia_translate, inertia_liftRelative, weightedPosition_liftRelative,
    totalMass_masses_of_sum_one eps mu hsum]
  simp only [real_inner_smul_left, real_inner_smul_right, real_inner_self_eq_norm_sq,
    norm_smul, Real.norm_eq_abs, mul_pow, sq_abs]
  field_simp [heps]
  ring

/-- Formula (3.3) is proved from the actual G, with all required denominator
conditions retained. Positive ratios are not needed for this identity. -/
theorem relativeAction_eq_augmentedPotential_div (eps : ℝ) (mu : MassRatio)
    (hsum : ∑ i, mu i=1) (heps : eps ≠ 0) (hden : 1+eps ≠ 0)
    (q : SatelliteConfiguration) :
    relativeAction eps mu q = augmentedPotential (masses eps mu) 1
      (centeredFromRelative eps mu q)/eps := by
  unfold augmentedPotential
  rw [potential_centeredFromRelative, potential_liftRelative,
    inertia_centeredFromRelative eps mu hsum hden]
  unfold relativeAction
  simp_rw [mul_add, Finset.sum_add_distrib]
  simp only [div_eq_mul_inv]
  simp_rw [← mul_assoc]
  rw [← Finset.sum_mul]
  field_simp [heps, hden]
  ring

def satelliteProjection (i : Satellite) : SatelliteConfiguration →L[ℝ] Plane :=
  ContinuousLinearMap.proj i

def satelliteDifference (i j : Satellite) : SatelliteConfiguration →L[ℝ] Plane :=
  satelliteProjection i-satelliteProjection j

def relativeAverageLinear (mu : MassRatio) : SatelliteConfiguration →L[ℝ] Plane :=
  ∑ i, mu i • satelliteProjection i

@[simp] theorem relativeAverageLinear_apply (mu : MassRatio) (q : SatelliteConfiguration) :
    relativeAverageLinear mu q=relativeAverage mu q := by
  simp [relativeAverageLinear, relativeAverage, satelliteProjection]

def RelativeCollisionFree (q : SatelliteConfiguration) : Prop :=
  (∀ i, q i ≠ 0) ∧ ∀ i j, i ≠ j → q i ≠ q j

def relativePairDerivative (mu : MassRatio) (q : SatelliteConfiguration) :
    SatelliteConfiguration →L[ℝ] ℝ :=
  ∑ p ∈ satellitePairs, (-(mu p.1*mu p.2)/satelliteDistance q p.1 p.2^3) •
    ((innerSL ℝ (q p.1-q p.2)).comp (satelliteDifference p.1 p.2))

def relativeSingleDerivative (mu : MassRatio) (q : SatelliteConfiguration) :
    SatelliteConfiguration →L[ℝ] ℝ :=
  ∑ i, (mu i*(1-(‖q i‖^3)⁻¹)) • ((innerSL ℝ (q i)).comp (satelliteProjection i))

def relativeActionDerivative (eps : ℝ) (mu : MassRatio) (q : SatelliteConfiguration) :
    SatelliteConfiguration →L[ℝ] ℝ :=
  relativeSingleDerivative mu q + eps • relativePairDerivative mu q -
    (eps/(1+eps)) • ((innerSL ℝ (relativeAverage mu q)).comp (relativeAverageLinear mu))

theorem relativePairPotential_hasFDerivAt (mu : MassRatio) (q : SatelliteConfiguration)
    (hq : RelativeCollisionFree q) :
    HasFDerivAt (relativePairPotential mu) (relativePairDerivative mu q) q := by
  unfold relativePairPotential relativePairDerivative
  apply HasFDerivAt.fun_sum
  intro p hp
  have hneq := hq.2 p.1 p.2 (ne_of_lt (Finset.mem_filter.mp hp).2)
  have hn : ‖q p.1-q p.2‖ ≠ 0 := norm_ne_zero_iff.mpr (sub_ne_zero.mpr hneq)
  have hd := (norm_hasFDerivAt (q p.1-q p.2) (sub_ne_zero.mpr hneq)).comp q
    (satelliteDifference p.1 p.2).hasFDerivAt
  have H := ((hasDerivAt_inv hn).comp_hasFDerivAt q hd).const_mul (mu p.1*mu p.2)
  have heq : (fun z : SatelliteConfiguration => mu p.1*mu p.2/‖z p.1-z p.2‖) =ᶠ[nhds q]
      (fun z => mu p.1*mu p.2*(‖z p.1-z p.2‖)⁻¹) :=
    Eventually.of_forall fun z => div_eq_mul_inv _ _
  apply (H.congr_of_eventuallyEq heq).congr_fderiv
  ext v
  simp only [satelliteDistance, smul_apply, ContinuousLinearMap.comp_apply, smul_eq_mul]
  field_simp [hn]

theorem relativeSinglePotential_hasFDerivAt (mu : MassRatio) (q : SatelliteConfiguration)
    (hq : ∀ i, q i ≠ 0) :
    HasFDerivAt (fun z : SatelliteConfiguration => ∑ i, mu i*((‖z i‖)⁻¹+‖z i‖^2/2))
      (relativeSingleDerivative mu q) q := by
  unfold relativeSingleDerivative
  apply HasFDerivAt.fun_sum
  intro i _
  have hn : ‖q i‖ ≠ 0 := norm_ne_zero_iff.mpr (hq i)
  have hd := (norm_hasFDerivAt (q i) (hq i)).comp q (satelliteProjection i).hasFDerivAt
  have hrec := (hasDerivAt_inv hn).comp_hasFDerivAt q hd
  have hsq := ((hasStrictFDerivAt_norm_sq (q i)).hasFDerivAt.comp q
    (satelliteProjection i).hasFDerivAt).mul_const ((2 : ℝ)⁻¹)
  convert! (hrec.add hsq).const_mul (mu i) using 1
  ext v
  simp only [smul_apply, add_apply, ContinuousLinearMap.comp_apply,
    smul_eq_mul]
  field_simp [hn]
  ring

/-- The first derivative of the actual extended relative action. It remains
valid at ε=0 and at zero individual ratios, provided physical positions differ. -/
theorem relativeAction_hasFDerivAt (eps : ℝ) (mu : MassRatio) (q : SatelliteConfiguration)
    (hq : RelativeCollisionFree q) :
    HasFDerivAt (relativeAction eps mu) (relativeActionDerivative eps mu q) q := by
  have hsingle := relativeSinglePotential_hasFDerivAt mu q hq.1
  have hpair := (relativePairPotential_hasFDerivAt mu q hq).const_mul eps
  have havg := ((hasStrictFDerivAt_norm_sq (relativeAverage mu q)).hasFDerivAt.comp q
    (relativeAverageLinear mu).hasFDerivAt).const_mul (eps/(1+eps)/2)
  convert! (hsingle.add hpair).sub havg using 1
  ext v
  simp only [relativeActionDerivative, sub_apply, add_apply, smul_apply,
    ContinuousLinearMap.comp_apply, smul_eq_mul]
  ring

def satelliteInteraction (mu : MassRatio) (q : SatelliteConfiguration) (i : Satellite) : Plane :=
  ∑ j ∈ Finset.univ.erase i, (mu j/satelliteDistance q i j^3) • (q j-q i)

def satellitePairForce (mu : MassRatio) (q : SatelliteConfiguration) (i j : Satellite) : Plane :=
  (mu i*mu j/satelliteDistance q i j^3) • (q j-q i)

@[simp] theorem satellitePairForce_self (mu : MassRatio) (q : SatelliteConfiguration) (i : Satellite) :
    satellitePairForce mu q i i=0 := by simp [satellitePairForce]

theorem satellitePairForce_reverse (mu : MassRatio) (q : SatelliteConfiguration) (i j : Satellite) :
    satellitePairForce mu q j i = -satellitePairForce mu q i j := by
  unfold satellitePairForce satelliteDistance
  rw [norm_sub_rev (q j) (q i), mul_comm (mu j) (mu i)]
  rw [show q i-q j=-(q j-q i) from by abel, smul_neg]

theorem weighted_satelliteInteraction (mu : MassRatio) (q : SatelliteConfiguration) (i : Satellite) :
    mu i • satelliteInteraction mu q i = ∑ j, satellitePairForce mu q i j := by
  simp [satelliteInteraction, satellitePairForce, Finset.smul_sum, smul_smul,
    mul_div_assoc, Finset.sum_erase_eq_sub]

theorem weighted_satelliteInteraction_zero (mu : MassRatio) (q : SatelliteConfiguration) :
    (∑ i, mu i • satelliteInteraction mu q i)=0 := by
  simp_rw [weighted_satelliteInteraction]
  have hneg : (∑ i, ∑ j, satellitePairForce mu q i j) =
      -(∑ i, ∑ j, satellitePairForce mu q i j) := by
    calc
      _ = ∑ j, ∑ i, satellitePairForce mu q i j := Finset.sum_comm
      _ = -(∑ j, ∑ i, satellitePairForce mu q j i) := by
        rw [← Finset.sum_neg_distrib]
        apply Finset.sum_congr rfl
        intro j _
        rw [← Finset.sum_neg_distrib]
        apply Finset.sum_congr rfl
        intro i _
        exact satellitePairForce_reverse mu q j i
  have htwice : (2 : ℝ) • (∑ i, ∑ j, satellitePairForce mu q i j)=0 := by
    rw [two_smul]
    exact eq_neg_iff_add_eq_zero.mp hneg
  exact (smul_eq_zero.mp htwice).resolve_left (by norm_num)

theorem sum_satellite_orderedPairs_eq_unordered (f : Satellite → Satellite → ℝ)
    (hdiag : ∀ i, f i i=0) :
    (∑ i, ∑ j, f i j)=∑ p ∈ satellitePairs, (f p.1 p.2+f p.2 p.1) := by
  simp [satellitePairs, Finset.sum_filter, Fintype.sum_prod_type, Fin.sum_univ_four, hdiag]
  ring

theorem relativePairDerivative_apply (mu : MassRatio) (q v : SatelliteConfiguration) :
    relativePairDerivative mu q v=∑ i, mu i*inner ℝ (satelliteInteraction mu q i) (v i) := by
  have hsum := sum_satellite_orderedPairs_eq_unordered
    (fun i j => inner ℝ (satellitePairForce mu q i j) (v i)) (by intro i; simp)
  have heq : (∑ i, mu i*inner ℝ (satelliteInteraction mu q i) (v i)) =
      ∑ i, ∑ j, inner ℝ (satellitePairForce mu q i j) (v i) := by
    simp_rw [← real_inner_smul_left, weighted_satelliteInteraction, sum_inner]
  rw [heq, hsum]
  simp only [relativePairDerivative, sum_apply, smul_apply, ContinuousLinearMap.comp_apply,
    smul_eq_mul]
  apply Finset.sum_congr rfl
  intro p _
  rw [satellitePairForce_reverse mu q p.1 p.2, inner_neg_left]
  simp only [satellitePairForce, real_inner_smul_left, inner_sub_right,
    satelliteDifference, satelliteProjection, sub_apply, ContinuousLinearMap.proj_apply,
    innerSL_apply_apply, inner_sub_left]
  ring

theorem relativeSingleDerivative_apply (mu : MassRatio) (q v : SatelliteConfiguration) :
    relativeSingleDerivative mu q v =
      ∑ i, mu i*inner ℝ (q i-(‖q i‖^3)⁻¹ • q i) (v i) := by
  simp only [relativeSingleDerivative, sum_apply, smul_apply, ContinuousLinearMap.comp_apply,
    satelliteProjection, ContinuousLinearMap.proj_apply, smul_eq_mul, innerSL_apply_apply]
  apply Finset.sum_congr rfl
  intro i _
  rw [inner_sub_left, real_inner_smul_left]
  ring

def relativeActionVectorGradient (eps : ℝ) (mu : MassRatio) (q : SatelliteConfiguration)
    (i : Satellite) : Plane :=
  mu i • (q i-(‖q i‖^3)⁻¹ • q i + eps • satelliteInteraction mu q i -
    (eps/(1+eps)) • relativeAverage mu q)

theorem relativeActionDerivative_apply (eps : ℝ) (mu : MassRatio)
    (q v : SatelliteConfiguration) :
    relativeActionDerivative eps mu q v = ∑ i, inner ℝ (relativeActionVectorGradient eps mu q i) (v i) := by
  simp only [relativeActionDerivative, add_apply, sub_apply, smul_apply,
    ContinuousLinearMap.comp_apply, relativeAverageLinear_apply, smul_eq_mul,
    relativePairDerivative_apply, relativeSingleDerivative_apply]
  simp only [innerSL_apply_apply, relativeAverage, inner_sum]
  simp_rw [real_inner_smul_right, Finset.mul_sum]
  rw [← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i _
  simp only [relativeActionVectorGradient, real_inner_smul_left, inner_sub_left,
    inner_add_left, relativeAverage]
  ring

theorem vectorResidual_weighted_sum (eps : ℝ) (mu : MassRatio)
    (hsum : ∑ i, mu i=1) (q : SatelliteConfiguration) :
    (∑ i, mu i • vectorResidual eps mu q i) = relativeAverage mu q - (1+eps) • relativeField mu q := by
  change (∑ i, mu i • (q i-(‖q i‖^3)⁻¹ • q i + eps • satelliteInteraction mu q i-
    eps • relativeField mu q)) = _
  simp_rw [smul_sub, smul_add, Finset.sum_sub_distrib, Finset.sum_add_distrib]
  simp_rw [smul_sub, Finset.sum_sub_distrib]
  have hfield : (∑ i, mu i • ((‖q i‖^3)⁻¹ • q i))=relativeField mu q := by
    simp only [relativeField, smul_smul, div_eq_mul_inv]
  have hzero : (∑ i, mu i • (eps • satelliteInteraction mu q i))=0 := by
    simp_rw [smul_comm (mu _) eps]
    rw [← Finset.smul_sum, weighted_satelliteInteraction_zero, smul_zero]
  rw [hfield, hzero, add_zero, ← Finset.sum_smul, hsum, one_smul]
  change relativeAverage mu q-relativeField mu q-eps • relativeField mu q = _
  rw [add_smul, one_smul]
  abel

theorem relativeMassMatrix_action (eps : ℝ) (mu : MassRatio) (v : SatelliteConfiguration)
    (i : Satellite) :
    (∑ j, relativeMassMatrix eps mu i j • v j) =
      mu i • (v i-(eps/(1+eps)) • relativeAverage mu v) := by
  unfold relativeMassMatrix
  simp_rw [sub_smul, Finset.sum_sub_distrib]
  have hdiag : (∑ j, (if i=j then mu i else 0) • v j)=mu i • v i := by simp
  rw [hdiag]
  simp only [relativeAverage, smul_sub, Finset.smul_sum, smul_smul]
  congr 1
  apply Finset.sum_congr rfl
  intro j _
  congr 1
  ring

/-- Away from roots, the actual extended gradient is (C tensor I₂)F. The
weighted residual identity is proved before any mass is set to zero. -/
theorem relativeActionVectorGradient_eq_CF (eps : ℝ) (mu : MassRatio)
    (hsum : ∑ i, mu i=1) (hden : 1+eps ≠ 0) (q : SatelliteConfiguration) (i : Satellite) :
    relativeActionVectorGradient eps mu q i =
      ∑ j, relativeMassMatrix eps mu i j • vectorResidual eps mu q j := by
  rw [relativeMassMatrix_action]
  change _ = mu i • (vectorResidual eps mu q i - (eps/(1+eps)) •
    (∑ j, mu j • vectorResidual eps mu q j))
  rw [vectorResidual_weighted_sum eps mu hsum q]
  have heq : eps/(1+eps)*(1+eps)=eps := div_mul_cancel₀ eps hden
  unfold relativeActionVectorGradient vectorResidual
  change mu i • (q i-(‖q i‖^3)⁻¹ • q i+eps • satelliteInteraction mu q i-
      (eps/(1+eps)) • relativeAverage mu q) =
    mu i • ((q i-(‖q i‖^3)⁻¹ • q i+eps • satelliteInteraction mu q i-eps • relativeField mu q)-
      (eps/(1+eps)) • (relativeAverage mu q-(1+eps) • relativeField mu q))
  rw [smul_sub (eps/(1+eps)), smul_smul, heq]
  module

theorem polarPoint_norm_sq (r theta : ℝ) : ‖polarPoint r theta‖^2=r^2 := by
  rw [EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_two]
  simp only [polarPoint, point, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one]
  nlinarith [Real.sin_sq_add_cos_sq theta]

theorem polarPoint_norm (r theta : ℝ) : ‖polarPoint r theta‖=|r| := by
  exact (sq_eq_sq₀ (norm_nonneg _) (abs_nonneg r)).mp
    (by simpa only [sq_abs] using polarPoint_norm_sq r theta)

theorem polarPoint_inner_radial (r phi theta : ℝ) :
    inner ℝ (polarPoint r phi) (polarPoint 1 theta)=r*Real.cos (phi-theta) := by
  rw [plane_inner_coordinates]
  simp only [polarPoint, point, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_fin_one, one_mul]
  rw [Real.cos_sub]
  ring

theorem polarPoint_inner_rotation (r s phi theta : ℝ) :
    inner ℝ (polarPoint r phi) (quarterTurn (polarPoint s theta))=s*r*Real.sin (phi-theta) := by
  rw [plane_inner_coordinates]
  simp only [polarPoint, quarterTurn, point, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_fin_one]
  rw [Real.sin_sub]
  ring

/-- Radial projection of the true action gradient is precisely μᵢRᵢ. -/
theorem relativeActionVectorGradient_radial (eps : ℝ) (mu r theta : Satellite → ℝ)
    (hr : ∀ i, 0<r i) (i : Satellite) :
    inner ℝ (relativeActionVectorGradient eps mu (polarSatellites r theta) i)
      (polarPoint 1 (theta i))=mu i*radialResidual eps mu r theta i := by
  have hnorm : ‖polarSatellites r theta i‖=r i := by
    simpa only [polarSatellites, abs_of_pos (hr i)] using polarPoint_norm (r i) (theta i)
  have hinner : inner ℝ (polarSatellites r theta i) (polarPoint 1 (theta i))=r i := by
    simpa only [polarSatellites, sub_self, Real.cos_zero, mul_one] using
      polarPoint_inner_radial (r i) (theta i) (theta i)
  have hint : inner ℝ (satelliteInteraction mu (polarSatellites r theta) i) (polarPoint 1 (theta i)) =
      -(∑ j ∈ Finset.univ.erase i, mu j*(r i-r j*Real.cos (theta j-theta i))/
        satelliteDistance (polarSatellites r theta) i j^3) := by
    unfold satelliteInteraction
    simp only [sum_inner, real_inner_smul_left, inner_sub_left, polarSatellites,
      polarPoint_inner_radial, sub_self, Real.cos_zero, mul_one]
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro j _
    ring
  have hrad : r i-(r i^3)⁻¹*r i=r i-(r i^2)⁻¹ := by
    field_simp [ne_of_gt (hr i)]
  simp only [relativeActionVectorGradient, real_inner_smul_left, inner_sub_left,
    inner_add_left, hnorm, hinner, hint, hrad]
  unfold radialResidual
  ring

/-- Tangential projection is ε μᵢ Tᵢ, retaining both small parameters before
division. No mass ratio or ε is canceled in this identity. -/
theorem relativeActionVectorGradient_angular (eps : ℝ) (mu r theta : Satellite → ℝ)
    (i : Satellite) :
    inner ℝ (relativeActionVectorGradient eps mu (polarSatellites r theta) i)
      (quarterTurn (polarSatellites r theta i))=eps*mu i*angularResidual eps mu r theta i := by
  have hint : inner ℝ (satelliteInteraction mu (polarSatellites r theta) i)
      (quarterTurn (polarSatellites r theta i)) =
      ∑ j ∈ Finset.univ.erase i, mu j*r i*r j*Real.sin (theta j-theta i)/
        satelliteDistance (polarSatellites r theta) i j^3 := by
    unfold satelliteInteraction
    simp only [sum_inner, real_inner_smul_left, inner_sub_left, quarterTurn_inner_self,
      sub_zero, polarSatellites, polarPoint_inner_rotation]
    apply Finset.sum_congr rfl
    intro j _
    ring
  have havg : inner ℝ (relativeAverage mu (polarSatellites r theta))
      (quarterTurn (polarSatellites r theta i)) =
      ∑ j ∈ Finset.univ.erase i, mu j*r i*r j*Real.sin (theta j-theta i) := by
    simp only [relativeAverage, sum_inner, real_inner_smul_left, polarSatellites,
      polarPoint_inner_rotation]
    rw [Finset.sum_erase_eq_sub (Finset.mem_univ i)]
    simp only [sub_self, Real.sin_zero, mul_zero, sub_zero]
    apply Finset.sum_congr rfl
    intro j _
    ring
  simp only [relativeActionVectorGradient, real_inner_smul_left, inner_sub_left,
    inner_add_left, quarterTurn_inner_self, mul_zero, sub_zero, zero_add, hint, havg]
  unfold angularResidual
  simp_rw [mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul]
  simp only [div_eq_mul_inv, mul_assoc]
  ring

abbrev PolarCoordinates := (Satellite → ℝ) × (Satellite → ℝ)

def polarCoordinateMap (p : PolarCoordinates) : SatelliteConfiguration :=
  polarSatellites p.1 p.2

def polarRadialProjection (i : Satellite) : PolarCoordinates →L[ℝ] ℝ :=
  (ContinuousLinearMap.proj i).comp (ContinuousLinearMap.fst ℝ _ _)

def polarAngularProjection (i : Satellite) : PolarCoordinates →L[ℝ] ℝ :=
  (ContinuousLinearMap.proj i).comp (ContinuousLinearMap.snd ℝ _ _)

def polarCoordinateDerivative (p : PolarCoordinates) :
    PolarCoordinates →L[ℝ] SatelliteConfiguration :=
  ContinuousLinearMap.pi fun i =>
    (polarRadialProjection i).smulRight (polarPoint 1 (p.2 i)) +
      (polarAngularProjection i).smulRight (quarterTurn (polarPoint (p.1 i) (p.2 i)))

theorem polarCoordinateDerivative_apply (p v : PolarCoordinates) (i : Satellite) :
    polarCoordinateDerivative p v i = v.1 i • polarPoint 1 (p.2 i) +
      v.2 i • quarterTurn (polarPoint (p.1 i) (p.2 i)) := by
  rfl

/-- The derivative is of the actual eight-variable polar map. Both radial
and angular variations are included before taking any partial derivative. -/
theorem polarCoordinateMap_hasFDerivAt (p : PolarCoordinates) :
    HasFDerivAt polarCoordinateMap (polarCoordinateDerivative p) p := by
  apply hasFDerivAt_pi.mpr
  intro i
  have hr : HasFDerivAt (fun z : PolarCoordinates => z.1 i) (polarRadialProjection i) p :=
    (polarRadialProjection i).hasFDerivAt
  have ht : HasFDerivAt (fun z : PolarCoordinates => z.2 i) (polarAngularProjection i) p :=
    (polarAngularProjection i).hasFDerivAt
  have hc := (Real.hasDerivAt_cos (p.2 i)).comp_hasFDerivAt p ht
  have hs := (Real.hasDerivAt_sin (p.2 i)).comp_hasFDerivAt p ht
  let d : PolarCoordinates →L[ℝ] (Fin 2 → ℝ) :=
    ContinuousLinearMap.pi (fun k => if k=0 then
      (Real.cos (p.2 i)) • polarRadialProjection i +
        (p.1 i) • ((-Real.sin (p.2 i)) • polarAngularProjection i)
      else (Real.sin (p.2 i)) • polarRadialProjection i +
        (p.1 i) • ((Real.cos (p.2 i)) • polarAngularProjection i))
  have hcoords : HasFDerivAt
      (fun z : PolarCoordinates => ![z.1 i*Real.cos (z.2 i), z.1 i*Real.sin (z.2 i)]) d p := by
    apply hasFDerivAt_pi.mpr
    intro k
    fin_cases k
    · convert! hr.mul hc using 1
      apply ContinuousLinearMap.ext
      intro v
      change Real.cos (p.2 i)*v.1 i + p.1 i*(-Real.sin (p.2 i)*v.2 i) =
        p.1 i*(-Real.sin (p.2 i)*v.2 i) + Real.cos (p.2 i)*v.1 i
      ring
    · convert! hr.mul hs using 1
      apply ContinuousLinearMap.ext
      intro v
      change Real.sin (p.2 i)*v.1 i + p.1 i*(Real.cos (p.2 i)*v.2 i) =
        p.1 i*(Real.cos (p.2 i)*v.2 i) + Real.sin (p.2 i)*v.1 i
      ring
  have h := (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 2 => ℝ)).symm.hasFDerivAt.comp p hcoords
  apply h.congr_fderiv
  apply ContinuousLinearMap.ext
  intro v
  change (WithLp.toLp 2 (d v) : Plane) =
    v.1 i • polarPoint 1 (p.2 i) + v.2 i • quarterTurn (polarPoint (p.1 i) (p.2 i))
  ext k
  fin_cases k <;>
    simp [d, polarRadialProjection, polarAngularProjection,
      polarPoint, quarterTurn, point, smul_smul] <;> ring

def polarAction (eps : ℝ) (mu : MassRatio) (p : PolarCoordinates) : ℝ :=
  relativeAction eps mu (polarCoordinateMap p)

def polarActionDerivative (eps : ℝ) (mu : MassRatio) (p : PolarCoordinates) :
    PolarCoordinates →L[ℝ] ℝ :=
  (relativeActionDerivative eps mu (polarCoordinateMap p)).comp (polarCoordinateDerivative p)

theorem polarAction_hasFDerivAt (eps : ℝ) (mu : MassRatio) (p : PolarCoordinates)
    (hq : RelativeCollisionFree (polarCoordinateMap p)) :
    HasFDerivAt (polarAction eps mu) (polarActionDerivative eps mu p) p :=
  (relativeAction_hasFDerivAt eps mu _ hq).comp p (polarCoordinateMap_hasFDerivAt p)

/-- Formula (3.6), as the full differential of Φ composed with the true
polar coordinate map. No positivity or nonvanishing of the masses is used. -/
theorem polarActionDerivative_apply (eps : ℝ) (mu : MassRatio)
    (p v : PolarCoordinates) (hr : ∀ i, 0<p.1 i) :
    polarActionDerivative eps mu p v =
      (∑ i, mu i*radialResidual eps mu p.1 p.2 i*v.1 i) +
        (∑ i, eps*mu i*angularResidual eps mu p.1 p.2 i*v.2 i) := by
  rw [polarActionDerivative, ContinuousLinearMap.comp_apply, relativeActionDerivative_apply]
  simp only [polarCoordinateDerivative_apply, inner_add_right,
    real_inner_smul_right, Finset.sum_add_distrib, polarCoordinateMap]
  congr 1 <;> apply Finset.sum_congr rfl <;> intro i _
  · rw [relativeActionVectorGradient_radial eps mu p.1 p.2 hr i]
    ring
  · change v.2 i*inner ℝ (relativeActionVectorGradient eps mu (polarSatellites p.1 p.2) i)
        (quarterTurn (polarSatellites p.1 p.2 i)) = _
    rw [relativeActionVectorGradient_angular eps mu p.1 p.2 i]
    ring

theorem polarAction_fderiv_apply (eps : ℝ) (mu : MassRatio)
    (p v : PolarCoordinates) (hr : ∀ i, 0<p.1 i)
    (hq : RelativeCollisionFree (polarCoordinateMap p)) :
    fderiv ℝ (polarAction eps mu) p v =
      (∑ i, mu i*radialResidual eps mu p.1 p.2 i*v.1 i) +
        (∑ i, eps*mu i*angularResidual eps mu p.1 p.2 i*v.2 i) := by
  rw [(polarAction_hasFDerivAt eps mu p hq).fderiv]
  exact polarActionDerivative_apply eps mu p v hr

def angularResidualPair (eps : ℝ) (mu r theta : Satellite → ℝ) (i j : Satellite) : ℝ :=
  mu i*mu j*r i*r j*Real.sin (theta j-theta i)*
    ((satelliteDistance (polarSatellites r theta) i j^3)⁻¹-(1+eps)⁻¹)

theorem angularResidualPair_reverse (eps : ℝ) (mu r theta : Satellite → ℝ)
    (i j : Satellite) :
    angularResidualPair eps mu r theta j i = -angularResidualPair eps mu r theta i j := by
  unfold angularResidualPair satelliteDistance
  rw [norm_sub_rev (polarSatellites r theta j) (polarSatellites r theta i)]
  rw [show theta i-theta j=-(theta j-theta i) by ring, Real.sin_neg]
  ring

/-- The angular identity holds at every physical point, including zero masses
and ε = 0. It is proved without division by any mass or by ε. -/
theorem weighted_angularResidual_zero (eps : ℝ) (mu r theta : Satellite → ℝ) :
    (∑ i, mu i*angularResidual eps mu r theta i)=0 := by
  have heq (i : Satellite) : mu i*angularResidual eps mu r theta i =
      ∑ j, angularResidualPair eps mu r theta i j := by
    unfold angularResidual
    rw [Finset.mul_sum, Finset.sum_erase_eq_sub (Finset.mem_univ i)]
    simp only [angularResidualPair, sub_self, Real.sin_zero, mul_zero, zero_mul, sub_zero]
    apply Finset.sum_congr rfl
    intro j _
    ring
  simp_rw [heq]
  have hneg : (∑ i, ∑ j, angularResidualPair eps mu r theta i j) =
      -(∑ i, ∑ j, angularResidualPair eps mu r theta i j) := by
    calc
      (∑ i, ∑ j, angularResidualPair eps mu r theta i j) =
          ∑ j, ∑ i, angularResidualPair eps mu r theta i j := Finset.sum_comm
      _ = -(∑ j, ∑ i, angularResidualPair eps mu r theta j i) := by
        rw [← Finset.sum_neg_distrib]
        apply Finset.sum_congr rfl
        intro j _
        rw [← Finset.sum_neg_distrib]
        apply Finset.sum_congr rfl
        intro i _
        exact angularResidualPair_reverse eps mu r theta j i
  linarith

theorem angularResidual_omitted_row (eps : ℝ) (mu r theta : Satellite → ℝ)
    (p : Satellite) (hp : mu p≠0)
    (hrows : ∀ i, i≠p → angularResidual eps mu r theta i=0) :
    angularResidual eps mu r theta p=0 := by
  have hsum := weighted_angularResidual_zero eps mu r theta
  have hred : (∑ i, mu i*angularResidual eps mu r theta i)=
      mu p*angularResidual eps mu r theta p := by
    apply Finset.sum_eq_single p
    · intro i _ hip
      rw [hrows i hip, mul_zero]
    · simp
  rw [hred] at hsum
  exact (mul_eq_zero.mp hsum).resolve_left hp

theorem relativeActionVectorGradient_zero_of_vectorResidual_zero (eps : ℝ)
    (mu : MassRatio) (hsum : ∑ i, mu i=1) (hden : 1+eps≠0)
    (q : SatelliteConfiguration) (hroot : ∀ i, vectorResidual eps mu q i=0) :
    ∀ i, relativeActionVectorGradient eps mu q i=0 := by
  intro i
  rw [relativeActionVectorGradient_eq_CF eps mu hsum hden q i]
  simp only [hroot, smul_zero, Finset.sum_const_zero]

/-- Every actual positive-mass vector root satisfies all four divided radial
and angular rows. The angular factor ε and each μᵢ are proved nonzero first. -/
theorem polarResiduals_zero_of_vectorResidual_zero (eps : ℝ)
    (mu r theta : Satellite → ℝ) (hm : PositiveRatio mu) (heps : 0<eps)
    (hr : ∀ i, 0<r i)
    (hroot : ∀ i, vectorResidual eps mu (polarSatellites r theta) i=0) :
    (∀ i, radialResidual eps mu r theta i=0) ∧
      (∀ i, angularResidual eps mu r theta i=0) := by
  have hgrad := relativeActionVectorGradient_zero_of_vectorResidual_zero eps mu hm.2
    (by linarith) (polarSatellites r theta) hroot
  constructor
  · intro i
    have h := relativeActionVectorGradient_radial eps mu r theta hr i
    rw [hgrad i, inner_zero_left] at h
    exact (mul_eq_zero.mp h.symm).resolve_left (ne_of_gt (hm.1 i))
  · intro i
    have h := relativeActionVectorGradient_angular eps mu r theta i
    rw [hgrad i, inner_zero_left] at h
    exact (mul_eq_zero.mp h.symm).resolve_left (mul_ne_zero (ne_of_gt heps) (ne_of_gt (hm.1 i)))

end DominantFiveBody


