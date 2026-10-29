import DominantFiveBody.SimilarityNormalization
import Mathlib.Geometry.Euclidean.Angle.Oriented.Rotation

/-! # Actual SO(2) transport, normalized similarity and shape Hessians -/

noncomputable section
open scoped BigOperators

namespace DominantFiveBody

def rotateConfiguration (R : Plane ≃ₗᵢ[ℝ] Plane) (x : Configuration) : Configuration :=
  fun i => R (x i)

theorem weightedPosition_rotateConfiguration (m : MassVector) (R : Plane ≃ₗᵢ[ℝ] Plane)
    (x : Configuration) : weightedPosition m (rotateConfiguration R x)=R (weightedPosition m x) := by
  simp only [weightedPosition,rotateConfiguration,map_sum,map_smul]

theorem massCenter_rotateConfiguration (m : MassVector) (R : Plane ≃ₗᵢ[ℝ] Plane)
    (x : Configuration) : massCenter m (rotateConfiguration R x)=R (massCenter m x) := by
  simp only [massCenter,weightedPosition_rotateConfiguration,map_smul]

theorem centered_rotateConfiguration (m : MassVector) (R : Plane ≃ₗᵢ[ℝ] Plane)
    (x : Configuration) : centered m (rotateConfiguration R x)=rotateConfiguration R (centered m x) := by
  funext i
  rw [centered,massCenter_rotateConfiguration]
  exact (R.map_sub _ _).symm

theorem collisionFree_rotateConfiguration (R : Plane ≃ₗᵢ[ℝ] Plane)
    (x : Configuration) (hx : CollisionFree x) : CollisionFree (rotateConfiguration R x) := by
  intro i j hij h
  exact hx i j hij (R.injective h)

theorem pairDistance_rotateConfiguration (R : Plane ≃ₗᵢ[ℝ] Plane)
    (x : Configuration) (i j : Label) : pairDistance (rotateConfiguration R x) i j=pairDistance x i j := by
  simp only [pairDistance,rotateConfiguration,←map_sub,R.norm_map]

theorem acceleration_rotateConfiguration (m : MassVector) (R : Plane ≃ₗᵢ[ℝ] Plane)
    (x : Configuration) (i : Label) :
    acceleration m (rotateConfiguration R x) i=R (acceleration m x i) := by
  simp only [acceleration,pairDistance_rotateConfiguration,rotateConfiguration,map_sum,map_smul,map_sub]

theorem normalizedCC_rotateConfiguration (m : MassVector) (R : Plane ≃ₗᵢ[ℝ] Plane)
    (x : Configuration) (hx : NormalizedCentralConfiguration m x) :
    NormalizedCentralConfiguration m (rotateConfiguration R x) := by
  refine ⟨collisionFree_rotateConfiguration R x hx.1,?_,?_⟩
  · rw [weightedPosition_rotateConfiguration,hx.2.1,map_zero]
  · intro i
    rw [acceleration_rotateConfiguration,hx.2.2 i,map_neg]
    rfl

theorem massInner_rotateConfiguration (m : MassVector) (R : Plane ≃ₗᵢ[ℝ] Plane)
    (v w : Configuration) :
    massInner m (rotateConfiguration R v) (rotateConfiguration R w)=massInner m v w := by
  simp only [massInner,rotateConfiguration,R.inner_map_map]

theorem plane_basis_det (u v : Plane) :
    (EuclideanSpace.basisFun (Fin 2) ℝ).toBasis.det ![u,v]=det2 u v := by
  rw [Module.Basis.det_apply,Matrix.det_fin_two]
  simp [Module.Basis.toMatrix_apply,EuclideanSpace.basisFun_repr,det2]
  ring

theorem det2_linearIsometryEquiv (R : Plane ≃ₗᵢ[ℝ] Plane) (u v : Plane) :
    det2 (R u) (R v)=LinearMap.det R.toLinearEquiv.toLinearMap*det2 u v := by
  let b := (EuclideanSpace.basisFun (Fin 2) ℝ).toBasis
  have h := b.det_comp R.toLinearEquiv.toLinearMap ![u,v]
  have he : R.toLinearEquiv.toLinearMap ∘ ![u,v]=![R u,R v] := by
    ext i
    fin_cases i <;> rfl
  rw [he,plane_basis_det,plane_basis_det] at h
  exact h

theorem quarterTurn_inner_eq_det2 (u v : Plane) : inner ℝ (quarterTurn u) v=det2 u v := by
  simp [plane_inner_coordinates,quarterTurn,point,det2]
  ring

theorem massInner_rotation_rotateConfiguration (m : MassVector) (R : Plane ≃ₗᵢ[ℝ] Plane)
    (v w : Configuration) (hdet : LinearMap.det R.toLinearEquiv.toLinearMap=1) :
    massInner m (rotationDirection (rotateConfiguration R v)) (rotateConfiguration R w)=
      massInner m (rotationDirection v) w := by
  simp only [massInner,rotationDirection,rotateConfiguration,quarterTurn_inner_eq_det2,
    det2_linearIsometryEquiv,hdet,one_mul]

theorem orientedArea_rotateConfiguration (R : Plane ≃ₗᵢ[ℝ] Plane) (x : Configuration)
    (hdet : LinearMap.det R.toLinearEquiv.toLinearMap=1) (i j k : Label) :
    orientedArea (rotateConfiguration R x) i j k=orientedArea x i j k := by
  simp only [orientedArea,rotateConfiguration,←map_sub,det2_linearIsometryEquiv,hdet,one_mul]

theorem strictConvex_rotateConfiguration_iff (σ : HullOrder) (R : Plane ≃ₗᵢ[ℝ] Plane)
    (x : Configuration) (hdet : LinearMap.det R.toLinearEquiv.toLinearMap=1) :
    StrictConvexInOrder σ (rotateConfiguration R x) ↔ StrictConvexInOrder σ x := by
  simp only [StrictConvexInOrder,orientedArea_rotateConfiguration R x hdet]

theorem shapeSpace_rotateConfiguration_mem_iff (m : MassVector) (R : Plane ≃ₗᵢ[ℝ] Plane)
    (x v : Configuration) (hdet : LinearMap.det R.toLinearEquiv.toLinearMap=1) :
    rotateConfiguration R v ∈ shapeSpace m (rotateConfiguration R x) ↔ v ∈ shapeSpace m x := by
  rw [mem_shapeSpace_iff,mem_shapeSpace_iff,centered_rotateConfiguration,
    weightedPosition_rotateConfiguration,massInner_rotateConfiguration,
    massInner_rotation_rotateConfiguration m R _ _ hdet]
  rw [R.map_eq_zero_iff]

theorem physicalHessian_rotateConfiguration (m : MassVector) (lam : ℝ) (R : Plane ≃ₗᵢ[ℝ] Plane)
    (x : Configuration) (hx : CollisionFree x) (v w : Configuration) :
    physicalHessian m lam (rotateConfiguration R x) (rotateConfiguration R v) (rotateConfiguration R w)=
      physicalHessian m lam x v w := by
  rw [physicalHessian_explicit m lam _ (collisionFree_rotateConfiguration R x hx),
    physicalHessian_explicit m lam x hx,massInner_rotateConfiguration]
  simp only [pairDistance_rotateConfiguration,rotateConfiguration,←map_sub,R.inner_map_map]

theorem shapeHessianNondegenerate_rotateConfiguration_forward (m : MassVector) (lam : ℝ)
    (R : Plane ≃ₗᵢ[ℝ] Plane) (x : Configuration) (hx : CollisionFree x)
    (hdet : LinearMap.det R.toLinearEquiv.toLinearMap=1)
    (hn : ShapeHessianNondegenerate m lam x) :
    ShapeHessianNondegenerate m lam (rotateConfiguration R x) := by
  intro v hv hk
  let u := rotateConfiguration R.symm v
  have hrecover : rotateConfiguration R u=v := by funext i; exact R.apply_symm_apply (v i)
  have hu : u ∈ shapeSpace m x := by
    apply (shapeSpace_rotateConfiguration_mem_iff m R x u hdet).mp
    rwa [hrecover]
  have hz := hn u hu (by
    intro w hw
    have h := hk (rotateConfiguration R w) ((shapeSpace_rotateConfiguration_mem_iff m R x w hdet).mpr hw)
    rw [←hrecover,physicalHessian_rotateConfiguration m lam R x hx u w] at h
    exact h)
  rw [←hrecover,hz]
  funext i
  exact R.map_zero

theorem shapeHessianNondegenerate_rotateConfiguration_iff (m : MassVector) (lam : ℝ)
    (R : Plane ≃ₗᵢ[ℝ] Plane) (x : Configuration) (hx : CollisionFree x)
    (hdet : LinearMap.det R.toLinearEquiv.toLinearMap=1) :
    ShapeHessianNondegenerate m lam (rotateConfiguration R x) ↔ ShapeHessianNondegenerate m lam x := by
  constructor
  · intro hn
    have hprod := LinearEquiv.det_mul_det_symm R.toLinearEquiv
    rw [hdet,one_mul] at hprod
    have h := shapeHessianNondegenerate_rotateConfiguration_forward m lam R.symm _
      (collisionFree_rotateConfiguration R x hx) hprod hn
    have he : rotateConfiguration R.symm (rotateConfiguration R x)=x := by
      funext i
      exact R.symm_apply_apply (x i)
    rwa [he] at h
  · exact shapeHessianNondegenerate_rotateConfiguration_forward m lam R x hx hdet

theorem weightedPosition_similarity_data (m : MassVector) (R : Plane ≃ₗᵢ[ℝ] Plane)
    (x y : Configuration) (a : ℝ) (b : Plane) (heq : ∀ i, y i=b+a • R (x i)) :
    weightedPosition m y=totalMass m • b+a • R (weightedPosition m x) := by
  simp only [weightedPosition,heq,smul_add,Finset.sum_add_distrib,totalMass,Finset.sum_smul,
    map_sum,map_smul,Finset.smul_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  rw [smul_smul,smul_smul,mul_comm]

/-- The normalization removes translation and positive scaling from an
actual similarity. The remaining freedom is exactly its SO(2) rotation. -/
theorem normalizedCC_orientedSimilar_iff_rotation (m : MassVector) (hm : PositiveMasses m)
    (x y : Configuration) (hx : NormalizedCentralConfiguration m x)
    (hy : NormalizedCentralConfiguration m y) :
    OrientedSimilar x y ↔ ∃ R : Plane ≃ₗᵢ[ℝ] Plane,
      LinearMap.det R.toLinearEquiv.toLinearMap=1 ∧ y=rotateConfiguration R x := by
  constructor
  · rintro ⟨b,a,R,ha,hdet,heq⟩
    have hb : b=0 := by
      have h := weightedPosition_similarity_data m R x y a b heq
      rw [hx.2.1,hy.2.1,map_zero,smul_zero,add_zero] at h
      exact (smul_eq_zero.mp h.symm).resolve_left (ne_of_gt (totalMass_pos m hm))
    have heq' : y=positiveAffineConfiguration a 0 (rotateConfiguration R x) := by
      funext i
      simpa only [hb,zero_add,positiveAffineConfiguration,rotateConfiguration,sub_zero] using heq i
    have hz : rotateConfiguration R x≠0 := by
      intro hz
      apply collisionFree_ne_zero x hx.1
      funext i
      have h := congrFun hz i
      exact R.injective (by simpa only [rotateConfiguration,Pi.zero_apply,map_zero] using h)
    have hsmul : a⁻¹^2 • rotateConfiguration R x=a • rotateConfiguration R x := by
      funext i
      have h := hy.2.2 i
      rw [heq',positiveAffineConfiguration_acceleration m a 0 (rotateConfiguration R x) ha
        (collisionFree_rotateConfiguration R x hx.1) i,acceleration_rotateConfiguration,hx.2.2 i,
        map_neg] at h
      simpa only [positiveAffineConfiguration,sub_zero,smul_neg,neg_inj,Pi.smul_apply,rotateConfiguration] using h
    have hs := smul_left_injective ℝ hz hsmul
    have hcube : a^3=1 := by
      field_simp [ha.ne'] at hs
      nlinarith
    have haone := (pow_eq_one_iff_of_nonneg ha.le (by decide : (3 : ℕ)≠0)).mp hcube
    refine ⟨R,hdet,?_⟩
    funext i
    simpa only [hb,haone,one_smul,zero_add,rotateConfiguration] using heq i
  · rintro ⟨R,hdet,rfl⟩
    exact ⟨0,1,R,by norm_num,hdet,fun i => by simp [rotateConfiguration]⟩

/-- A normalized chart's uniqueness up to actual rotations proves
uniqueness of the original geometric central configurations up to the
paper's label-preserving oriented similarity. -/
theorem geometric_oriented_uniqueness_of_normalized (m : MassVector) (hm : PositiveMasses m)
    (σ : HullOrder)
    (huniq : ∀ x y, NormalizedCentralConfiguration m x → StrictConvexInOrder σ x →
      NormalizedCentralConfiguration m y → StrictConvexInOrder σ y →
      ∃ R : Plane ≃ₗᵢ[ℝ] Plane, LinearMap.det R.toLinearEquiv.toLinearMap=1 ∧
        y=rotateConfiguration R x) :
    ∀ x y, StrictConvexCentralConfiguration m σ x → StrictConvexCentralConfiguration m σ y →
      OrientedSimilar x y := by
  intro x y hx hy
  obtain ⟨x',hx',hc',hxx'⟩ := strictConvexCC_has_normalized_representative m hm σ x hx
  obtain ⟨y',hy',hd',hyy'⟩ := strictConvexCC_has_normalized_representative m hm σ y hy
  have hsimilar := (normalizedCC_orientedSimilar_iff_rotation m hm x' y' hx' hy').mpr
    (huniq x' y' hx' hc' hy' hd')
  exact orientedSimilar_trans hxx' (orientedSimilar_trans hsimilar (orientedSimilar_symm hyy'))

theorem plane_ext_of_inner_det (u v w : Plane) (hu : u≠0)
    (hi : inner ℝ u v=inner ℝ u w) (hd : det2 u v=det2 u w) : v=w := by
  rw [plane_inner_coordinates,plane_inner_coordinates] at hi
  unfold det2 at hd
  have hp : 0<u 0^2+u 1^2 := by
    have h := real_inner_self_pos.mpr hu
    rw [plane_inner_coordinates] at h
    nlinarith
  have h0 : (u 0^2+u 1^2)*(v 0-w 0)=0 := by
    linear_combination u 0*hi-u 1*hd
  have h1 : (u 0^2+u 1^2)*(v 1-w 1)=0 := by
    linear_combination u 1*hi+u 0*hd
  ext i
  fin_cases i
  · exact sub_eq_zero.mp ((mul_eq_zero.mp h0).resolve_left hp.ne')
  · exact sub_eq_zero.mp ((mul_eq_zero.mp h1).resolve_left hp.ne')

theorem linearIsometryEquiv_eq_refl_of_fixed_nonzero (R : Plane ≃ₗᵢ[ℝ] Plane)
    (hdet : LinearMap.det R.toLinearEquiv.toLinearMap=1)
    (u : Plane) (hu : u≠0) (hfix : R u=u) : R=LinearIsometryEquiv.refl ℝ Plane := by
  apply LinearIsometryEquiv.ext
  intro w
  apply plane_ext_of_inner_det u (R w) w hu
  · calc
      inner ℝ u (R w)=inner ℝ (R u) (R w) := by rw [hfix]
      _=inner ℝ u w := R.inner_map_map u w
  · calc
      det2 u (R w)=det2 (R u) (R w) := by rw [hfix]
      _=det2 u w := by rw [det2_linearIsometryEquiv,hdet,one_mul]

def FirstSatelliteGauge (x : Configuration) : Prop :=
  0<satellitesRelative x 0 0 ∧ satellitesRelative x 0 1=0

theorem point_norm_nonneg (r : ℝ) (hr : 0≤r) : ‖point r 0‖=r := by
  have he : point r 0=polarPoint r 0 := by simp [polarPoint]
  rw [he,polarPoint_norm,abs_of_nonneg hr]

local instance plane_dim_two : Fact (Module.finrank ℝ Plane=2) := ⟨by simp [Plane]⟩

def planeOrientation : Orientation ℝ Plane (Fin 2) :=
  (EuclideanSpace.basisFun (Fin 2) ℝ).toBasis.orientation

def firstSatelliteRotation (x : Configuration) : Plane ≃ₗᵢ[ℝ] Plane :=
  planeOrientation.rotation (planeOrientation.oangle (satellitesRelative x 0)
    (point ‖satellitesRelative x 0‖ 0))

theorem firstSatelliteRotation_det (x : Configuration) :
    LinearMap.det (firstSatelliteRotation x).toLinearEquiv.toLinearMap=1 :=
  planeOrientation.det_rotation _

theorem firstSatelliteRotation_anchor (x : Configuration) :
    firstSatelliteRotation x (satellitesRelative x 0)=point ‖satellitesRelative x 0‖ 0 := by
  apply (planeOrientation.rotation_oangle_eq_iff_norm_eq _ _).mpr
  rw [point_norm_nonneg _ (norm_nonneg _)]

theorem firstSatelliteGauge_rotation (x : Configuration) (hx : CollisionFree x) :
    FirstSatelliteGauge (rotateConfiguration (firstSatelliteRotation x) x) := by
  have hu : satellitesRelative x 0≠0 := by
    apply sub_ne_zero.mpr
    exact hx 1 0 (by decide)
  have he : satellitesRelative (rotateConfiguration (firstSatelliteRotation x) x) 0=
      firstSatelliteRotation x (satellitesRelative x 0) := by
    simp only [satellitesRelative,primaryRelative,rotateConfiguration,map_sub]
  rw [FirstSatelliteGauge,he,firstSatelliteRotation_anchor]
  constructor
  · exact norm_pos_iff.mpr hu
  · rfl

/-- Two multiplier-one representatives with the same positive first
satellite axis in one oriented similarity class coincide literally. -/
theorem normalized_gauged_orientedSimilar_eq (m : MassVector) (hm : PositiveMasses m)
    (x y : Configuration) (hx : NormalizedCentralConfiguration m x)
    (hy : NormalizedCentralConfiguration m y) (hgx : FirstSatelliteGauge x)
    (hgy : FirstSatelliteGauge y) (hxy : OrientedSimilar x y) : x=y := by
  obtain ⟨R,hdet,he⟩ := (normalizedCC_orientedSimilar_iff_rotation m hm x y hx hy).mp hxy
  have hrel : satellitesRelative y 0=R (satellitesRelative x 0) := by
    rw [he]
    simp only [satellitesRelative,primaryRelative,rotateConfiguration,map_sub]
  have hqx : satellitesRelative x 0=point (satellitesRelative x 0 0) 0 := by
    ext i
    fin_cases i
    · rfl
    · exact hgx.2
  have hqy : satellitesRelative y 0=point (satellitesRelative y 0 0) 0 := by
    ext i
    fin_cases i
    · rfl
    · exact hgy.2
  have hr : satellitesRelative y 0 0=satellitesRelative x 0 0 := by
    have h := congrArg norm hrel
    rw [R.norm_map,hqx,hqy,point_norm_nonneg _ hgx.1.le,point_norm_nonneg _ hgy.1.le] at h
    exact h
  have hfix : R (satellitesRelative x 0)=satellitesRelative x 0 := by
    rw [←hrel,hqy,hr,←hqx]
  have hnonzero : satellitesRelative x 0≠0 := by
    intro hz
    have h := congrArg (fun v : Plane => v 0) hz
    have hp := hgx.1
    change satellitesRelative x 0 0=0 at h
    linarith
  have hR := linearIsometryEquiv_eq_refl_of_fixed_nonzero R hdet _ hnonzero hfix
  rw [hR] at he
  exact he.symm

/-- Every original strictly convex CC has exactly one centered,
multiplier-one representative with positive first satellite axis. -/
theorem strictConvexCC_existsUnique_normalized_gauged (m : MassVector) (hm : PositiveMasses m)
    (σ : HullOrder) (x : Configuration) (hx : StrictConvexCentralConfiguration m σ x) :
    ∃! y, NormalizedCentralConfiguration m y ∧ FirstSatelliteGauge y ∧
      StrictConvexInOrder σ y ∧ OrientedSimilar x y := by
  obtain ⟨z,hz,hconv,hxz⟩ := strictConvexCC_has_normalized_representative m hm σ x hx
  let R := firstSatelliteRotation z
  let y := rotateConfiguration R z
  have hdet := firstSatelliteRotation_det z
  have hy := normalizedCC_rotateConfiguration m R z hz
  have hg := firstSatelliteGauge_rotation z hz.1
  have hc := (strictConvex_rotateConfiguration_iff σ R z hdet).mpr hconv
  have hzy : OrientedSimilar z y := ⟨0,1,R,by norm_num,hdet,fun i => by simp [y,rotateConfiguration]⟩
  refine ⟨y,⟨hy,hg,hc,orientedSimilar_trans hxz hzy⟩,?_⟩
  intro w hw
  exact normalized_gauged_orientedSimilar_eq m hm w y hw.1 hy hw.2.1 hg
    (orientedSimilar_trans (orientedSimilar_symm hw.2.2.2) (orientedSimilar_trans hxz hzy))

/-- Literal uniqueness in the fixed first-angle slice suffices for the
original label-preserving oriented similarity conclusion. -/
theorem geometric_oriented_uniqueness_of_gauged_normalized (m : MassVector)
    (hm : PositiveMasses m) (σ : HullOrder)
    (huniq : ∀ x y, NormalizedCentralConfiguration m x → FirstSatelliteGauge x →
      StrictConvexInOrder σ x → NormalizedCentralConfiguration m y → FirstSatelliteGauge y →
      StrictConvexInOrder σ y → x=y) :
    ∀ x y, StrictConvexCentralConfiguration m σ x → StrictConvexCentralConfiguration m σ y →
      OrientedSimilar x y := by
  intro x y hx hy
  obtain ⟨x',hx',_⟩ := strictConvexCC_existsUnique_normalized_gauged m hm σ x hx
  obtain ⟨y',hy',_⟩ := strictConvexCC_existsUnique_normalized_gauged m hm σ y hy
  have he := huniq x' y' hx'.1 hx'.2.1 hx'.2.2.1 hy'.1 hy'.2.1 hy'.2.2.1
  exact orientedSimilar_trans hx'.2.2.2 (he.symm ▸ orientedSimilar_symm hy'.2.2.2)

/-- The true six-dimensional Hessian in the fixed-angle normalized
slice transports back to every original geometric central configuration. -/
theorem geometric_nondegeneracy_of_gauged_normalized (m : MassVector)
    (hm : PositiveMasses m) (σ : HullOrder)
    (hall : ∀ y, NormalizedCentralConfiguration m y → FirstSatelliteGauge y →
      StrictConvexInOrder σ y → ShapeHessianNondegenerate m 1 y) :
    ∀ x, StrictConvexCentralConfiguration m σ x → NondegenerateCentralConfiguration m x := by
  intro x hx
  obtain ⟨hcollision,lam,hlam,hroot⟩ := hx.1
  let a := Real.rpow lam (1/3)
  have ha : 0<a := Real.rpow_pos_of_pos hlam _
  have hscale : a^3=lam := by
    simpa [a,one_div] using Real.rpow_inv_natCast_pow hlam.le (by decide : (3 : ℕ)≠0)
  let z := positiveAffineConfiguration a (massCenter m x) x
  have hz := normalizedCC_of_positiveAffine_multiplier m x hcollision lam a ha hscale
    (ne_of_gt (totalMass_pos m hm)) hroot
  have hc := (strictConvex_positiveAffineConfiguration_iff σ a (massCenter m x) x ha).mpr hx.2
  let R := firstSatelliteRotation z
  have hdet := firstSatelliteRotation_det z
  have hn := hall (rotateConfiguration R z) (normalizedCC_rotateConfiguration m R z hz)
    (firstSatelliteGauge_rotation z hz.1) ((strictConvex_rotateConfiguration_iff σ R z hdet).mpr hc)
  have hnz := (shapeHessianNondegenerate_rotateConfiguration_iff m 1 R z hz.1 hdet).mp hn
  exact nondegenerateCC_of_normalized_positiveAffine m hm x hcollision lam a hlam ha hscale hroot hnz

end DominantFiveBody




