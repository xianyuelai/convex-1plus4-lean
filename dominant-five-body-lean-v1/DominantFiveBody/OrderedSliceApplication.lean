import DominantFiveBody.OrderedPhysicalSequence
import DominantFiveBody.PolarSliceCoordinates
import DominantFiveBody.SliceConnection

/-! The ordered slice is faithful to the original geometric theorem.
Uniformity for this one slice transports to every original hull order;
the transport does not add label permutations to oriented similarity. -/

noncomputable section
open scoped BigOperators ContDiff
open Filter Set Topology
namespace DominantFiveBody
set_option maxHeartbeats 600000

theorem orderedSliceRoot_of_normalized_gauged (mu : PositiveMassRatio) (eps : ℝ)
    (heps : 0<eps) (x : Configuration)
    (hx : NormalizedCentralConfiguration (masses eps mu.val) x)
    (hg : FirstSatelliteGauge x) (hc : StrictConvexInOrder standardHullOrder x) :
    ∃ y,orderedSliceRoot mu eps y ∧ slicePhysicalConfiguration (eps,mu.val) y=x := by
  obtain ⟨r,theta,hr,hzero,horder,hpolar⟩ := strictConvex_gauged_ordered_polar x hc hx.1 hg
  let y := polarSlice r theta
  have hcf := satellitesRelative_collisionFree x hx.1
  rw [hpolar] at hcf
  have hphys : slicePhysicalConfiguration (eps,mu.val) y=x := by
    rw [polarSlice_physical_eq _ _ _ _ hzero,←hpolar]
    exact centeredFromRelative_satellitesRelative eps mu.val mu.property.2 (by linarith) x hx.2.1
  have hrows := polarResiduals_zero_of_normalized eps mu.val x hx mu.property heps r theta hr hpolar
  refine ⟨y,⟨polarSlice_regular eps mu.val r theta (by linarith) hr hzero hcf,?_,?_,
    polarSlice_residual_zero eps mu.val r theta hzero hrows.1 hrows.2⟩,hphys⟩
  · simpa only [y,polarSlice_angles _ _ hzero,OrderedSemicircle] using horder
  · rw [hphys]
    exact hc

theorem orderedSliceRoot_physical (mu : PositiveMassRatio) (eps : ℝ) (heps : 0<eps)
    (y : SliceCoordinates) (hy : orderedSliceRoot mu eps y) :
    NormalizedCentralConfiguration (masses eps mu.val) (slicePhysicalConfiguration (eps,mu.val) y) ∧
      FirstSatelliteGauge (slicePhysicalConfiguration (eps,mu.val) y) ∧
      StrictConvexInOrder standardHullOrder (slicePhysicalConfiguration (eps,mu.val) y) := by
  refine ⟨normalizedCC_of_reducedResidual_zero _ y hy.1 heps mu.property hy.2.2.2,?_,hy.2.2.1⟩
  rw [FirstSatelliteGauge,slicePhysicalConfiguration_satellitesRelative]
  simpa only [sliceSatellites,polarSatellites,sliceAngles,Fin.cases_zero,polarPoint,
    Real.cos_zero,Real.sin_zero,mul_one,mul_zero,point,Matrix.cons_val_zero,Matrix.cons_val_one,
    Matrix.cons_val_fin_one] using And.intro (hy.1.2.1 0) (rfl : (0 : ℝ)=0)

theorem orderedSlice_fixedParameterLocalExistence : FixedParameterLocalExistence orderedSliceRoot := by
  intro mu
  obtain ⟨d,hd,hroots⟩ := normalized_physical_local_existence_all_orders mu.val mu.property standardHullOrder
  refine ⟨d,hd,?_⟩
  intro eps heps hed
  obtain ⟨x,hx,hc,_⟩ := hroots eps heps hed
  obtain ⟨y,hy,_⟩ := orderedSliceRoot_of_normalized_gauged mu eps heps
    (rotateConfiguration (firstSatelliteRotation x) x)
    (normalizedCC_rotateConfiguration _ _ _ hx) (firstSatelliteGauge_rotation x hx.1)
    ((strictConvex_rotateConfiguration_iff _ _ _ (firstSatelliteRotation_det x)).mpr hc)
  exact ⟨y,hy⟩

theorem orientedSimilar_reindex_iff (x y : Configuration) (e : Equiv.Perm Label) :
    OrientedSimilar (x ∘ e) (y ∘ e) ↔ OrientedSimilar x y := by
  constructor
  · rintro ⟨b,a,R,ha,hR,h⟩
    exact ⟨b,a,R,ha,hR,fun i => by simpa only [Function.comp_apply,Equiv.apply_symm_apply] using h (e.symm i)⟩
  · rintro ⟨b,a,R,ha,hR,h⟩
    exact ⟨b,a,R,ha,hR,fun i => h (e i)⟩

theorem orderedGaugeConfiguration_orientedSimilar (sigma : HullOrder) (x : Configuration) :
    OrientedSimilar (x ∘ sigma.labels) (orderedGaugeConfiguration sigma x) := by
  refine ⟨0,1,firstSatelliteRotation (x ∘ sigma.labels),by norm_num,
    firstSatelliteRotation_det _,?_⟩
  intro i
  simp only [orderedGaugeConfiguration,rotateConfiguration,one_smul,zero_add]

theorem orderedSlice_uniqueness_to_geometric (mu : PositiveMassRatio) (eps : ℝ)
    (heps : 0<eps) (sigma : HullOrder)
    (huniq : ∀ y z,orderedSliceRoot
      ⟨mu.val ∘ hullSatellitePermutation sigma,positiveRatio_hull_reindex _ sigma mu.property⟩ eps y →
      orderedSliceRoot ⟨mu.val ∘ hullSatellitePermutation sigma,positiveRatio_hull_reindex _ sigma mu.property⟩ eps z →
      y=z) :
    ∀ x y,StrictConvexCentralConfiguration (masses eps mu.val) sigma x →
      StrictConvexCentralConfiguration (masses eps mu.val) sigma y → OrientedSimilar x y := by
  intro x y hx hy
  have hm := masses_positive eps mu.val heps mu.property
  obtain ⟨x',hx',hcx,hxx'⟩ := strictConvexCC_has_normalized_representative _ hm sigma x hx
  obtain ⟨y',hy',hcy,hyy'⟩ := strictConvexCC_has_normalized_representative _ hm sigma y hy
  let nu : PositiveMassRatio := ⟨mu.val ∘ hullSatellitePermutation sigma,positiveRatio_hull_reindex _ sigma mu.property⟩
  obtain ⟨u,hu,huX⟩ := orderedSliceRoot_of_normalized_gauged nu eps heps
    (orderedGaugeConfiguration sigma x')
    (orderedGaugeConfiguration_normalized eps mu.val sigma x' hx')
    (orderedGaugeConfiguration_gauge sigma x' hx'.1) (orderedGaugeConfiguration_convex sigma x' hcx)
  obtain ⟨v,hv,hvY⟩ := orderedSliceRoot_of_normalized_gauged nu eps heps
    (orderedGaugeConfiguration sigma y')
    (orderedGaugeConfiguration_normalized eps mu.val sigma y' hy')
    (orderedGaugeConfiguration_gauge sigma y' hy'.1) (orderedGaugeConfiguration_convex sigma y' hcy)
  have he : orderedGaugeConfiguration sigma x'=orderedGaugeConfiguration sigma y' := by
    rw [←huX,←hvY,huniq u v hu hv]
  have hs : OrientedSimilar (x' ∘ sigma.labels) (y' ∘ sigma.labels) :=
    orientedSimilar_trans (orderedGaugeConfiguration_orientedSimilar sigma x')
      (he.symm ▸ orientedSimilar_symm (orderedGaugeConfiguration_orientedSimilar sigma y'))
  exact orientedSimilar_trans hxx'
    (orientedSimilar_trans ((orientedSimilar_reindex_iff x' y' sigma.labels).mp hs) (orientedSimilar_symm hyy'))

theorem orderedSlice_nondegeneracy_to_geometric (mu : PositiveMassRatio) (eps : ℝ)
    (heps : 0<eps) (sigma : HullOrder)
    (hnd : ∀ y,orderedSliceRoot
      ⟨mu.val ∘ hullSatellitePermutation sigma,positiveRatio_hull_reindex _ sigma mu.property⟩ eps y →
      orderedSliceNondegenerate
        ⟨mu.val ∘ hullSatellitePermutation sigma,positiveRatio_hull_reindex _ sigma mu.property⟩ eps y) :
    ∀ x,StrictConvexCentralConfiguration (masses eps mu.val) sigma x →
      NondegenerateCentralConfiguration (masses eps mu.val) x := by
  apply geometric_nondegeneracy_of_gauged_normalized _ (masses_positive eps mu.val heps mu.property) sigma
  intro x hx _ hc
  let nu : PositiveMassRatio := ⟨mu.val ∘ hullSatellitePermutation sigma,positiveRatio_hull_reindex _ sigma mu.property⟩
  obtain ⟨y,hy,he⟩ := orderedSliceRoot_of_normalized_gauged nu eps heps
    (orderedGaugeConfiguration sigma x)
    (orderedGaugeConfiguration_normalized eps mu.val sigma x hx)
    (orderedGaugeConfiguration_gauge sigma x hx.1) (orderedGaugeConfiguration_convex sigma x hc)
  have hn := hnd y hy
  change ShapeHessianNondegenerate (masses eps nu.val) 1 (slicePhysicalConfiguration (eps,nu.val) y) at hn
  rw [he] at hn
  have hxperm := normalized_reindex _ x hx sigma.labels
  rw [←masses_hull_reindex] at hxperm
  have hnperm := (shapeHessianNondegenerate_rotateConfiguration_iff (masses eps nu.val) 1
    (firstSatelliteRotation (x ∘ sigma.labels)) (x ∘ sigma.labels) hxperm.1
    (firstSatelliteRotation_det _)).mp hn
  rw [masses_hull_reindex] at hnperm
  exact (shapeHessianNondegenerate_permutation_iff _ x hx sigma.labels).mp hnperm

theorem main_of_orderedSlice_uniform
    (h : ∃ d : ℝ,0<d ∧ ∀ mu eps,0<eps → eps<d →
      (∃! y,orderedSliceRoot mu eps y) ∧
      (∀ y,orderedSliceRoot mu eps y → orderedSliceNondegenerate mu eps y)) :
    MainUniformStatement := by
  obtain ⟨d,hd,hall⟩ := h
  refine ⟨d,hd,?_⟩
  intro mu hm eps heps hed sigma
  let nu : PositiveMassRatio := ⟨mu ∘ hullSatellitePermutation sigma,positiveRatio_hull_reindex mu sigma hm⟩
  obtain ⟨hex,hnd⟩ := hall nu eps heps hed
  obtain ⟨y,hy,huniq⟩ := hex
  have hp := orderedSliceRoot_physical nu eps heps y hy
  let x := slicePhysicalConfiguration (eps,nu.val) y ∘ sigma.labels.symm
  have hmass : masses eps nu.val ∘ sigma.labels.symm=masses eps mu := masses_hull_pullback eps mu sigma
  have hx : NormalizedCentralConfiguration (masses eps mu) x := by
    have ht := normalizedCC_permutation _ _ hp.1 sigma.labels.symm
    rw [hmass] at ht
    exact ht
  have hc : StrictConvexInOrder sigma x := strictConvex_hull_pullback sigma _ hp.2.2
  have hs : StrictConvexCentralConfiguration (masses eps mu) sigma x := ⟨normalized_is_central _ _ hx,hc⟩
  refine ⟨x,hs,?_,?_⟩
  · intro z hz
    exact orderedSlice_uniqueness_to_geometric ⟨mu,hm⟩ eps heps sigma
      (fun u v hu hv => (huniq u hu).trans (huniq v hv).symm) x z hs hz
  · exact orderedSlice_nondegeneracy_to_geometric ⟨mu,hm⟩ eps heps sigma hnd

/-- Only the actual four-type sequence capture remains as input here.
The other Section 7 interfaces and the geometric translation are proved. -/
theorem main_of_orderedSlice_connection
    (hconnection : ConnectionProperty orderedSliceRoot orderedSliceNondegenerate orderedSliceEndpoint) :
    MainUniformStatement :=
  main_of_orderedSlice_uniform (main_of_chart_facts orderedSlice_fixedParameterLocalExistence
    orderedSlice_localContinuationUniqueness hconnection)

end DominantFiveBody
