import DominantFiveBody.PairConvexity
import DominantFiveBody.PairZeroEndpoint
import DominantFiveBody.PairHessian

/-! # Complete-pair local physical continuation on independent parameters

The neighborhood properties are proved from actual area factors and
physical row recovery.  This local theorem still has to be connected to
the classification of arbitrary physical sequences.
-/

noncomputable section
open scoped BigOperators ContDiff
open Filter Set Topology

namespace DominantFiveBody
open Coorbital

def pairChartConfiguration (q : PairChartParameters) (y : PairChartVariables) : Configuration :=
  centeredFromRelative (q 0) (pairChartMass (q 1) (q 2) (q 3)) (pairChartPoints (q 1) (q 3) y)

def pairPhysicalSafeSet (sigma : HullOrder) : Set PairJointVariables :=
  {v | (∀ i, 0<pairChartRadii (v.1 1) (v.1 3) v.2 i) ∧
    (∀ i j, |pairChartAngles (v.1 1) (v.1 3) v.2 j-pairChartAngles (v.1 1) (v.1 3) v.2 i|<Real.pi) ∧
    (0<v.1 1 → StrictConvexInOrder sigma (liftRelative (pairChartPoints (v.1 1) (v.1 3) v.2)))}

theorem pairChartPositiveRadii_isOpen : IsOpen {v : PairJointVariables |
    ∀ i, 0<pairChartRadii (v.1 1) (v.1 3) v.2 i} := by
  simp only [Set.ofPred_forall]
  apply isOpen_iInter_of_finite
  intro i
  exact isOpen_lt continuous_const (pairChartRadii_joint_contDiff 0 i).continuous

theorem pairPhysicalSafeSet_boundary_interior (p alpha psi z : ℝ)
    (hz : 0<z) (hpsi0 : psi≠0) (hpsih : psi≠h) (hspan : twoSourceSpan psi<Real.pi) :
    ((![0,0,p,alpha] : PairChartParameters),pairUnitPoint h psi z) ∈
      interior (pairPhysicalSafeSet (pairBoundaryHullOrder psi)) := by
  have hsep := probe_separations_lt_pi hspan
  have hhpi : |h|<Real.pi := by rw [abs_of_pos (by unfold h; positivity)]; unfold h; linarith [Real.pi_pos]
  have hr : ∀ᶠ v : PairJointVariables in 𝓝 ((![0,0,p,alpha] : PairChartParameters),pairUnitPoint h psi z),
      ∀ i, 0<pairChartRadii (v.1 1) (v.1 3) v.2 i :=
    pairChartPositiveRadii_isOpen.mem_nhds (by
      intro i
      change 0<pairChartRadii 0 alpha (pairUnitPoint h psi z) i
      rw [pairUnitPoint_radii]
      norm_num)
  have hw : ∀ᶠ v : PairJointVariables in 𝓝 ((![0,0,p,alpha] : PairChartParameters),pairUnitPoint h psi z),
      ∀ i j, |pairChartAngles (v.1 1) (v.1 3) v.2 j-pairChartAngles (v.1 1) (v.1 3) v.2 i|<Real.pi :=
    pairChartWidth_isOpen.mem_nhds (pairChartWidth_at_unit_boundary alpha h psi z hhpi hsep.1 hsep.2)
  have hc := pairChart_boundary_strictConvex_neighborhood p alpha psi z hz hpsi0 hpsih hspan
  apply mem_interior_iff_mem_nhds.mpr
  filter_upwards [hr,hw,hc] with v hr hw hc
  exact ⟨hr,hw,hc⟩

theorem pairChart_regular_root_physical (q : PairChartParameters) (keepD : Bool)
    (y : PairChartVariables) (sigma : HullOrder)
    (heps : 0<q 0) (ht : 0<q 1) (hm : PositiveRatio (pairChartMass (q 1) (q 2) (q 3)))
    (hreg : PairChartRegular (q 0) (q 1) (q 3) y) (hsafe : (q,y) ∈ pairPhysicalSafeSet sigma)
    (hroot : pairChartParameterRows keepD q y=0)
    (hJ : (pairChartJacobian (q 0) (q 1) (q 2) (q 3) keepD y).IsInvertible) :
    StrictConvexCentralConfiguration (masses (q 0) (pairChartMass (q 1) (q 2) (q 3))) sigma
      (pairChartConfiguration q y) ∧
    NondegenerateCentralConfiguration (masses (q 0) (pairChartMass (q 1) (q 2) (q 3)))
      (pairChartConfiguration q y) := by
  have hx := (pairChartExtendedRows_zero_iff_normalized (q 0) (q 1) (q 2) (q 3) keepD y
    heps ht hm hreg hsafe.1).mp hroot
  have hnd := (pairChartJacobian_isInvertible_iff_shape (q 0) (q 1) (q 2) (q 3) keepD y
    heps ht hm hreg hsafe.1 hroot).mp hJ
  have hconv := (strictConvex_centeredFromRelative_iff sigma (q 0) (pairChartMass (q 1) (q 2) (q 3))
    (pairChartPoints (q 1) (q 3) y)).mpr (hsafe.2.2 ht)
  refine ⟨⟨normalized_is_central _ _ hx,hconv⟩,hx.1,1,by norm_num,?_,?_,hnd⟩
  · intro i
    simpa [pairChartConfiguration,massCenter,hx.2.1] using hx.2.2 i
  · exact finrank_shapeSpace _ (masses_positive _ _ heps hm) _ hx.1

/-- §5.2 local chart theorem with actual convexity and the physical
six-dimensional Hessian.  η,r,C are common for every α∈[0,1]. -/
theorem pairChart_compact_physical_continuation (p psi : ℝ) (keepD : Bool)
    (hp : 0≤p) (hp1 : p≤1) (hkeep : if keepD then 0<p else p<1)
    (hpsi0 : psi≠0) (hpsih : psi≠h) (hspan : twoSourceSpan psi<Real.pi)
    (hroot : p*coorbitalKernel psi+(1-p)*coorbitalKernel (psi-h)=0)
    (tau : ℝ) (htau : 0<tau) :
    let y0 := pairUnitPoint h psi (pairBoundaryScale (pairProbeDerivative p h psi))
    ∃ eta r C : ℝ, 0<eta ∧ 0<r ∧ 0<C ∧ r≤tau ∧ eta≤r ∧
      ∀ alpha ∈ Icc (0 : ℝ) 1, ∃ branch : PairChartParameters → PairChartVariables,
        branch ![0,0,p,alpha]=y0 ∧
        ContDiffOn ℝ ∞ branch (Metric.ball ![0,0,p,alpha] eta) ∧
        ∀ q, dist q ![0,0,p,alpha]<eta →
          dist (branch q) y0<r/2 ∧ PairChartRegular (q 0) (q 1) (q 3) (branch q) ∧
          (q,branch q) ∈ pairPhysicalSafeSet (pairBoundaryHullOrder psi) ∧
          (pairChartJacobian (q 0) (q 1) (q 2) (q 3) keepD (branch q)).IsInvertible ∧
          ‖(pairChartJacobian (q 0) (q 1) (q 2) (q 3) keepD (branch q)).inverse‖≤C ∧
          pairChartParameterRows keepD q (branch q)=0 ∧
          (∀ y, dist y y0<r → (pairChartParameterRows keepD q y=0 ↔ branch q=y)) ∧
          (0<q 0 → 0<q 1 → PositiveRatio (pairChartMass (q 1) (q 2) (q 3)) →
            StrictConvexCentralConfiguration (masses (q 0) (pairChartMass (q 1) (q 2) (q 3)))
              (pairBoundaryHullOrder psi) (pairChartConfiguration q (branch q)) ∧
            NondegenerateCentralConfiguration (masses (q 0) (pairChartMass (q 1) (q 2) (q 3)))
              (pairChartConfiguration q (branch q))) := by
  let z0 := pairBoundaryScale (pairProbeDerivative p h psi)
  let y0 := pairUnitPoint h psi z0
  let domain : Set PairJointVariables := {v | PairChartRegular (v.1 0) (v.1 1) (v.1 3) v.2} ∩
    interior (pairPhysicalSafeSet (pairBoundaryHullOrder psi))
  let K : Set PairJointVariables := (fun a : ℝ => ((![0,0,p,a] : PairChartParameters),y0)) '' Icc 0 1
  have hD : 0<pairProbeDerivative p h psi :=
    twoSourceProbe hp (by linarith) (by ring) hpsi0 hpsih hspan hroot
  have hz : 0<z0 := pairBoundaryScale_pos _ hD
  have hscale : pairProbeDerivative p h psi*z0^3=1 := pairBoundaryScale_equation _ hD
  have hhpos : 0<h := by unfold h; positivity
  have hhpi : |h|<Real.pi := by rw [abs_of_pos hhpos]; unfold h; linarith [Real.pi_pos]
  have hsep := probe_separations_lt_pi hspan
  have hK : IsCompact K := isCompact_Icc.image (by fun_prop)
  have hdata : ∀ a ∈ K, a ∈ domain ∧ pairChartParameterRows keepD a.1 a.2=0 ∧
      (CompactImplicit.jacobian (pairChartParameterRows keepD) a.1 a.2).IsInvertible := by
    rintro a ⟨alpha,_,rfl⟩
    refine ⟨⟨?_,?_⟩,?_,?_⟩
    · exact pairUnitPoint_regular alpha h psi z0 hz hhpos.ne' hhpi hpsi0 hpsih hsep.1 hsep.2
    · exact pairPhysicalSafeSet_boundary_interior p alpha psi z0 hz hpsi0 hpsih hspan
    · exact pairChartExtendedRows_unit_root p alpha psi z0 keepD hz hpsi0 hpsih hsep.1 hsep.2 hroot hscale
    · exact pairChartJacobian_boundary_isInvertible p alpha psi z0 keepD hp hp1 hkeep hz hpsi0 hpsih hspan hroot hscale
  obtain ⟨eta,r,C,heta,hr,hC,hrt,her,hbranch⟩ :=
    CompactImplicit.compact_product (pairChartParameterRows keepD) domain K
      (pairChartRegular_isOpen.inter isOpen_interior)
      ((pairChartExtendedRows_joint_contDiffOn ∞ keepD).mono (fun _ hv => hv.1)) hK hdata tau htau
  refine ⟨eta,r,C,heta,hr,hC,hrt,her,?_⟩
  intro alpha halpha
  obtain ⟨branch,hbase,hsmooth,hbranch⟩ :=
    hbranch ((![0,0,p,alpha] : PairChartParameters),y0) ⟨alpha,halpha,rfl⟩
  refine ⟨branch,hbase,hsmooth,?_⟩
  intro q hq
  obtain ⟨hd,hdom,hJ,hinv,hrootq,huniq⟩ := hbranch q hq
  have hsafe := interior_subset hdom.2
  refine ⟨hd,hdom.1,hsafe,hJ,hinv,hrootq,huniq,?_⟩
  intro heps ht hm
  exact pairChart_regular_root_physical q keepD (branch q) (pairBoundaryHullOrder psi)
    heps ht hm hdom.1 hsafe hrootq hJ

end DominantFiveBody
