import DominantFiveBody.NestedConvexity
import DominantFiveBody.NestedCollinearity

/-! # Actual nested continuation with convexity and the physical Hessian

This theorem uses the proved zero-scale collinearity, not an area oracle.
Both scales and epsilon are independent; alpha varies about its anchor.
-/

noncomputable section
open scoped BigOperators Matrix ContDiff
open Filter Set Topology
namespace DominantFiveBody
open Coorbital
set_option maxHeartbeats 800000

def nestedChartConfiguration (q : NestedChartParameters) (y : NestedChartVariables) : Configuration :=
  centeredFromRelative (q 0) (nestedChartMass (q 1) (q 2) (q 3))
    (nestedChartPoints (q 1) (q 2) (q 3) y)

theorem nestedContinuationRoot_convex_physical (q : NestedChartParameters)
    (y : NestedChartVariables) (sigma : HullOrder)
    (hdomain : NestedContinuationDomain (q,y))
    (heps : 0<q 0) (ht : 0<q 1) (heta : 0<q 2)
    (hm : PositiveRatio (nestedChartMass (q 1) (q 2) (q 3)))
    (hroot : nestedChartParameterRows q y=0)
    (hJ : (nestedChartJacobian (q 0) (q 1) (q 2) (q 3) y).IsInvertible)
    (hconv : StrictConvexInOrder sigma (liftRelative (nestedChartPoints (q 1) (q 2) (q 3) y))) :
    StrictConvexCentralConfiguration (masses (q 0) (nestedChartMass (q 1) (q 2) (q 3))) sigma
      (nestedChartConfiguration q y) ∧
    NondegenerateCentralConfiguration (masses (q 0) (nestedChartMass (q 1) (q 2) (q 3)))
      (nestedChartConfiguration q y) := by
  obtain ⟨hx,hnd⟩ := nestedContinuationRoot_physical q y hdomain heps ht heta hm hroot hJ
  have hc := (strictConvex_centeredFromRelative_iff sigma (q 0)
    (nestedChartMass (q 1) (q 2) (q 3)) (nestedChartPoints (q 1) (q 2) (q 3) y)).mpr hconv
  refine ⟨⟨normalized_is_central _ _ hx,hc⟩,hx.1,1,by norm_num,?_,?_,hnd⟩
  · intro i
    simpa [nestedChartConfiguration,massCenter,hx.2.1] using hx.2.2 i
  · exact finrank_shapeSpace _ (masses_positive _ _ heps hm) _ hx.1

theorem nestedChart_convex_physical_continuation (alpha0 tau omega : ℝ)
    (halpha0 : alpha0∈Icc (0 : ℝ) 1) (htau : tau=1 ∨ tau=-1) (hw : omega=1 ∨ omega=-1)
    (bound : ℝ) (hbound : 0<bound) :
    ∃ delta r C : ℝ,0<delta ∧ 0<r ∧ 0<C ∧ r≤bound ∧ delta≤r ∧
      ∃ branch : NestedChartParameters → NestedChartVariables,
        branch (nestedParameter 0 0 0 alpha0)=nestedBasePoint (tau*h) omega ∧
        ContDiffOn ℝ ∞ branch (Metric.ball (nestedParameter 0 0 0 alpha0) delta) ∧
        ∀ q,dist q (nestedParameter 0 0 0 alpha0)<delta →
          dist (branch q) (nestedBasePoint (tau*h) omega)<r/2 ∧
          NestedContinuationDomain (q,branch q) ∧
          (nestedChartJacobian (q 0) (q 1) (q 2) (q 3) (branch q)).IsInvertible ∧
          ‖(nestedChartJacobian (q 0) (q 1) (q 2) (q 3) (branch q)).inverse‖≤C ∧
          nestedChartParameterRows q (branch q)=0 ∧
          (∀ y,dist y (nestedBasePoint (tau*h) omega)<r →
            (nestedChartParameterRows q y=0 ↔ branch q=y)) ∧
          (0<q 1 → 0<q 2 → q 3∈Icc (0 : ℝ) 1 →
            StrictConvexInOrder (nestedBoundaryHullOrder tau omega)
              (liftRelative (nestedChartPoints (q 1) (q 2) (q 3) (branch q)))) ∧
          (0<q 0 → 0<q 1 → 0<q 2 → q 3∈Icc (0 : ℝ) 1 →
            PositiveRatio (nestedChartMass (q 1) (q 2) (q 3)) →
            StrictConvexCentralConfiguration (masses (q 0) (nestedChartMass (q 1) (q 2) (q 3)))
              (nestedBoundaryHullOrder tau omega) (nestedChartConfiguration q (branch q)) ∧
            NondegenerateCentralConfiguration (masses (q 0) (nestedChartMass (q 1) (q 2) (q 3)))
              (nestedChartConfiguration q (branch q))) ∧
          (q 0=0 → 0<q 1 → 0<q 2 → PositiveRatio (nestedChartMass (q 1) (q 2) (q 3)) →
            (∀ i,nestedChartRadii (q 1) (q 2) (q 3) (branch q) i=1) ∧
            branch q 2=0 ∧ branch q 3=0 ∧
            RelativeCollisionFree (nestedChartPoints (q 1) (q 2) (q 3) (branch q)) ∧
            SeparatedSemicircle (nestedChartAngles (q 1) (q 2) (q 3) (branch q)) ∧
            ∀ i,coorbitalResidual (nestedChartMass (q 1) (q 2) (q 3))
              (nestedChartAngles (q 1) (q 2) (q 3) (branch q)) i=0) := by
  have hh : 0<h := by unfold h; positivity
  have hangle : |tau*h|=h := by rcases htau with rfl | rfl <;> simp [abs_of_pos hh]
  have hwabs : |omega|=1 := by rcases hw with rfl | rfl <;> norm_num
  obtain ⟨d,r,C,hd,hr,hC,hrbound,hdr,hbranches⟩ :=
    nestedChart_compact_boundary_continuation (tau*h) omega hangle hwabs bound hbound
  obtain ⟨branch,hbase,hsmooth,hdata⟩ := hbranches alpha0 halpha0
  obtain ⟨dZ,hdZ,hdZd,hzero⟩ := nestedChart_zero_face_area_zero_of_local_uniqueness
    alpha0 tau omega htau d r hd hr branch hbase hsmooth
    (fun q hq => (hdata q hq).2.1)
    (fun q hq => (hdata q hq).2.2.2.2.1)
    (fun q hq => (hdata q hq).2.2.2.2.2)
  obtain ⟨delta,hdelta,hdeltaZ,hconv⟩ := nestedChart_strictConvex_neighborhood_of_zero_face
    alpha0 tau omega dZ htau hw hdZ branch hbase
    (hsmooth.mono (Metric.ball_subset_ball hdZd))
    (fun q hq => (hdata q (lt_of_lt_of_le hq hdZd)).2.2.2.2.1)
    (fun q hq => (hdata q (lt_of_lt_of_le hq hdZd)).2.1.2.1) hzero
  have hdeltad : delta≤d := hdeltaZ.trans hdZd
  refine ⟨delta,r,C,hdelta,hr,hC,hrbound,hdeltad.trans hdr,branch,hbase,
    hsmooth.mono (Metric.ball_subset_ball hdeltad),?_⟩
  intro q hq
  obtain ⟨hdist,hdomain,hJ,hinv,hroot,huniq⟩ := hdata q (lt_of_lt_of_le hq hdeltad)
  have hparameter : nestedParameter (q 0) (q 1) (q 2) (q 3)=q := by
    funext i
    fin_cases i <;> rfl
  have hconvq (ht : 0<q 1) (heta : 0<q 2) (halpha : q 3∈Icc (0 : ℝ) 1) :
      StrictConvexInOrder (nestedBoundaryHullOrder tau omega)
        (liftRelative (nestedChartPoints (q 1) (q 2) (q 3) (branch q))) := by
    simpa only [hparameter] using hconv (q 0) (q 1) (q 2) (q 3)
      (by simpa only [hparameter] using hq) ht heta halpha
  refine ⟨hdist,hdomain,hJ,hinv,hroot,huniq,hconvq,?_,?_⟩
  · intro heps ht heta halpha hm
    exact nestedContinuationRoot_convex_physical q (branch q) _ hdomain heps ht heta hm hroot hJ
      (hconvq ht heta halpha)
  · intro heps ht heta hm
    have hd0 : NestedContinuationDomain ((![0,q 1,q 2,q 3] : NestedChartParameters),branch q) := by
      have heq : (![0,q 1,q 2,q 3] : NestedChartParameters)=q := by
        funext i
        fin_cases i
        · exact heps.symm
        · rfl
        · rfl
        · rfl
      rwa [heq]
    exact nestedContinuationRoot_fixed_mass_endpoint (q 1) (q 2) (q 3) (branch q) ht heta hm hd0
      (by simpa only [nestedChartParameterRows,heps] using hroot)

end DominantFiveBody
