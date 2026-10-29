import DominantFiveBody.CollisionUpperRectangleGeometry
import DominantFiveBody.CollisionNestedSegmentVectors

noncomputable section
open scoped BigOperators ContDiff
open Filter Set Topology
namespace DominantFiveBody
set_option maxHeartbeats 1800000

theorem planeReflection_quarterTurn (v : Plane) :
    planeReflection (quarterTurn v)= -quarterTurn (planeReflection v) := by
  ext i
  fin_cases i <;> simp [planeReflection,quarterTurn,point,PiLp.neg_apply]

theorem planeReflection_physicalPairSegmentPoint (qa qb : Plane) (t : ℝ) :
    planeReflection (physicalPairSegmentPoint qa qb t)=
      physicalPairSegmentPoint (planeReflection qa) (planeReflection qb) t := by
  simp only [physicalPairSegmentPoint,map_add,map_smul]

theorem physicalPairSegmentPoint_reverse (qa qb : Plane) (t : ℝ) :
    physicalPairSegmentPoint qb qa (1-t)=physicalPairSegmentPoint qa qb t := by
  unfold physicalPairSegmentPoint
  module

theorem normalized_complete_upper_triple_nested_segment_scaled_geometry_uniform
    (eps : ℕ → ℝ) (mu : ℕ → MassRatio) (x : ℕ → Configuration)
    (heps : ∀ n,0<eps n) (hepst : Tendsto eps atTop (𝓝 0))
    (hm : ∀ n,PositiveRatio (mu n))
    (hx : ∀ n,NormalizedCentralConfiguration (masses (eps n) (mu n)) (x n))
    (hconv : ∀ n,StrictConvexInOrder standardHullOrder (x n))
    (r theta : ℕ → Satellite → ℝ) (hr : ∀ n i,0<r n i)
    (hpolar : ∀ n,satellitesRelative (x n)=polarSatellites (r n) (theta n))
    (horder : ∀ n,OrderedSemicircle (theta n))
    (muLimit : MassRatio) (hmt : Tendsto mu atTop (𝓝 muLimit))
    (qLimit : SatelliteConfiguration)
    (hqt : Tendsto (fun n => satellitesRelative (x n)) atTop (𝓝 qLimit))
    (theta0 : Satellite → ℝ) (htt : Tendsto theta atTop (𝓝 theta0))
    (center : Plane) (htriple : CompleteLimitingSatelliteTriple qLimit 0 center)
    (a b c : TripleLabel) (hab : a<b) (hca : c≠a) (hcb : c≠b)
    (hpair : Tendsto (fun n => satelliteDistance (satellitesRelative (x n)) a.succ b.succ/
      tripleHighDiameter (satellitesRelative (x n))) atTop (𝓝 0)) :
    ∀ eta : ℝ,0<eta → ∀ᶠ n in atTop,∀ t∈Icc (0 : ℝ) 1,
      ‖(tripleHighDiameter (satellitesRelative (x n)))⁻¹ •
        (satellitesRelative (x n) c.succ-
          physicalPairSegmentPoint (satellitesRelative (x n) a.succ)
            (satellitesRelative (x n) b.succ) t)-
        (lowNestedOrientation a c) • quarterTurn (polarPoint 1 (theta0 3))‖<eta := by
  have hrev (i : TripleLabel) : (i.rev.castSucc : Satellite).rev=i.succ := by fin_cases i <;> rfl
  have hdist (n : ℕ) : satelliteDistance (satellitesRelative (mirrorConfiguration (x n))) b.rev.castSucc a.rev.castSucc=
      satelliteDistance (satellitesRelative (x n)) a.succ b.succ := by
    rw [mirrorConfiguration_pairDistance,hrev,hrev]
    exact norm_sub_rev _ _
  have hmt' : Tendsto (fun n => mu n ∘ Fin.revPerm) atTop (𝓝 (muLimit ∘ Fin.revPerm)) := by
    apply tendsto_pi_nhds.mpr
    intro i
    exact (continuous_apply i.rev).continuousAt.tendsto.comp hmt
  have htt' : Tendsto (fun n i => -theta n (Fin.rev i)) atTop (𝓝 (fun i => -theta0 (Fin.rev i))) := by
    apply tendsto_pi_nhds.mpr
    intro i
    exact ((continuous_apply i.rev).continuousAt.tendsto.comp htt).neg
  have hpair' : Tendsto (fun n => satelliteDistance (satellitesRelative (mirrorConfiguration (x n)))
      b.rev.castSucc a.rev.castSucc/tripleLowDiameter (satellitesRelative (mirrorConfiguration (x n))))
      atTop (𝓝 0) := by simpa only [hdist,tripleLowDiameter_mirror] using hpair
  have hlow := normalized_complete_lower_triple_nested_segment_scaled_geometry_uniform eps
    (fun n => mu n ∘ Fin.revPerm) (fun n => mirrorConfiguration (x n)) heps hepst
    (fun n => positiveRatio_satellitePermutation _ (hm n) Fin.revPerm)
    (fun n => mirrorConfiguration_normalized _ _ _ (hx n))
    (fun n => mirrorConfiguration_strictConvex _ (hconv n))
    (fun n => r n ∘ Fin.revPerm) (fun n i => -theta n (Fin.rev i))
    (fun n i => hr n i.rev) (fun n => mirrorConfiguration_polar _ _ _ (hpolar n))
    (fun n => mirrorAngles_ordered _ (horder n)) (muLimit ∘ Fin.revPerm) hmt'
    (fun i => planeReflection (qLimit (Fin.rev i))) (mirrorConfiguration_relative_limit x qLimit hqt)
    (fun i => -theta0 (Fin.rev i)) htt' (planeReflection center)
    (complete_upper_triple_mirror qLimit center htriple) b.rev a.rev c.rev
    (Fin.rev_lt_rev.mpr hab) (Fin.rev_injective.ne hcb) (Fin.rev_injective.ne hca) hpair'
  have hadj := (normalized_complete_upper_triple_nested_scale_complete eps mu x heps hepst hm hx
    hconv r theta hr hpolar horder muLimit hmt qLimit hqt theta0 htt center htriple a b c hab hca hcb hpair).1
  have homega : lowNestedOrientation b.rev c.rev= -lowNestedOrientation a c := by
    fin_cases a <;> fin_cases b <;> fin_cases c <;> simp_all [lowNestedOrientation]

  intro eta heta
  filter_upwards [hlow eta heta] with n hn
  intro t ht
  have ht' : 1-t∈Icc (0 : ℝ) 1 := ⟨by linarith [ht.2],by linarith [ht.1]⟩
  have hh := hn (1-t) ht'
  rw [tripleLowDiameter_mirror] at hh
  simp only [mirrorConfiguration_relative,hrev,Fin.rev_zero,
    homega] at hh
  rw [show (Fin.last 3 : Satellite)=(3 : Satellite) from rfl] at hh
  have he :
      (tripleHighDiameter (satellitesRelative (x n)))⁻¹ •
        (planeReflection (satellitesRelative (x n) c.succ)-
          physicalPairSegmentPoint (planeReflection (satellitesRelative (x n) b.succ))
            (planeReflection (satellitesRelative (x n) a.succ)) (1-t))-
        (-lowNestedOrientation a c) • quarterTurn (polarPoint 1 (-theta0 3)) =
      planeReflection ((tripleHighDiameter (satellitesRelative (x n)))⁻¹ •
        (satellitesRelative (x n) c.succ-
          physicalPairSegmentPoint (satellitesRelative (x n) a.succ)
            (satellitesRelative (x n) b.succ) t)-
        (lowNestedOrientation a c) • quarterTurn (polarPoint 1 (theta0 3))) := by
    rw [←planeReflection_physicalPairSegmentPoint,physicalPairSegmentPoint_reverse]
    simp only [map_sub,map_smul,planeReflection_quarterTurn,planeReflection_polar]
    module
  rw [he,planeReflection.norm_map] at hh
  exact hh

end DominantFiveBody
