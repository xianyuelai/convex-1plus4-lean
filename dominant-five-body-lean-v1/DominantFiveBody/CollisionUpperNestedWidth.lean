import DominantFiveBody.CollisionUpperTriple
import DominantFiveBody.CollisionTripleNestedWidth

/-! # Actual upper nested-triple radial and width limits

Reflection reverses both labels and their current masses.  The small pair
is selected by its actual distance-to-diameter limit, without a limiting
mass-share hypothesis.
-/

noncomputable section
open scoped BigOperators
open Filter Set Topology
namespace DominantFiveBody

theorem normalized_complete_upper_triple_nested_geometry
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
    (a b c : TripleLabel) (hab : a≠b) (hca : c≠a) (hcb : c≠b)
    (hpair : Tendsto (fun n => satelliteDistance (satellitesRelative (x n)) a.succ b.succ/
      tripleHighDiameter (satellitesRelative (x n))) atTop (𝓝 0)) :
    (∀ i j : TripleLabel,Tendsto (fun n => (r n j.succ-r n i.succ)/
      tripleHighDiameter (satellitesRelative (x n))) atTop (𝓝 0)) ∧
    Tendsto (fun n => (theta n 3-theta n 1)/tripleHighDiameter (satellitesRelative (x n)))
      atTop (𝓝 1) := by
  have hrev (i : TripleLabel) : (i.rev.castSucc : Satellite).rev=i.succ := by
    fin_cases i <;> rfl
  have hmt' : Tendsto (fun n => mu n ∘ Fin.revPerm) atTop (𝓝 (muLimit ∘ Fin.revPerm)) := by
    apply tendsto_pi_nhds.mpr
    intro i
    exact (continuous_apply i.rev).continuousAt.tendsto.comp hmt
  have htt' : Tendsto (fun n i => -theta n (Fin.rev i)) atTop (𝓝 (fun i => -theta0 (Fin.rev i))) := by
    apply tendsto_pi_nhds.mpr
    intro i
    exact ((continuous_apply i.rev).continuousAt.tendsto.comp htt).neg
  have hpair' : Tendsto (fun n =>
      satelliteDistance (satellitesRelative (mirrorConfiguration (x n))) a.rev.castSucc b.rev.castSucc/
        tripleLowDiameter (satellitesRelative (mirrorConfiguration (x n)))) atTop (𝓝 0) := by
    simpa only [mirrorConfiguration_pairDistance,tripleLowDiameter_mirror,hrev] using hpair
  have hrad := normalized_complete_lower_triple_nested_radial_limits eps
    (fun n => mu n ∘ Fin.revPerm) (fun n => mirrorConfiguration (x n)) heps hepst
    (fun n => positiveRatio_satellitePermutation _ (hm n) Fin.revPerm)
    (fun n => mirrorConfiguration_normalized _ _ _ (hx n))
    (fun n => mirrorConfiguration_strictConvex _ (hconv n))
    (fun n => r n ∘ Fin.revPerm) (fun n i => -theta n (Fin.rev i))
    (fun n i => hr n i.rev) (fun n => mirrorConfiguration_polar _ _ _ (hpolar n))
    (fun n => mirrorAngles_ordered _ (horder n)) (muLimit ∘ Fin.revPerm) hmt'
    (fun i => planeReflection (qLimit (Fin.rev i))) (mirrorConfiguration_relative_limit x qLimit hqt)
    (fun i => -theta0 (Fin.rev i)) htt' (planeReflection center)
    (complete_upper_triple_mirror qLimit center htriple) a.rev b.rev c.rev
    (Fin.rev_injective.ne hab) (Fin.rev_injective.ne hca) (Fin.rev_injective.ne hcb) hpair'
  have hwidth := normalized_complete_lower_triple_nested_width_limit eps
    (fun n => mu n ∘ Fin.revPerm) (fun n => mirrorConfiguration (x n)) heps hepst
    (fun n => positiveRatio_satellitePermutation _ (hm n) Fin.revPerm)
    (fun n => mirrorConfiguration_normalized _ _ _ (hx n))
    (fun n => mirrorConfiguration_strictConvex _ (hconv n))
    (fun n => r n ∘ Fin.revPerm) (fun n i => -theta n (Fin.rev i))
    (fun n i => hr n i.rev) (fun n => mirrorConfiguration_polar _ _ _ (hpolar n))
    (fun n => mirrorAngles_ordered _ (horder n)) (muLimit ∘ Fin.revPerm) hmt'
    (fun i => planeReflection (qLimit (Fin.rev i))) (mirrorConfiguration_relative_limit x qLimit hqt)
    (fun i => -theta0 (Fin.rev i)) htt' (planeReflection center)
    (complete_upper_triple_mirror qLimit center htriple) a.rev b.rev c.rev
    (Fin.rev_injective.ne hab) (Fin.rev_injective.ne hca) (Fin.rev_injective.ne hcb) hpair'
  constructor
  · intro i j
    simpa only [tripleLowDiameter_mirror,Function.comp_apply,Fin.revPerm_apply,hrev] using hrad i.rev j.rev
  · simpa only [tripleLowDiameter_mirror,neg_sub_neg,
      show Fin.rev (0 : Satellite)=3 from rfl,show Fin.rev (2 : Satellite)=1 from rfl] using hwidth

end DominantFiveBody
