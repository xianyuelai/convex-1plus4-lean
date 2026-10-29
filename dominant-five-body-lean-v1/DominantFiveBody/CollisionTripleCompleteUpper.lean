import DominantFiveBody.CollisionTripleComplete
import DominantFiveBody.CollisionUpperTriple

/-! Proposition 4.3 for arbitrary complete upper triples.
The corresponding lower theorem already promotes the extracted regimes
to the entire sequence. Reflection preserves the actual diameter.
-/

noncomputable section
open scoped BigOperators ContDiff
open Filter Set Topology
namespace DominantFiveBody
set_option maxHeartbeats 800000

theorem normalized_complete_upper_triple_complete_geometry
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
    (center : Plane) (htriple : CompleteLimitingSatelliteTriple qLimit 0 center) :
    (∀ i j : TripleLabel,Tendsto (fun n => (r n j.succ-r n i.succ)/
      tripleHighDiameter (satellitesRelative (x n))) atTop (𝓝 0)) ∧
    Tendsto (fun n => (theta n 3-theta n 1)/tripleHighDiameter (satellitesRelative (x n)))
      atTop (𝓝 1) ∧
    ∃ k : ℝ,0<k ∧ ∀ᶠ n in atTop,k≤(mu n 1+mu n 2+mu n 3)/
      tripleHighDiameter (satellitesRelative (x n))^3 := by
  have hrev (i : TripleLabel) : (i.castSucc : Satellite).rev=i.rev.succ := by fin_cases i <;> rfl
  have hmt' : Tendsto (fun n => mu n ∘ Fin.revPerm) atTop (𝓝 (muLimit ∘ Fin.revPerm)) := by
    apply tendsto_pi_nhds.mpr
    intro i
    exact (continuous_apply i.rev).continuousAt.tendsto.comp hmt
  have htt' : Tendsto (fun n i => -theta n (Fin.rev i)) atTop (𝓝 (fun i => -theta0 (Fin.rev i))) := by
    apply tendsto_pi_nhds.mpr
    intro i
    exact ((continuous_apply i.rev).continuousAt.tendsto.comp htt).neg
  obtain ⟨hrad,hwidth⟩ := normalized_complete_lower_triple_geometry eps
    (fun n => mu n ∘ Fin.revPerm) (fun n => mirrorConfiguration (x n)) heps hepst
    (fun n => positiveRatio_satellitePermutation _ (hm n) Fin.revPerm)
    (fun n => mirrorConfiguration_normalized _ _ _ (hx n))
    (fun n => mirrorConfiguration_strictConvex _ (hconv n))
    (fun n => r n ∘ Fin.revPerm) (fun n i => -theta n (Fin.rev i))
    (fun n i => hr n i.rev) (fun n => mirrorConfiguration_polar _ _ _ (hpolar n))
    (fun n => mirrorAngles_ordered _ (horder n)) (muLimit ∘ Fin.revPerm) hmt'
    (fun i => planeReflection (qLimit (Fin.rev i))) (mirrorConfiguration_relative_limit x qLimit hqt)
    (fun i => -theta0 (Fin.rev i)) htt' (planeReflection center)
    (complete_upper_triple_mirror qLimit center htriple)
  obtain ⟨k,hk,hbound⟩ := normalized_complete_lower_triple_mass_lower eps
    (fun n => mu n ∘ Fin.revPerm) (fun n => mirrorConfiguration (x n)) heps hepst
    (fun n => positiveRatio_satellitePermutation _ (hm n) Fin.revPerm)
    (fun n => mirrorConfiguration_normalized _ _ _ (hx n))
    (fun n => mirrorConfiguration_strictConvex _ (hconv n))
    (fun n => r n ∘ Fin.revPerm) (fun n i => -theta n (Fin.rev i))
    (fun n i => hr n i.rev) (fun n => mirrorConfiguration_polar _ _ _ (hpolar n))
    (fun n => mirrorAngles_ordered _ (horder n)) (muLimit ∘ Fin.revPerm) hmt'
    (fun i => planeReflection (qLimit (Fin.rev i))) (mirrorConfiguration_relative_limit x qLimit hqt)
    (fun i => -theta0 (Fin.rev i)) htt' (planeReflection center)
    (complete_upper_triple_mirror qLimit center htriple)
  refine ⟨?_,?_,k,hk,?_⟩
  · intro i j
    simpa only [tripleLowDiameter_mirror,Function.comp_apply,Fin.revPerm_apply,hrev,Fin.rev_rev]
      using hrad i.rev j.rev
  · simpa only [tripleLowDiameter_mirror,neg_sub_neg,
      show Fin.rev (0 : Satellite)=3 from rfl,show Fin.rev (2 : Satellite)=1 from rfl] using hwidth
  · filter_upwards [hbound] with n hn
    rw [tripleLowDiameter_mirror] at hn
    convert! hn using 1
    simp only [Function.comp_apply,Fin.revPerm_apply]
    congr 1
    change mu n 1+mu n 2+mu n 3=mu n 3+mu n 2+mu n 1
    ring

end DominantFiveBody
