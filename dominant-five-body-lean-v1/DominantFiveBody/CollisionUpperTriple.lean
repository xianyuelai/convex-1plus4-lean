import DominantFiveBody.CollisionReflection
import DominantFiveBody.CollisionTripleInitialScale
import DominantFiveBody.CollisionTripleWidth

/-! Actual upper endpoint triples inherit the proved lower endpoint estimates.
The reflected equations keep all current positive masses. -/

noncomputable section
open scoped BigOperators
open Filter Set Topology
namespace DominantFiveBody

def tripleHighDiameter (q : SatelliteConfiguration) : ℝ :=
  max ‖q 3-q 2‖ (max ‖q 3-q 1‖ ‖q 2-q 1‖)

theorem tripleLowDiameter_mirror (x : Configuration) :
    tripleLowDiameter (satellitesRelative (mirrorConfiguration x))=
      tripleHighDiameter (satellitesRelative x) := by
  simp only [tripleLowDiameter,tripleHighDiameter,mirrorConfiguration_relative,←map_sub,
    planeReflection.norm_map]
  change max ‖satellitesRelative x 2-satellitesRelative x 3‖
    (max ‖satellitesRelative x 1-satellitesRelative x 3‖ ‖satellitesRelative x 1-satellitesRelative x 2‖)=_
  rw [norm_sub_rev (satellitesRelative x 2),norm_sub_rev (satellitesRelative x 1),
    norm_sub_rev (satellitesRelative x 1)]

theorem normalized_complete_upper_triple_initial_scales
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
    (c : Plane) (htriple : CompleteLimitingSatelliteTriple qLimit 0 c) :
    ∃ K C : ℝ,0<K ∧ 0<C ∧ ∀ᶠ n in atTop,
      (∀ i j : TripleLabel,|r n j.succ-r n i.succ|≤K*(theta n 3-theta n 1)) ∧
      tripleHighDiameter (satellitesRelative (x n))≤(K+2)*(theta n 3-theta n 1) ∧
      (mu n 1+mu n 2+mu n 3)/tripleHighDiameter (satellitesRelative (x n))^3≤C*mu n 0 := by
  have hmt' : Tendsto (fun n => mu n ∘ Fin.revPerm) atTop (𝓝 (muLimit ∘ Fin.revPerm)) := by
    apply tendsto_pi_nhds.mpr
    intro i
    exact (continuous_apply i.rev).continuousAt.tendsto.comp hmt
  have htt' : Tendsto (fun n i => -theta n (Fin.rev i)) atTop (𝓝 (fun i => -theta0 (Fin.rev i))) := by
    apply tendsto_pi_nhds.mpr
    intro i
    exact ((continuous_apply i.rev).continuousAt.tendsto.comp htt).neg
  obtain ⟨K,C,hK,hC,hbound⟩ := normalized_complete_lower_triple_initial_scales eps
    (fun n => mu n ∘ Fin.revPerm) (fun n => mirrorConfiguration (x n)) heps hepst
    (fun n => positiveRatio_satellitePermutation _ (hm n) Fin.revPerm)
    (fun n => mirrorConfiguration_normalized _ _ _ (hx n))
    (fun n => mirrorConfiguration_strictConvex _ (hconv n))
    (fun n => r n ∘ Fin.revPerm) (fun n i => -theta n (Fin.rev i))
    (fun n i => hr n i.rev) (fun n => mirrorConfiguration_polar _ _ _ (hpolar n))
    (fun n => mirrorAngles_ordered _ (horder n))
    (muLimit ∘ Fin.revPerm) hmt' (fun i => planeReflection (qLimit (Fin.rev i)))
    (mirrorConfiguration_relative_limit x qLimit hqt) (fun i => -theta0 (Fin.rev i)) htt'
    (planeReflection c) (complete_upper_triple_mirror qLimit c htriple)
  refine ⟨K,C,hK,hC,?_⟩
  filter_upwards [hbound] with n hn
  have hdiam := hn.2.1
  have hmass := hn.2.2
  simp only [tripleLowDiameter_mirror,neg_sub_neg] at hdiam hmass
  refine ⟨?_,hdiam,?_⟩
  · intro i j
    have hh := hn.1 i.rev j.rev
    have hi : Fin.rev (i.rev.castSucc : Satellite)=i.succ := by fin_cases i <;> rfl
    have hj : Fin.rev (j.rev.castSucc : Satellite)=j.succ := by fin_cases j <;> rfl
    simpa only [Function.comp_apply,Fin.revPerm_apply,hi,hj,neg_sub_neg,
      show Fin.rev (0 : Satellite)=3 from rfl,show Fin.rev (2 : Satellite)=1 from rfl] using hh
  · convert hmass using 1 <;> dsimp [Function.comp_apply,Fin.revPerm]
    ring

theorem normalized_complete_upper_triple_regular_geometry
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
    (c : Plane) (htriple : CompleteLimitingSatelliteTriple qLimit 0 c)
    (eta : ℝ) (heta : 0<eta)
    (hcomparable : ∀ᶠ n in atTop,∀ i j : TripleLabel,i≠j →
      eta*tripleHighDiameter (satellitesRelative (x n))≤satelliteDistance (satellitesRelative (x n)) i.succ j.succ) :
    (∀ i j : TripleLabel,Tendsto (fun n => (r n j.succ-r n i.succ)/
      tripleHighDiameter (satellitesRelative (x n))) atTop (𝓝 0)) ∧
    Tendsto (fun n => (theta n 3-theta n 1)/tripleHighDiameter (satellitesRelative (x n))) atTop (𝓝 1) := by
  have hrev (i : TripleLabel) : (i.castSucc : Satellite).rev=i.rev.succ := by fin_cases i <;> rfl
  have hmt' : Tendsto (fun n => mu n ∘ Fin.revPerm) atTop (𝓝 (muLimit ∘ Fin.revPerm)) := by
    apply tendsto_pi_nhds.mpr
    intro i
    exact (continuous_apply i.rev).continuousAt.tendsto.comp hmt
  have htt' : Tendsto (fun n i => -theta n (Fin.rev i)) atTop (𝓝 (fun i => -theta0 (Fin.rev i))) := by
    apply tendsto_pi_nhds.mpr
    intro i
    exact ((continuous_apply i.rev).continuousAt.tendsto.comp htt).neg
  have hcomp' : ∀ᶠ n in atTop,∀ i j : TripleLabel,i≠j →
      eta*tripleLowDiameter (satellitesRelative (mirrorConfiguration (x n)))≤
        satelliteDistance (satellitesRelative (mirrorConfiguration (x n))) i.castSucc j.castSucc := by
    filter_upwards [hcomparable] with n hn
    intro i j hij
    rw [tripleLowDiameter_mirror,mirrorConfiguration_pairDistance,hrev,hrev]
    exact hn i.rev j.rev (Fin.rev_injective.ne hij)
  have hrad := normalized_complete_lower_triple_regular_radial_limits eps
    (fun n => mu n ∘ Fin.revPerm) (fun n => mirrorConfiguration (x n)) heps hepst
    (fun n => positiveRatio_satellitePermutation _ (hm n) Fin.revPerm)
    (fun n => mirrorConfiguration_normalized _ _ _ (hx n))
    (fun n => mirrorConfiguration_strictConvex _ (hconv n))
    (fun n => r n ∘ Fin.revPerm) (fun n i => -theta n (Fin.rev i))
    (fun n i => hr n i.rev) (fun n => mirrorConfiguration_polar _ _ _ (hpolar n))
    (fun n => mirrorAngles_ordered _ (horder n)) (muLimit ∘ Fin.revPerm) hmt'
    (fun i => planeReflection (qLimit (Fin.rev i))) (mirrorConfiguration_relative_limit x qLimit hqt)
    (fun i => -theta0 (Fin.rev i)) htt' (planeReflection c)
    (complete_upper_triple_mirror qLimit c htriple) eta heta hcomp'
  have hwidth := normalized_complete_lower_triple_regular_width_limit eps
    (fun n => mu n ∘ Fin.revPerm) (fun n => mirrorConfiguration (x n)) heps hepst
    (fun n => positiveRatio_satellitePermutation _ (hm n) Fin.revPerm)
    (fun n => mirrorConfiguration_normalized _ _ _ (hx n))
    (fun n => mirrorConfiguration_strictConvex _ (hconv n))
    (fun n => r n ∘ Fin.revPerm) (fun n i => -theta n (Fin.rev i))
    (fun n i => hr n i.rev) (fun n => mirrorConfiguration_polar _ _ _ (hpolar n))
    (fun n => mirrorAngles_ordered _ (horder n)) (muLimit ∘ Fin.revPerm) hmt'
    (fun i => planeReflection (qLimit (Fin.rev i))) (mirrorConfiguration_relative_limit x qLimit hqt)
    (fun i => -theta0 (Fin.rev i)) htt' (planeReflection c)
    (complete_upper_triple_mirror qLimit c htriple) eta heta hcomp'
  constructor
  · intro i j
    simpa only [tripleLowDiameter_mirror,Function.comp_apply,Fin.revPerm_apply,hrev,Fin.rev_rev] using hrad i.rev j.rev
  · simpa only [tripleLowDiameter_mirror,neg_sub_neg,
      show Fin.rev (0 : Satellite)=3 from rfl,show Fin.rev (2 : Satellite)=1 from rfl] using hwidth

end DominantFiveBody
