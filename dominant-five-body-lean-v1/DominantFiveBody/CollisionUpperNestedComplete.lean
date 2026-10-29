import DominantFiveBody.CollisionTripleNestedComplete
import DominantFiveBody.CollisionUpperTriple

/-! # Actual upper nested rates by reflection and reversal of labels -/

noncomputable section
open scoped BigOperators ContDiff
open Filter Set Topology
namespace DominantFiveBody
set_option maxHeartbeats 1200000

theorem normalized_complete_upper_triple_nested_scale_complete
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
    b.val=a.val+1 ∧
    Tendsto (fun n => (mu n a.succ+mu n b.succ)/(mu n 1+mu n 2+mu n 3)) atTop (𝓝 0) ∧
    Tendsto (fun n => (mu n 1+mu n 2+mu n 3)/tripleHighDiameter (satellitesRelative (x n))^3)
      atTop (𝓝 (9/4 : ℝ)) ∧
    Tendsto (fun n => (mu n a.succ+mu n b.succ)/
      satelliteDistance (satellitesRelative (x n)) a.succ b.succ^3) atTop (𝓝 (27/4 : ℝ)) ∧
    Tendsto (fun n => (theta n b.succ-theta n a.succ)/
      satelliteDistance (satellitesRelative (x n)) a.succ b.succ) atTop (𝓝 1) ∧
    ∃ C : ℝ,0<C ∧ ∀ᶠ n in atTop,|r n b.succ-r n a.succ|≤
      C*eps n*satelliteDistance (satellitesRelative (x n)) a.succ b.succ := by
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
  have hlow := normalized_complete_lower_triple_nested_scale_complete eps
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
  have hsum (n : ℕ) : (mu n ∘ Fin.revPerm) 0+(mu n ∘ Fin.revPerm) 1+(mu n ∘ Fin.revPerm) 2=
      mu n 1+mu n 2+mu n 3 := by
    change mu n 3+mu n 2+mu n 1=mu n 1+mu n 2+mu n 3
    ring
  have hsumrev (n : ℕ) : mu n (Fin.rev 0)+mu n (Fin.rev 1)+mu n (Fin.rev 2)=
      mu n 1+mu n 2+mu n 3 := by
    change mu n 3+mu n 2+mu n 1=mu n 1+mu n 2+mu n 3
    ring
  have hadj : b.val=a.val+1 := by
    have hh := hlow.1
    simp only [Fin.val_rev] at hh
    have ha := a.isLt
    have hb := b.isLt
    omega
  refine ⟨hadj,?_,?_,?_,?_,?_⟩
  · simpa only [Function.comp_apply,Fin.revPerm_apply,hrev,hsumrev,add_comm] using hlow.2.1
  · simpa only [hsum,tripleLowDiameter_mirror] using hlow.2.2.1
  · simpa only [Function.comp_apply,Fin.revPerm_apply,hrev,add_comm,hdist] using hlow.2.2.2.1
  · simpa only [neg_sub_neg,hrev,hdist] using hlow.2.2.2.2.1
  · obtain ⟨C,hC,hbound⟩ := hlow.2.2.2.2.2
    refine ⟨C,hC,?_⟩
    simpa only [Function.comp_apply,Fin.revPerm_apply,hrev,hdist,abs_sub_comm] using hbound

end DominantFiveBody
