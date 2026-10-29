import DominantFiveBody.CollisionTripleOriginalAngular

/-! # Original group proof of the complete triple cubic lower bound -/
noncomputable section
open scoped BigOperators ContDiff
open Filter Set Topology
namespace DominantFiveBody
set_option maxHeartbeats 1800000

theorem normalized_complete_lower_triple_original_group_zero_cube_impossible
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
    (center : Plane) (htriple : CompleteLimitingSatelliteTriple qLimit 3 center)
    (hnu : Tendsto (fun n => (mu n 0+mu n 1+mu n 2)/
      tripleLowDiameter (satellitesRelative (x n))^3) atTop (𝓝 0)) : False := by
  obtain ⟨phi,z,hphi,hzt,_,hdiff⟩ := lower_triple_scaled_positions_compact_subsequence
    (fun n => satellitesRelative (x n)) (fun n => satellitesRelative_collisionFree _ (hx n).1)
  have hkill (a b : TripleLabel) (hz : z a.castSucc≠z b.castSucc) : False :=
    normalized_complete_lower_triple_original_angular_scaled_zero_cube_impossible
      (eps ∘ phi) (mu ∘ phi) (x ∘ phi) (fun n => heps (phi n)) (hepst.comp hphi.tendsto_atTop)
      (fun n => hm (phi n)) (fun n => hx (phi n)) (fun n => hconv (phi n))
      (r ∘ phi) (theta ∘ phi) (fun n => hr (phi n)) (fun n => hpolar (phi n)) (fun n => horder (phi n))
      muLimit (hmt.comp hphi.tendsto_atTop) qLimit (hqt.comp hphi.tendsto_atTop)
      theta0 (htt.comp hphi.tendsto_atTop) center htriple z hzt (hnu.comp hphi.tendsto_atTop) a b hz
  rcases hdiff with h01|h02|h12
  · exact hkill 0 1 h01
  · exact hkill 0 2 h02
  · exact hkill 1 2 h12

theorem real_eventually_positive_lower_of_no_zero_subsequence
    (f : ℕ → ℝ) (hf : ∀ n,0≤f n)
    (havoid : ∀ phi : ℕ → ℕ,StrictMono phi → ¬ Tendsto (f ∘ phi) atTop (𝓝 0)) :
    ∃ k : ℝ,0<k ∧ ∀ᶠ n in atTop,k≤f n := by
  by_contra hbad
  have hzero : MapClusterPt (0 : ℝ) atTop f := by
    rw [mapClusterPt_iff_frequently]
    intro S hS
    obtain ⟨eta,heta,hball⟩ := Metric.mem_nhds_iff.mp hS
    have hfreq : ∃ᶠ n in atTop,f n<eta := by
      by_contra hn
      have hb : ∀ᶠ n in atTop,eta≤f n := by simpa only [not_lt] using not_frequently.mp hn
      exact hbad ⟨eta,heta,hb⟩
    apply hfreq.mono
    intro n hn
    apply hball
    simpa only [Metric.mem_ball,Real.dist_eq,sub_zero,abs_of_nonneg (hf n)] using hn
  obtain ⟨phi,hphi,hlim⟩ := hzero.tendsto_subseq
  exact havoid phi hphi hlim

theorem normalized_complete_lower_triple_original_group_mass_lower
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
    (center : Plane) (htriple : CompleteLimitingSatelliteTriple qLimit 3 center) :
    ∃ k : ℝ,0<k ∧ ∀ᶠ n in atTop,k≤(mu n 0+mu n 1+mu n 2)/
      tripleLowDiameter (satellitesRelative (x n))^3 := by
  apply real_eventually_positive_lower_of_no_zero_subsequence
  · intro n
    exact div_nonneg (by linarith [(hm n).1 0,(hm n).1 1,(hm n).1 2])
      (pow_nonneg (le_of_lt (tripleLowDiameter_pos _ (satellitesRelative_collisionFree _ (hx n).1))) _)
  · intro phi hphi hzero
    exact normalized_complete_lower_triple_original_group_zero_cube_impossible
      (eps ∘ phi) (mu ∘ phi) (x ∘ phi) (fun n => heps (phi n)) (hepst.comp hphi.tendsto_atTop)
      (fun n => hm (phi n)) (fun n => hx (phi n)) (fun n => hconv (phi n))
      (r ∘ phi) (theta ∘ phi) (fun n => hr (phi n)) (fun n => hpolar (phi n)) (fun n => horder (phi n))
      muLimit (hmt.comp hphi.tendsto_atTop) qLimit (hqt.comp hphi.tendsto_atTop)
      theta0 (htt.comp hphi.tendsto_atTop) center htriple hzero

end DominantFiveBody
