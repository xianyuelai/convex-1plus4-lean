import DominantFiveBody.OrderedSliceTripleCases
import DominantFiveBody.CollisionTripleNestedMacro

/-! Proposition 4.3 for arbitrary complete lower triples.
The regular/nested split is an extraction from actual distances; its
consequences are promoted back to the entire original sequence.
-/

noncomputable section
open scoped BigOperators ContDiff
open Filter Set Topology
namespace DominantFiveBody
set_option maxHeartbeats 1200000

theorem real_tendsto_of_every_subsequence (f : ℕ → ℝ) (z : ℝ)
    (h : ∀ phi : ℕ → ℕ,StrictMono phi → ∃ psi : ℕ → ℕ,StrictMono psi ∧
      Tendsto (f ∘ phi ∘ psi) atTop (𝓝 z)) : Tendsto f atTop (𝓝 z) := by
  apply Metric.tendsto_atTop.mpr
  intro eta heta
  by_contra hbad
  push Not at hbad
  obtain ⟨phi,hphi,hfar⟩ := Nat.exists_strictMono_subsequence
    (P := fun n => eta≤dist (f n) z) (by
      intro N
      obtain ⟨n,hn,hbadn⟩ := hbad (N+1)
      exact ⟨n,by omega,hbadn⟩)
  obtain ⟨psi,hpsi,ht⟩ := h phi hphi
  have hs : ∀ᶠ n in atTop,dist (f (phi (psi n))) z<eta :=
    ht.eventually (Metric.ball_mem_nhds z heta)
  obtain ⟨n,hn⟩ := hs.exists
  exact (not_lt_of_ge (hfar (psi n))) hn

theorem normalized_complete_lower_triple_geometry_subsequence
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
    ∃ phi : ℕ → ℕ,StrictMono phi ∧
      (∀ i j : TripleLabel,Tendsto (fun n => (r (phi n) j.castSucc-r (phi n) i.castSucc)/
        tripleLowDiameter (satellitesRelative (x (phi n)))) atTop (𝓝 0)) ∧
      Tendsto (fun n => (theta (phi n) 2-theta (phi n) 0)/
        tripleLowDiameter (satellitesRelative (x (phi n)))) atTop (𝓝 1) ∧
      ∃ k : ℝ,0<k ∧ ∀ᶠ n in atTop,k≤(mu (phi n) 0+mu (phi n) 1+mu (phi n) 2)/
        tripleLowDiameter (satellitesRelative (x (phi n)))^3 := by
  obtain ⟨phi,hphi,hnested|⟨eta,heta,hcomp⟩⟩ := low_triple_scale_cases
    (fun n => satellitesRelative (x n)) (fun n => satellitesRelative_collisionFree _ (hx n).1)
  · obtain ⟨a,b,c,hab,hca,hcb,hpair⟩ := hnested
    have hrad := normalized_complete_lower_triple_nested_radial_limits (eps ∘ phi) (mu ∘ phi) (x ∘ phi)
      (fun n => heps (phi n)) (hepst.comp hphi.tendsto_atTop) (fun n => hm (phi n))
      (fun n => hx (phi n)) (fun n => hconv (phi n)) (r ∘ phi) (theta ∘ phi)
      (fun n => hr (phi n)) (fun n => hpolar (phi n)) (fun n => horder (phi n))
      muLimit (hmt.comp hphi.tendsto_atTop) qLimit (hqt.comp hphi.tendsto_atTop)
      theta0 (htt.comp hphi.tendsto_atTop) center htriple a b c hab.ne hca hcb hpair
    have hwidth := normalized_complete_lower_triple_nested_width_limit (eps ∘ phi) (mu ∘ phi) (x ∘ phi)
      (fun n => heps (phi n)) (hepst.comp hphi.tendsto_atTop) (fun n => hm (phi n))
      (fun n => hx (phi n)) (fun n => hconv (phi n)) (r ∘ phi) (theta ∘ phi)
      (fun n => hr (phi n)) (fun n => hpolar (phi n)) (fun n => horder (phi n))
      muLimit (hmt.comp hphi.tendsto_atTop) qLimit (hqt.comp hphi.tendsto_atTop)
      theta0 (htt.comp hphi.tendsto_atTop) center htriple a b c hab.ne hca hcb hpair
    have hmass := normalized_complete_lower_triple_nested_macro_mass_cube_limit
      (eps ∘ phi) (mu ∘ phi) (x ∘ phi)
      (fun n => heps (phi n)) (hepst.comp hphi.tendsto_atTop) (fun n => hm (phi n))
      (fun n => hx (phi n)) (fun n => hconv (phi n)) (r ∘ phi) (theta ∘ phi)
      (fun n => hr (phi n)) (fun n => hpolar (phi n)) (fun n => horder (phi n))
      muLimit (hmt.comp hphi.tendsto_atTop) qLimit (hqt.comp hphi.tendsto_atTop)
      theta0 (htt.comp hphi.tendsto_atTop) center htriple a b c hab hca hcb hpair
    refine ⟨phi,hphi,hrad,hwidth,1,by norm_num,?_⟩
    exact (hmass.eventually (Ioi_mem_nhds (by norm_num : (1 : ℝ)<9/4))).mono (fun _ hn => hn.le)
  · have hcomp' := Eventually.of_forall (f := atTop) hcomp
    have hrad := normalized_complete_lower_triple_regular_radial_limits (eps ∘ phi) (mu ∘ phi) (x ∘ phi)
      (fun n => heps (phi n)) (hepst.comp hphi.tendsto_atTop) (fun n => hm (phi n))
      (fun n => hx (phi n)) (fun n => hconv (phi n)) (r ∘ phi) (theta ∘ phi)
      (fun n => hr (phi n)) (fun n => hpolar (phi n)) (fun n => horder (phi n))
      muLimit (hmt.comp hphi.tendsto_atTop) qLimit (hqt.comp hphi.tendsto_atTop)
      theta0 (htt.comp hphi.tendsto_atTop) center htriple eta heta hcomp'
    have hwidth := normalized_complete_lower_triple_regular_width_limit (eps ∘ phi) (mu ∘ phi) (x ∘ phi)
      (fun n => heps (phi n)) (hepst.comp hphi.tendsto_atTop) (fun n => hm (phi n))
      (fun n => hx (phi n)) (fun n => hconv (phi n)) (r ∘ phi) (theta ∘ phi)
      (fun n => hr (phi n)) (fun n => hpolar (phi n)) (fun n => horder (phi n))
      muLimit (hmt.comp hphi.tendsto_atTop) qLimit (hqt.comp hphi.tendsto_atTop)
      theta0 (htt.comp hphi.tendsto_atTop) center htriple eta heta hcomp'
    obtain ⟨k,hk,hbound⟩ := normalized_complete_lower_triple_regular_mass_lower
      (eps ∘ phi) (mu ∘ phi) (x ∘ phi)
      (fun n => heps (phi n)) (hepst.comp hphi.tendsto_atTop) (fun n => hm (phi n))
      (fun n => hx (phi n)) (fun n => hconv (phi n)) (r ∘ phi) (theta ∘ phi)
      (fun n => hr (phi n)) (fun n => hpolar (phi n)) (fun n => horder (phi n))
      muLimit (hmt.comp hphi.tendsto_atTop) qLimit (hqt.comp hphi.tendsto_atTop)
      theta0 (htt.comp hphi.tendsto_atTop) center htriple eta heta hcomp'
    exact ⟨phi,hphi,hrad,hwidth,k,hk,hbound⟩

theorem normalized_complete_lower_triple_geometry
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
    (∀ i j : TripleLabel,Tendsto (fun n => (r n j.castSucc-r n i.castSucc)/
      tripleLowDiameter (satellitesRelative (x n))) atTop (𝓝 0)) ∧
    Tendsto (fun n => (theta n 2-theta n 0)/
      tripleLowDiameter (satellitesRelative (x n))) atTop (𝓝 1) := by
  constructor
  · intro i j
    apply real_tendsto_of_every_subsequence
    intro phi hphi
    obtain ⟨psi,hpsi,hrad,_,_⟩ := normalized_complete_lower_triple_geometry_subsequence
      (eps ∘ phi) (mu ∘ phi) (x ∘ phi)
      (fun n => heps (phi n)) (hepst.comp hphi.tendsto_atTop) (fun n => hm (phi n))
      (fun n => hx (phi n)) (fun n => hconv (phi n)) (r ∘ phi) (theta ∘ phi)
      (fun n => hr (phi n)) (fun n => hpolar (phi n)) (fun n => horder (phi n))
      muLimit (hmt.comp hphi.tendsto_atTop) qLimit (hqt.comp hphi.tendsto_atTop)
      theta0 (htt.comp hphi.tendsto_atTop) center htriple
    exact ⟨psi,hpsi,hrad i j⟩
  · apply real_tendsto_of_every_subsequence
    intro phi hphi
    obtain ⟨psi,hpsi,_,hwidth,_⟩ := normalized_complete_lower_triple_geometry_subsequence
      (eps ∘ phi) (mu ∘ phi) (x ∘ phi)
      (fun n => heps (phi n)) (hepst.comp hphi.tendsto_atTop) (fun n => hm (phi n))
      (fun n => hx (phi n)) (fun n => hconv (phi n)) (r ∘ phi) (theta ∘ phi)
      (fun n => hr (phi n)) (fun n => hpolar (phi n)) (fun n => horder (phi n))
      muLimit (hmt.comp hphi.tendsto_atTop) qLimit (hqt.comp hphi.tendsto_atTop)
      theta0 (htt.comp hphi.tendsto_atTop) center htriple
    exact ⟨psi,hpsi,hwidth⟩

theorem real_eventually_lower_of_every_subsequence (f : ℕ → ℝ) (hf : ∀ n,0≤f n)
    (h : ∀ phi : ℕ → ℕ,StrictMono phi → ∃ psi : ℕ → ℕ,StrictMono psi ∧
      ∃ k : ℝ,0<k ∧ ∀ᶠ n in atTop,k≤f (phi (psi n))) :
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
  obtain ⟨psi,hpsi,k,hk,hbound⟩ := h phi hphi
  have hs : ∀ᶠ n in atTop,f (phi (psi n))<k :=
    (hlim.comp hpsi.tendsto_atTop).eventually (Iio_mem_nhds hk)
  obtain ⟨n,hn,hsmall⟩ := (hbound.and hs).exists
  exact (not_lt_of_ge hn) hsmall

theorem normalized_complete_lower_triple_mass_lower
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
  apply real_eventually_lower_of_every_subsequence
  · intro n
    exact div_nonneg (by linarith [(hm n).1 0,(hm n).1 1,(hm n).1 2])
      (pow_nonneg (le_of_lt (tripleLowDiameter_pos _ (satellitesRelative_collisionFree _ (hx n).1))) _)
  · intro phi hphi
    obtain ⟨psi,hpsi,_,_,k,hk,hbound⟩ := normalized_complete_lower_triple_geometry_subsequence
      (eps ∘ phi) (mu ∘ phi) (x ∘ phi)
      (fun n => heps (phi n)) (hepst.comp hphi.tendsto_atTop) (fun n => hm (phi n))
      (fun n => hx (phi n)) (fun n => hconv (phi n)) (r ∘ phi) (theta ∘ phi)
      (fun n => hr (phi n)) (fun n => hpolar (phi n)) (fun n => horder (phi n))
      muLimit (hmt.comp hphi.tendsto_atTop) qLimit (hqt.comp hphi.tendsto_atTop)
      theta0 (htt.comp hphi.tendsto_atTop) center htriple
    exact ⟨psi,hpsi,k,hk,hbound⟩

end DominantFiveBody
