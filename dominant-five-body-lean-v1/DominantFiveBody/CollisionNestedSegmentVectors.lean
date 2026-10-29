import DominantFiveBody.CollisionNestedSegmentGeometry

/-! # Signed scaled vector geometry throughout the actual smaller-pair segment -/
noncomputable section
open scoped BigOperators ContDiff
open Filter Set Topology
namespace DominantFiveBody
set_option maxHeartbeats 1500000

theorem physical_pair_segment_scaled_displacement_uniform
    (qa qb qc : ℕ → Plane) (d : ℕ → ℝ) (u : Plane) (hd : ∀ n,0<d n)
    (hnear : Tendsto (fun n => (d n)⁻¹ • (qc n-qa n)) atTop (𝓝 u))
    (hsmall : Tendsto (fun n => ‖qb n-qa n‖/d n) atTop (𝓝 0)) :
    ∀ eta : ℝ,0<eta → ∀ᶠ n in atTop,∀ t∈Icc (0 : ℝ) 1,
      ‖(d n)⁻¹ • (qc n-physicalPairSegmentPoint (qa n) (qb n) t)-u‖<eta := by
  have hB : Tendsto (fun n => (d n)⁻¹ • (qb n-qa n)) atTop (𝓝 0) := by
    apply tendsto_zero_iff_norm_tendsto_zero.mpr
    convert! hsmall using 1
    funext n
    rw [norm_smul,Real.norm_eq_abs,abs_inv,abs_of_pos (hd n)]
    ring
  let F : ℕ → ℝ → Plane := fun n t =>
    (d n)⁻¹ • (qc n-physicalPairSegmentPoint (qa n) (qb n) t)
  have hseq : ∀ t : ℕ → ℝ,(∀ n,t n∈Icc (0 : ℝ) 1) →
      Tendsto (fun n => F n (t n)) atTop (𝓝 u) := by
    intro t ht
    have hsm := bounded_segment_coefficient_small_smul t _ ht hB
    convert! hnear.sub hsm using 1
    · funext n;dsimp only [F];rw [physicalPairSegmentPoint_eq];module
    · simp
  have hU := limit_on_moving_sets_of_all_selections (fun _ => Icc (0 : ℝ) 1) (fun _ => (0 : ℝ))
    (fun _ => by norm_num) F u hseq
  simpa only [dist_eq_norm] using hU

theorem normalized_complete_lower_triple_nested_segment_scaled_geometry_uniform
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
    (a b c : TripleLabel) (hab : a<b) (hca : c≠a) (hcb : c≠b)
    (hpair : Tendsto (fun n => satelliteDistance (satellitesRelative (x n)) a.castSucc b.castSucc/
      tripleLowDiameter (satellitesRelative (x n))) atTop (𝓝 0)) :
    ∀ eta : ℝ,0<eta → ∀ᶠ n in atTop,∀ t∈Icc (0 : ℝ) 1,
      ‖(tripleLowDiameter (satellitesRelative (x n)))⁻¹ •
        (satellitesRelative (x n) c.castSucc-
          physicalPairSegmentPoint (satellitesRelative (x n) a.castSucc)
            (satellitesRelative (x n) b.castSucc) t)-
        (lowNestedOrientation a c) • quarterTurn (polarPoint 1 (theta0 0))‖<eta := by
  have hdir := normalized_complete_lower_triple_nested_directions eps mu x heps hepst hm hx
    hconv r theta hr hpolar horder muLimit hmt qLimit hqt theta0 htt center htriple a b c hab hca hcb hpair
  exact physical_pair_segment_scaled_displacement_uniform
    (fun n => satellitesRelative (x n) a.castSucc)
    (fun n => satellitesRelative (x n) b.castSucc)
    (fun n => satellitesRelative (x n) c.castSucc)
    (fun n => tripleLowDiameter (satellitesRelative (x n)))
    ((lowNestedOrientation a c) • quarterTurn (polarPoint 1 (theta0 0)))
    (fun n => tripleLowDiameter_pos _ (satellitesRelative_collisionFree _ (hx n).1))
    (hdir.2.2.2.1 a (by simp)) (by simpa only [satelliteDistance,norm_sub_rev] using hpair)

end DominantFiveBody
