import DominantFiveBody.CollisionExteriorDerivativeBounds
import DominantFiveBody.CollisionNestedSegmentGeometry

/-! # Original DP=O(1) on the entire actual smaller-pair segment -/
noncomputable section
open scoped BigOperators ContDiff
open Filter Set Topology
namespace DominantFiveBody
open Coorbital
set_option maxHeartbeats 1800000

theorem polarUnit_distance_h (angle psi : ℝ) (hgap : angle-psi=Coorbital.h) :
    ‖polarPoint 1 angle-polarPoint 1 psi‖=1 := by
  have hh : (angle-psi)/2=Real.pi/6 := by unfold Coorbital.h at hgap;linarith
  have hs := polar_distance_sq 1 1 psi angle
  rw [hh,Real.sin_pi_div_six] at hs
  norm_num at hs
  rcases hs with he|he
  · exact he
  · nlinarith [norm_nonneg (polarPoint 1 angle-polarPoint 1 psi)]

theorem normalized_complete_lower_triple_nested_segment_derivative_bound
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
    ∀ᶠ n in atTop,∀ t∈Icc (0 : ℝ) 1,
      ‖fderiv ℝ (pairExteriorField (mu n) (satellitesRelative (x n)) a.castSucc b.castSucc)
        (physicalPairSegmentPoint (satellitesRelative (x n) a.castSucc) (satellitesRelative (x n) b.castSucc) t)‖≤128 := by
  classical
  let q := fun n => satellitesRelative (x n)
  let d := fun n => tripleLowDiameter (q n)
  have hd (n : ℕ) : 0<d n := tripleLowDiameter_pos _ (satellitesRelative_collisionFree _ (hx n).1)
  have hfull := normalized_complete_lower_triple_nested_precise_scales eps mu x heps hepst hm hx
    hconv r theta hr hpolar horder muLimit hmt qLimit hqt theta0 htt center htriple a b c hab hca hcb hpair
  have hdir := normalized_complete_lower_triple_nested_directions eps mu x heps hepst hm hx
    hconv r theta hr hpolar horder muLimit hmt qLimit hqt theta0 htt center htriple a b c hab hca hcb hpair
  obtain ⟨hrt,hunit,hmono,_,hspan⟩ := normalized_ordered_polar_limit_geometry eps mu x heps hepst hm hx
    r theta hr hpolar horder muLimit hmt qLimit hqt theta0 htt
  have hgapAbs := (normalized_complete_triple_limiting_exterior eps mu x heps hepst hm hx
    r theta hr hpolar horder muLimit hmt qLimit hqt theta0 htt 3 center htriple).2 0 (by decide)
  have hgap : theta0 3-theta0 0=h := by
    rw [abs_of_nonneg (sub_nonneg.mpr (hmono (by decide : (0 : Satellite)≤3)))] at hgapAbs
    exact hgapAbs
  have hcenter : center=polarPoint 1 (theta0 0) := ((htriple 0).mpr (by decide)).symm.trans (hunit 0)
  have hfarNorm : ‖qLimit 3-center‖=1 := by
    rw [hunit 3,hcenter]
    exact polarUnit_distance_h (theta0 3) (theta0 0) hgap
  have hpoint (i : TripleLabel) : Tendsto (fun n => q n i.castSucc) atTop (𝓝 center) := by
    have he := (htriple i.castSucc).mpr (by fin_cases i <;> decide)
    simpa only [Function.comp_def,he] using (continuous_apply i.castSucc).continuousAt.tendsto.comp hqt
  have hqp : Tendsto (fun n => q n 3) atTop (𝓝 (qLimit 3)) :=
    (continuous_apply (3 : Satellite)).continuousAt.tendsto.comp hqt
  have hJnorm : ‖quarterTurn (polarPoint 1 (theta0 0))‖=1 := by
    have he : ‖quarterTurn (polarPoint 1 (theta0 0))‖^2=1 := by
      rw [← real_inner_self_eq_norm_sq,quarterTurn_inner_quarterTurn,real_inner_self_eq_norm_sq,
        polarPoint_norm,abs_one]
      norm_num
    nlinarith [norm_nonneg (quarterTurn (polarPoint 1 (theta0 0)))]
  have hu : ‖(lowNestedOrientation a c) • quarterTurn (polarPoint 1 (theta0 0))‖=1 := by
    rw [norm_smul,Real.norm_eq_abs,lowNestedOrientation_abs,hJnorm,mul_one]
  have hnear := physical_pair_segment_near_distance_uniform (fun n => q n a.castSucc)
    (fun n => q n b.castSucc) (fun n => q n c.castSucc) d
    ((lowNestedOrientation a c) • quarterTurn (polarPoint 1 (theta0 0))) hd hu
    (hdir.2.2.2.1 a (by simp)) (by simpa only [satelliteDistance,norm_sub_rev] using hpair)
  have hfar := physical_pair_segment_far_distance_uniform (fun n => q n a.castSucc)
    (fun n => q n b.castSucc) (fun n => q n 3) center (qLimit 3) (hpoint a) (hpoint b) hqp
  have hcastNe {i j : TripleLabel} (hij : i≠j) : i.castSucc≠j.castSucc := by
    intro he
    apply hij
    apply Fin.ext
    exact congrArg (fun k : Satellite => k.val) he
  have hlowNe (i : TripleLabel) : i.castSucc≠(3 : Satellite) := by fin_cases i <;> decide
  have hc : c.castSucc∈pairExteriorLabels a.castSucc b.castSucc := by
    simp only [pairExteriorLabels,Finset.mem_erase,Finset.mem_univ,and_true]
    exact ⟨hcastNe hcb,hcastNe hca⟩
  have hp : (3 : Satellite)∈pairExteriorLabels a.castSucc b.castSucc := by
    simp only [pairExteriorLabels,Finset.mem_erase,Finset.mem_univ,and_true]
    exact ⟨(hlowNe b).symm,(hlowNe a).symm⟩
  filter_upwards [hnear (1/2) (by norm_num),hfar (1/2) (by norm_num),
    hfull.2.2.2.2.2.1.eventually (Iio_mem_nhds (by norm_num : (9/4 : ℝ)<3))] with n hnNear hnFar hnMass
  intro t ht
  have hyNear : d n/2≤‖q n c.castSucc-physicalPairSegmentPoint (q n a.castSucc) (q n b.castSucc) t‖ := by
    have hb := (abs_lt.mp (hnNear t ht)).1
    have hn : (1/2 : ℝ)≤‖q n c.castSucc-physicalPairSegmentPoint (q n a.castSucc) (q n b.castSucc) t‖/d n := by linarith
    have hh := (le_div_iff₀ (hd n)).mp hn
    linarith
  have hyFar : (1/2 : ℝ)≤‖q n 3-physicalPairSegmentPoint (q n a.castSucc) (q n b.castSucc) t‖ := by
    have hb := (abs_lt.mp (hnFar t ht)).1
    rw [hfarNorm] at hb
    linarith
  have hb := pairExteriorField_fderiv_norm_bound_two_sources (mu n) (hm n) (q n)
    a.castSucc b.castSucc c.castSucc 3 (hcastNe hab.ne) (hlowNe c) hc hp
    (physicalPairSegmentPoint (q n a.castSucc) (q n b.castSucc) t) (d n) 3 (hd n) (by norm_num)
    hyNear hyFar hnMass.le
  norm_num at hb
  exact hb

end DominantFiveBody
