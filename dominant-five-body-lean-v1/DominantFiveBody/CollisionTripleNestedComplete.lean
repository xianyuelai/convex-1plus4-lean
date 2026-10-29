import DominantFiveBody.CollisionTripleNestedScale
import DominantFiveBody.CollisionPairSecantRadialBound

/-! # Complete actual lower nested rates, including the quantitative radial bound -/

noncomputable section
open scoped BigOperators ContDiff
open Filter Set Topology
namespace DominantFiveBody
open Coorbital
set_option maxHeartbeats 1500000

theorem normalized_complete_lower_triple_nested_radial_bound
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
    ∃ C : ℝ,0<C ∧ ∀ᶠ n in atTop,|r n b.castSucc-r n a.castSucc|≤
      C*eps n*satelliteDistance (satellitesRelative (x n)) a.castSucc b.castSucc := by
  have hfull := normalized_complete_lower_triple_nested_precise_scales eps mu x heps hepst hm hx
    hconv r theta hr hpolar horder muLimit hmt qLimit hqt theta0 htt center htriple a b c hab hca hcb hpair
  have hdir := normalized_complete_lower_triple_nested_directions eps mu x heps hepst hm hx
    hconv r theta hr hpolar horder muLimit hmt qLimit hqt theta0 htt center htriple a b c hab hca hcb hpair
  obtain ⟨_,hunit,hmono,_,hspan⟩ := normalized_ordered_polar_limit_geometry eps mu x heps hepst hm hx
    r theta hr hpolar horder muLimit hmt qLimit hqt theta0 htt
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
  have hcenter : center=polarPoint 1 (theta0 0) := ((htriple 0).mpr (by decide)).symm.trans (hunit 0)
  have hpoint (i : TripleLabel) : Tendsto (fun n => satellitesRelative (x n) i.castSucc) atTop (𝓝 center) := by
    simpa only [Function.comp_def,(htriple i.castSucc).mpr (hlowNe i)] using
      (continuous_apply i.castSucc).continuousAt.tendsto.comp hqt
  have hpointP : Tendsto (fun n => satellitesRelative (x n) 3) atTop (𝓝 (qLimit 3)) :=
    (continuous_apply (3 : Satellite)).continuousAt.tendsto.comp hqt
  have hpointSep : qLimit 3≠center := fun he => (htriple 3).mp he rfl
  have hmp := (normalized_complete_lower_triple_mass_vanishes eps mu x heps hepst hm hx hconv
    r theta hr hpolar horder muLimit hmt qLimit hqt theta0 htt center htriple).2
  let U : Plane := lowNestedOrientation a c • quarterTurn (polarPoint 1 (theta0 0))
  have hJnorm : ‖quarterTurn (polarPoint 1 (theta0 0))‖=1 := by
    have he : ‖quarterTurn (polarPoint 1 (theta0 0))‖^2=1 := by
      rw [← real_inner_self_eq_norm_sq,quarterTurn_inner_quarterTurn,real_inner_self_eq_norm_sq,
        polarPoint_norm,abs_one]
      norm_num
    nlinarith [norm_nonneg (quarterTurn (polarPoint 1 (theta0 0)))]
  have hU : ‖U‖=1 := by rw [norm_smul,Real.norm_eq_abs,lowNestedOrientation_abs,hJnorm]; ring
  have hsec := physical_nested_pair_exterior_secant_limit mu
    (fun n => tripleLowDiameter (satellitesRelative (x n))) (fun n => satellitesRelative (x n))
    a.castSucc b.castSucc c.castSucc 3 (hcastNe hab.ne) (hlowNe c) hc hp
    (fun n => satellitesRelative_collisionFree _ (hx n).1)
    (fun n => tripleLowDiameter_pos _ (satellitesRelative_collisionFree _ (hx n).1))
    U (quarterTurn (polarPoint 1 (theta0 0))) center (qLimit 3) hU (9/4) 1 hpointSep
    (hdir.2.2.2.1 a (by simp)) hpair hfull.1 hfull.2.2.2.2.2.1 hmp (hpoint a) (hpoint b) hpointP
  have hcf (n : ℕ) : RelativeCollisionFree (polarSatellites (r n) (theta n)) := by
    rw [← hpolar n]
    exact satellitesRelative_collisionFree _ (hx n).1
  have hroot (n : ℕ) (i : Satellite) : vectorResidual (eps n) (mu n) (polarSatellites (r n) (theta n)) i=0 := by
    rw [← hpolar n]
    exact vectorResidual_zero_of_normalized _ _ _ (hx n) i
  have hthetaEq := complete_lower_triple_angles_equal qLimit theta0 hunit hmono hspan center htriple b a
  have htat (i : Satellite) : Tendsto (fun n => theta n i) atTop (𝓝 (theta0 i)) :=
    (continuous_apply i).continuousAt.tendsto.comp htt
  have hgap : Tendsto (fun n => theta n b.castSucc-theta n a.castSucc) atTop (𝓝 0) := by
    simpa only [hthetaEq,sub_self] using (htat b.castSucc).sub (htat a.castSucc)
  obtain ⟨C,hC,hbound⟩ := physical_pair_radial_bound_of_exterior_secant_limit eps mu r theta a.castSucc b.castSucc
    (hcastNe hab.ne) (fun n => (heps n).le) hm hr hcf hroot
    (by simpa only [hpolar] using hfull.2.1) hgap _ (by simpa only [hpolar] using hsec)
  refine ⟨C,hC,?_⟩
  simpa only [← hpolar] using hbound

theorem normalized_complete_lower_triple_nested_scale_complete
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
    b.val=a.val+1 ∧
    Tendsto (fun n => (mu n a.castSucc+mu n b.castSucc)/(mu n 0+mu n 1+mu n 2)) atTop (𝓝 0) ∧
    Tendsto (fun n => (mu n 0+mu n 1+mu n 2)/tripleLowDiameter (satellitesRelative (x n))^3)
      atTop (𝓝 (9/4 : ℝ)) ∧
    Tendsto (fun n => (mu n a.castSucc+mu n b.castSucc)/
      satelliteDistance (satellitesRelative (x n)) a.castSucc b.castSucc^3) atTop (𝓝 (27/4 : ℝ)) ∧
    Tendsto (fun n => (theta n b.castSucc-theta n a.castSucc)/
      satelliteDistance (satellitesRelative (x n)) a.castSucc b.castSucc) atTop (𝓝 1) ∧
    ∃ C : ℝ,0<C ∧ ∀ᶠ n in atTop,|r n b.castSucc-r n a.castSucc|≤
      C*eps n*satelliteDistance (satellitesRelative (x n)) a.castSucc b.castSucc := by
  have hfull := normalized_complete_lower_triple_nested_precise_scales eps mu x heps hepst hm hx
    hconv r theta hr hpolar horder muLimit hmt qLimit hqt theta0 htt center htriple a b c hab hca hcb hpair
  have hmacro := normalized_complete_lower_triple_nested_macro_mass_cube_limit eps mu x heps hepst hm hx
    hconv r theta hr hpolar horder muLimit hmt qLimit hqt theta0 htt center htriple a b c hab hca hcb hpair
  have hdir := normalized_complete_lower_triple_nested_directions eps mu x heps hepst hm hx
    hconv r theta hr hpolar horder muLimit hmt qLimit hqt theta0 htt center htriple a b c hab hca hcb hpair
  have hadj : b.val=a.val+1 := by
    rcases hdir.1 with ⟨rfl,rfl,_⟩|⟨rfl,rfl,_⟩ <;> norm_num
  have hshare : Tendsto (fun n => (mu n a.castSucc+mu n b.castSucc)/(mu n 0+mu n 1+mu n 2))
      atTop (𝓝 0) := by
    convert! hfull.2.2.2.2.2.2.div hmacro (by norm_num : (9/4 : ℝ)≠0) using 1
    · funext n
      simp only [Pi.div_apply]
      have hd := tripleLowDiameter_pos _ (satellitesRelative_collisionFree _ (hx n).1)
      have hnu := add_pos (add_pos ((hm n).1 0) ((hm n).1 1)) ((hm n).1 2)
      field_simp [ne_of_gt hd,ne_of_gt hnu]
    · norm_num
  exact ⟨hadj,hshare,hmacro,hfull.2.2.2.2.1,hfull.2.2.1,
    normalized_complete_lower_triple_nested_radial_bound eps mu x heps hepst hm hx hconv
      r theta hr hpolar horder muLimit hmt qLimit hqt theta0 htt center htriple a b c hab hca hcb hpair⟩

end DominantFiveBody
