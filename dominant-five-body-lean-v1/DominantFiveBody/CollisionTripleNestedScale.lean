import DominantFiveBody.CollisionTripleNestedMacro
import DominantFiveBody.CollisionNestedUnselected

/-! # Actual smaller-pair scales in a lower collision triple -/

noncomputable section
open scoped BigOperators ContDiff
open Filter Set Topology
namespace DominantFiveBody
open Coorbital
set_option maxHeartbeats 1500000

theorem normalized_complete_lower_triple_nested_precise_scales
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
    Tendsto (fun n => physicalPairDirection (satellitesRelative (x n)) a.castSucc b.castSucc)
      atTop (𝓝 (quarterTurn (polarPoint 1 (theta0 0)))) ∧
    Tendsto (fun n => eps n*(mu n a.castSucc+mu n b.castSucc)/
      satelliteDistance (satellitesRelative (x n)) a.castSucc b.castSucc^3) atTop (𝓝 0) ∧
    Tendsto (fun n => (theta n b.castSucc-theta n a.castSucc)/
      satelliteDistance (satellitesRelative (x n)) a.castSucc b.castSucc) atTop (𝓝 1) ∧
    Tendsto (fun n => (r n b.castSucc-r n a.castSucc)/
      satelliteDistance (satellitesRelative (x n)) a.castSucc b.castSucc) atTop (𝓝 0) ∧
    Tendsto (fun n => (mu n a.castSucc+mu n b.castSucc)/
      satelliteDistance (satellitesRelative (x n)) a.castSucc b.castSucc^3) atTop (𝓝 (27/4 : ℝ)) ∧
    Tendsto (fun n => mu n c.castSucc/tripleLowDiameter (satellitesRelative (x n))^3)
      atTop (𝓝 (9/4 : ℝ)) ∧
    Tendsto (fun n => (mu n a.castSucc+mu n b.castSucc)/
      tripleLowDiameter (satellitesRelative (x n))^3) atTop (𝓝 0) := by
  let d := fun n => tripleLowDiameter (satellitesRelative (x n))
  let s := fun n => satelliteDistance (satellitesRelative (x n)) a.castSucc b.castSucc
  have hd (n : ℕ) : 0<d n := tripleLowDiameter_pos _ (satellitesRelative_collisionFree _ (hx n).1)
  have hs (n : ℕ) : 0<s n := norm_pos_iff.mpr (sub_ne_zero.mpr
    ((satellitesRelative_collisionFree _ (hx n).1).2 a.castSucc b.castSucc
      (ne_of_lt (show a.castSucc<b.castSucc from hab))))
  have hq0 : qLimit 0=center := (htriple 0).mpr (by decide)
  have hdt := tripleLowDiameter_tendsto_zero _ qLimit hqt
    (((htriple 1).mpr (by decide)).trans hq0.symm)
    (((htriple 2).mpr (by decide)).trans hq0.symm)
  have hst : Tendsto s atTop (𝓝 0) := by
    convert! hpair.mul hdt using 1
    · funext n
      have hdn : tripleLowDiameter (satellitesRelative (x n))≠0 := ne_of_gt (hd n)
      dsimp only [s]
      field_simp [hdn]
    · ring
  obtain ⟨hrt,hunit,hmono,_,hspan⟩ := normalized_ordered_polar_limit_geometry eps mu x heps hepst hm hx
    r theta hr hpolar horder muLimit hmt qLimit hqt theta0 htt
  have hrat (i : Satellite) : Tendsto (fun n => r n i) atTop (𝓝 1) :=
    (continuous_apply i).continuousAt.tendsto.comp hrt
  have htat (i : TripleLabel) : Tendsto (fun n => theta n i.castSucc) atTop (𝓝 (theta0 0)) := by
    have he := complete_lower_triple_angles_equal qLimit theta0 hunit hmono hspan center htriple i 0
    simpa only [Function.comp_def,he,show (0 : TripleLabel).castSucc=(0 : Satellite) from rfl] using
      (continuous_apply i.castSucc).continuousAt.tendsto.comp htt
  have htp : Tendsto (fun n => theta n 3) atTop (𝓝 (theta0 3)) :=
    (continuous_apply (3 : Satellite)).continuousAt.tendsto.comp htt
  have hgapAbs := (normalized_complete_triple_limiting_exterior eps mu x heps hepst hm hx
    r theta hr hpolar horder muLimit hmt qLimit hqt theta0 htt 3 center htriple).2 0 (by decide)
  have hgapEq : theta0 3-theta0 0=h := by
    rw [abs_of_nonneg (sub_nonneg.mpr (hmono (by decide : (0 : Satellite)≤3)))] at hgapAbs
    exact hgapAbs
  have hside : 0<theta0 3-theta0 0 ∧ theta0 3-theta0 0<Real.pi := by
    rw [hgapEq]
    constructor <;> unfold h <;> linarith [Real.pi_pos]
  obtain ⟨hnu0,hmp⟩ := normalized_complete_lower_triple_mass_vanishes eps mu x heps hepst hm hx
    hconv r theta hr hpolar horder muLimit hmt qLimit hqt theta0 htt center htriple
  have hlowMass (i : TripleLabel) : Tendsto (fun n => mu n i.castSucc) atTop (𝓝 0) := by
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hnu0
    · exact Eventually.of_forall (fun n => ((hm n).1 i.castSucc).le)
    · exact Eventually.of_forall (fun n => by
        fin_cases i
        · change mu n 0≤mu n 0+mu n 1+mu n 2
          linarith [(hm n).1 1,(hm n).1 2]
        · change mu n 1≤mu n 0+mu n 1+mu n 2
          linarith [(hm n).1 0,(hm n).1 2]
        · change mu n 2≤mu n 0+mu n 1+mu n 2
          linarith [(hm n).1 0,(hm n).1 1])
  have hcf (n : ℕ) : RelativeCollisionFree (polarSatellites (r n) (theta n)) := by
    rw [← hpolar n]
    exact satellitesRelative_collisionFree _ (hx n).1
  have hroot (n : ℕ) (i : Satellite) : vectorResidual (eps n) (mu n) (polarSatellites (r n) (theta n)) i=0 := by
    rw [← hpolar n]
    exact vectorResidual_zero_of_normalized _ _ _ (hx n) i
  have hQ (n : ℕ) (i : Satellite) : tangentialResidual (mu n) (r n) (theta n) i=0 :=
    tangentialResidual_zero_of_normalized _ _ _ (hx n) (ne_of_gt (heps n)) (r n) (theta n) (hr n) (hpolar n) i
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
  have hdir := normalized_complete_lower_triple_nested_directions eps mu x heps hepst hm hx
    hconv r theta hr hpolar horder muLimit hmt qLimit hqt theta0 htt center htriple a b c hab hca hcb hpair
  have hadj : b.castSucc.val=a.castSucc.val+1 := by
    rcases hdir.1 with ⟨rfl,rfl,_⟩|⟨rfl,rfl,_⟩ <;> norm_num
  have hsupport : ∀ᶠ n in atTop,0<det2
      (polarPoint (r n b.castSucc) (theta n b.castSucc)-polarPoint (r n a.castSucc) (theta n a.castSucc))
      (polarPoint (r n 3) (theta n 3)-polarPoint (r n a.castSucc) (theta n a.castSucc)) :=
    Eventually.of_forall (fun n => by
      have hn := strictConvex_adjacent_pair_support (x n) (hconv n) a.castSucc b.castSucc hadj 3 hp
      simpa only [hpolar n,polarSatellites] using hn)
  let U : Plane := lowNestedOrientation a c • quarterTurn (polarPoint 1 (theta0 0))
  have hJnorm : ‖quarterTurn (polarPoint 1 (theta0 0))‖=1 := by
    have he : ‖quarterTurn (polarPoint 1 (theta0 0))‖^2=1 := by
      rw [← real_inner_self_eq_norm_sq,quarterTurn_inner_quarterTurn,real_inner_self_eq_norm_sq,
        polarPoint_norm,abs_one]
      norm_num
    nlinarith [norm_nonneg (quarterTurn (polarPoint 1 (theta0 0)))]
  have hU : ‖U‖=1 := by rw [norm_smul,Real.norm_eq_abs,lowNestedOrientation_abs,hJnorm]; ring
  have hUr : inner ℝ U (polarPoint 1 (theta0 0))=0 := by
    rw [real_inner_smul_left]
    have horth := quarterTurn_inner_self (polarPoint 1 (theta0 0))
    rw [real_inner_comm] at horth
    rw [horth,mul_zero]
  have hsource : Tendsto (fun n => (d n)⁻¹ •
      (polarPoint (r n c.castSucc) (theta n c.castSucc)-polarPoint (r n a.castSucc) (theta n a.castSucc)))
      atTop (𝓝 U) := by
    have hpEq (n : ℕ) (i : Satellite) : satellitesRelative (x n) i=polarPoint (r n i) (theta n i) :=
      congrFun (hpolar n) i
    simpa only [hpEq] using hdir.2.2.2.1 a (by simp)
  have hsmall : Tendsto (fun n => satelliteDistance (polarSatellites (r n) (theta n)) a.castSucc b.castSucc/d n)
      atTop (𝓝 0) := by simpa only [← hpolar] using hpair
  have hQpos := physical_pair_tangential_difference_eventually_positive mu r theta a.castSucc b.castSucc
    (hcastNe hab.ne) (fun n => (hm n).1) hr hQ (fun n => by simpa only [← hpolar] using hs n)
    (by simpa only [← hpolar] using hst) (hrat a.castSucc) (hrat b.castSucc)
    (fun n => horder n a.castSucc b.castSucc hab)
  have habs : |theta0 0-theta0 3|=h := by rw [abs_sub_comm]; exact hgapAbs
  have hmacro : Tendsto (fun n => (mu n a.castSucc+mu n b.castSucc+mu n c.castSucc)/d n^3)
      atTop (𝓝 (kappa |theta0 0-theta0 3|)) := by
    simpa only [three_distinct_low_masses_sum _ a b c hab.ne hca hcb,habs,kappa_h] using
      normalized_complete_lower_triple_nested_macro_mass_cube_limit eps mu x heps hepst hm hx
        hconv r theta hr hpolar horder muLimit hmt qLimit hqt theta0 htt center htriple a b c hab hca hcb hpair
  have hfull := physical_nested_pair_unselected_precise_scales eps mu r theta d a.castSucc b.castSucc c.castSucc 3
    (hcastNe hab.ne) (hlowNe c) hc hp hcf hroot hQ hepst (fun n => (hm n).1) hr hrat
    (hlowMass a) (hlowMass b) (theta0 0) (theta0 3) (htat a) (htat b) (htat c) htp hside hd hdt U hU hUr
    hsource hsmall hmp (fun n => horder n a.castSucc b.castSucc hab) hQpos hsupport hmacro
  simpa only [← hpolar,habs,kappa_h,show (3 : ℝ)*(9/4)=27/4 by norm_num] using hfull

end DominantFiveBody
