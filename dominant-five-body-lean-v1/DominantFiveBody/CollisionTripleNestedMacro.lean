import DominantFiveBody.CollisionNestedDirections
import DominantFiveBody.CollisionNestedScales

/-! # Actual nested lower-triple total mass scale

The signed first-order geometry is obtained from the actual smaller
pair. The current-mass averaged angular equation then gives the total
cluster mass divided by the actual diameter cubed.
-/

noncomputable section
open scoped BigOperators
open Filter Set Topology
namespace DominantFiveBody
open Coorbital
set_option maxHeartbeats 800000

theorem normalized_complete_lower_triple_nested_macro_mass_cube_limit
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
    Tendsto (fun n => (mu n 0+mu n 1+mu n 2)/
      tripleLowDiameter (satellitesRelative (x n))^3) atTop (𝓝 (9/4 : ℝ)) := by
  obtain ⟨hrt,hunit,hmono,_,hspan⟩ := normalized_ordered_polar_limit_geometry eps mu x
    heps hepst hm hx r theta hr hpolar horder muLimit hmt qLimit hqt theta0 htt
  have hrat (i : Satellite) : Tendsto (fun n => r n i) atTop (𝓝 1) :=
    (continuous_apply i).continuousAt.tendsto.comp hrt
  have hthetaEq (i : TripleLabel) : theta0 i.castSucc=theta0 0 :=
    complete_lower_triple_angles_equal qLimit theta0 hunit hmono hspan center htriple i 0
  have hgapAbs := (normalized_complete_triple_limiting_exterior eps mu x heps hepst hm hx
    r theta hr hpolar horder muLimit hmt qLimit hqt theta0 htt 3 center htriple).2 0 (by decide)
  have hsep : theta0 3≠theta0 0 := by
    intro he
    rw [he,sub_self,abs_zero] at hgapAbs
    have hh : 0<h := by unfold h; positivity
    linarith
  have hpi : |theta0 3-theta0 0|<Real.pi := by
    rw [hgapAbs]
    unfold h
    linarith [Real.pi_pos]
  have hd (n : ℕ) : 0<tripleLowDiameter (satellitesRelative (x n)) :=
    tripleLowDiameter_pos _ (satellitesRelative_collisionFree _ (hx n).1)
  have hq0 : qLimit 0=center := (htriple 0).mpr (by decide)
  have hdt := tripleLowDiameter_tendsto_zero _ qLimit hqt
    (((htriple 1).mpr (by decide)).trans hq0.symm)
    (((htriple 2).mpr (by decide)).trans hq0.symm)
  have hrad := normalized_complete_lower_triple_nested_radial_limits eps mu x heps hepst hm hx
    hconv r theta hr hpolar horder muLimit hmt qLimit hqt theta0 htt center htriple a b c
    hab.ne hca hcb hpair
  have hdir := normalized_complete_lower_triple_nested_directions eps mu x heps hepst hm hx
    hconv r theta hr hpolar horder muLimit hmt qLimit hqt theta0 htt center htriple a b c
    hab hca hcb hpair
  have hcastNe {i j : TripleLabel} (hij : i≠j) : i.castSucc≠j.castSucc := by
    intro he
    exact hij (Fin.castSucc_injective _ he)
  have hlowNe (i : TripleLabel) : i.castSucc≠(3 : Satellite) := by fin_cases i <;> decide
  have hc : c.castSucc∈pairExteriorLabels a.castSucc b.castSucc := by
    simp only [pairExteriorLabels,Finset.mem_erase,Finset.mem_univ,and_true]
    exact ⟨hcastNe hcb,hcastNe hca⟩
  have hp : (3 : Satellite)∈pairExteriorLabels a.castSucc b.castSucc := by
    simp only [pairExteriorLabels,Finset.mem_erase,Finset.mem_univ,and_true]
    exact ⟨(hlowNe b).symm,(hlowNe a).symm⟩
  have homega : lowNestedOrientation a c≠0 := by
    intro he
    have hh := lowNestedOrientation_abs a c
    rw [he,abs_zero] at hh
    norm_num at hh
  have hmacro := normalized_nested_macro_mass_cube_limit_of_first_order_geometry eps mu x
    heps hepst hm hx r theta hr hpolar hrat theta0 htt a.castSucc b.castSucc c.castSucc 3
    (hcastNe hab.ne) (hlowNe c) hc hp (theta0 0) (lowNestedOrientation a c) homega
    (hthetaEq a) (hthetaEq b) (hthetaEq c) hsep hpi
    (fun n => tripleLowDiameter (satellitesRelative (x n))) hd hdt (hrad a c) (hrad b c)
    (hdir.2.2.1 a (by simp)) (hdir.2.2.1 b (by simp))
    (hdir.2.2.2.2 a (by simp)) (hdir.2.2.2.2 b (by simp))
  have habs : |theta0 0-theta0 3|=h := by rw [abs_sub_comm]; exact hgapAbs
  simpa only [three_distinct_low_masses_sum _ a b c hab.ne hca hcb,habs,kappa_h] using hmacro

end DominantFiveBody
