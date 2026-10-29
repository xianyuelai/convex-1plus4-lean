import DominantFiveBody.CollisionNestedGeometry
import DominantFiveBody.CollisionTripleWidth

/-! # Actual nested lower-triple radial and width limits

The smaller pair is specified by its actual distance-to-diameter limit.
Current pair masses cancel in the vector grouping theorem; no limiting
individual mass share or direction is assumed.
-/

noncomputable section
open scoped BigOperators Matrix ContDiff
open Filter Set Topology
namespace DominantFiveBody
set_option maxHeartbeats 1200000

theorem three_distinct_tripleLabels_cover (a b c : TripleLabel)
    (hab : a≠b) (hca : c≠a) (hcb : c≠b) (i : TripleLabel) : i=a ∨ i=b ∨ i=c := by
  fin_cases a <;> fin_cases b <;> fin_cases c <;> fin_cases i <;> simp_all

theorem tripleLargestDistance_low_permutation (q : SatelliteConfiguration) (a b c : TripleLabel)
    (hab : a≠b) (hca : c≠a) (hcb : c≠b) :
    tripleLargestDistance q a.castSucc b.castSucc c.castSucc=tripleLowDiameter q := by
  have h10 : ‖q 1-q 0‖=‖q 0-q 1‖ := norm_sub_rev _ _
  have h20 : ‖q 2-q 0‖=‖q 0-q 2‖ := norm_sub_rev _ _
  have h21 : ‖q 2-q 1‖=‖q 1-q 2‖ := norm_sub_rev _ _
  fin_cases a <;> fin_cases b <;> fin_cases c
  all_goals simp_all [tripleLargestDistance,tripleLowDiameter,satelliteDistance]
  all_goals first | ac_rfl | simp only [max_left_comm, max_comm]

theorem normalized_complete_lower_triple_nested_radial_limits
    (eps : ℕ → ℝ) (mu : ℕ → MassRatio) (x : ℕ → Configuration)
    (heps : ∀ n,0<eps n) (hepst : Tendsto eps atTop (𝓝 0))
    (hm : ∀ n,PositiveRatio (mu n))
    (hx : ∀ n,NormalizedCentralConfiguration (masses (eps n) (mu n)) (x n))
    (hconv : ∀ n,StrictConvexInOrder ⟨Equiv.refl Label,rfl⟩ (x n))
    (r theta : ℕ → Satellite → ℝ) (hr : ∀ n i,0<r n i)
    (hpolar : ∀ n,satellitesRelative (x n)=polarSatellites (r n) (theta n))
    (horder : ∀ n i j,i<j → 0<theta n j-theta n i ∧ theta n j-theta n i<Real.pi)
    (muLimit : MassRatio) (hmt : Tendsto mu atTop (𝓝 muLimit))
    (qLimit : SatelliteConfiguration)
    (hqt : Tendsto (fun n => satellitesRelative (x n)) atTop (𝓝 qLimit))
    (theta0 : Satellite → ℝ) (htheta : Tendsto theta atTop (𝓝 theta0))
    (center : Plane) (htriple : CompleteLimitingSatelliteTriple qLimit 3 center)
    (a b c : TripleLabel) (hab : a≠b) (hca : c≠a) (hcb : c≠b)
    (hpair : Tendsto (fun n => satelliteDistance (satellitesRelative (x n)) a.castSucc b.castSucc/
      tripleLowDiameter (satellitesRelative (x n))) atTop (𝓝 0)) :
    ∀ i j : TripleLabel,Tendsto (fun n => (r n j.castSucc-r n i.castSucc)/
      tripleLowDiameter (satellitesRelative (x n))) atTop (𝓝 0) := by
  classical
  let q := fun n => satellitesRelative (x n)
  let d := fun n => tripleLowDiameter (q n)
  have hcf (n : ℕ) : RelativeCollisionFree (q n) := satellitesRelative_collisionFree (x n) (hx n).1
  have hd (n : ℕ) : 0<d n := tripleLowDiameter_pos _ (hcf n)
  have hdiam (n : ℕ) : d n=tripleLargestDistance (q n) a.castSucc b.castSucc c.castSucc :=
    (tripleLargestDistance_low_permutation _ a b c hab hca hcb).symm
  obtain ⟨_,C,_,hC,hinitial⟩ := normalized_complete_lower_triple_initial_scales eps mu x
    heps hepst hm hx hconv r theta hr hpolar horder muLimit hmt qLimit hqt theta0 htheta center htriple
  have hbound : ∀ᶠ n in atTop,(mu n a.castSucc+mu n b.castSucc+mu n c.castSucc)/d n^3≤C := by
    filter_upwards [hinitial] with n hn
    rw [three_distinct_low_masses_sum _ a b c hab hca hcb]
    have h3 : mu n 3≤1 := PositiveRatio.coordinate_le_one _ (hm n) 3
    exact hn.2.2.trans (by simpa only [mul_one] using mul_le_mul_of_nonneg_left h3 hC.le)
  obtain ⟨_,hunit,hmono,_,hspan⟩ := normalized_ordered_polar_limit_geometry eps mu x
    heps hepst hm hx r theta hr hpolar horder muLimit hmt qLimit hqt theta0 htheta
  have lowNe (i : TripleLabel) : i.castSucc≠(3 : Satellite) := by fin_cases i <;> decide
  have castNe {i j : TripleLabel} (hij : i≠j) : i.castSucc≠j.castSucc := by
    intro he
    apply hij
    apply Fin.ext
    exact congrArg (fun k : Satellite => k.val) he
  have hcenter : center=polarPoint 1 (theta0 0) := ((htriple 0).mpr (by decide)).symm.trans (hunit 0)
  have hcu : ‖center‖=1 := by rw [hcenter,polarPoint_norm,abs_one]
  have hsep : qLimit 3≠center := fun he => (htriple 3).mp he rfl
  have hpoint (i : TripleLabel) : Tendsto (fun n => q n i.castSucc) atTop (𝓝 center) := by
    have heq := (htriple i.castSucc).mpr (lowNe i)
    simpa only [q,Function.comp_def,heq] using (continuous_apply i.castSucc).tendsto qLimit |>.comp hqt
  have hp : Tendsto (fun n => q n 3) atTop (𝓝 (qLimit 3)) := by
    simpa only [q,Function.comp_def] using (continuous_apply (3 : Satellite)).tendsto qLimit |>.comp hqt
  have hcMem : c.castSucc∈pairExteriorLabels a.castSucc b.castSucc :=
    Finset.mem_erase.mpr ⟨castNe hcb,Finset.mem_erase.mpr ⟨castNe hca,Finset.mem_univ _⟩⟩
  have hpMem : (3 : Satellite)∈pairExteriorLabels a.castSucc b.castSucc :=
    Finset.mem_erase.mpr ⟨(lowNe b).symm,Finset.mem_erase.mpr ⟨(lowNe a).symm,Finset.mem_univ _⟩⟩
  have hroots (n : ℕ) (i : Satellite) : vectorResidual (eps n) (mu n) (q n) i=0 :=
    vectorResidual_zero_of_normalized (eps n) (mu n) (x n) (hx n) i
  have hproj := physical_nested_group_radial_projections_tendsto eps mu q hepst hm hroots hcf
    muLimit hmt a.castSucc b.castSucc c.castSucc 3 (castNe hab) (lowNe c) hcMem hpMem
    center (qLimit 3) hcu hsep (hpoint a) (hpoint b) (hpoint c) hp d hd hdiam hpair C hbound
  have hangle (i : TripleLabel) : Tendsto (fun n => theta n i.castSucc) atTop (𝓝 (theta0 0)) := by
    have heq : theta0 i.castSucc=theta0 0 :=
      complete_lower_triple_angles_equal qLimit theta0 hunit hmono hspan center htriple i 0
    simpa only [Function.comp_def,heq] using (continuous_apply i.castSucc).tendsto theta0 |>.comp htheta
  have hnorm (i j : TripleLabel) (n : ℕ) :
      ‖(d n)⁻¹ • (polarPoint (r n j.castSucc) (theta n j.castSucc)-
        polarPoint (r n i.castSucc) (theta n i.castSucc))‖≤1 := by
    have heq : ‖(d n)⁻¹ • (polarPoint (r n j.castSucc) (theta n j.castSucc)-
        polarPoint (r n i.castSucc) (theta n i.castSucc))‖=
        satelliteDistance (q n) i.castSucc j.castSucc/d n := by
      rw [norm_smul,Real.norm_eq_abs,abs_inv,abs_of_pos (hd n)]
      simp only [q,hpolar n,satelliteDistance,polarSatellites,div_eq_mul_inv,norm_sub_rev,mul_comm]
    rw [heq]
    exact (div_le_one (hd n)).mpr (tripleLowDiameter_bound (q n) i j)
  have hradA : Tendsto (fun n => (r n a.castSucc-r n c.castSucc)/d n) atTop (𝓝 0) := by
    apply polar_scaled_radius_difference_tendsto_zero _ _ _ _ d (theta0 0)
      (hangle c) (hangle a) hd (hnorm c a)
    simpa only [q,hpolar,hcenter,polarSatellites] using hproj.1
  have hradB : Tendsto (fun n => (r n b.castSucc-r n c.castSucc)/d n) atTop (𝓝 0) := by
    apply polar_scaled_radius_difference_tendsto_zero _ _ _ _ d (theta0 0)
      (hangle c) (hangle b) hd (hnorm c b)
    simpa only [q,hpolar,hcenter,polarSatellites] using hproj.2
  have hradC : Tendsto (fun n => (r n c.castSucc-r n c.castSucc)/d n) atTop (𝓝 0) := by
    simpa only [sub_self,zero_div] using (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (𝓝 0))
  have htoC (i : TripleLabel) : Tendsto (fun n => (r n i.castSucc-r n c.castSucc)/d n) atTop (𝓝 0) := by
    rcases three_distinct_tripleLabels_cover a b c hab hca hcb i with rfl|rfl|rfl
    · exact hradA
    · exact hradB
    · exact hradC
  intro i j
  have ht := (htoC j).sub (htoC i)
  simpa only [sub_self] using ht.congr (fun n => by ring)

theorem normalized_complete_lower_triple_nested_width_limit
    (eps : ℕ → ℝ) (mu : ℕ → MassRatio) (x : ℕ → Configuration)
    (heps : ∀ n,0<eps n) (hepst : Tendsto eps atTop (𝓝 0))
    (hm : ∀ n,PositiveRatio (mu n))
    (hx : ∀ n,NormalizedCentralConfiguration (masses (eps n) (mu n)) (x n))
    (hconv : ∀ n,StrictConvexInOrder ⟨Equiv.refl Label,rfl⟩ (x n))
    (r theta : ℕ → Satellite → ℝ) (hr : ∀ n i,0<r n i)
    (hpolar : ∀ n,satellitesRelative (x n)=polarSatellites (r n) (theta n))
    (horder : ∀ n i j,i<j → 0<theta n j-theta n i ∧ theta n j-theta n i<Real.pi)
    (muLimit : MassRatio) (hmt : Tendsto mu atTop (𝓝 muLimit))
    (qLimit : SatelliteConfiguration)
    (hqt : Tendsto (fun n => satellitesRelative (x n)) atTop (𝓝 qLimit))
    (theta0 : Satellite → ℝ) (htheta : Tendsto theta atTop (𝓝 theta0))
    (center : Plane) (htriple : CompleteLimitingSatelliteTriple qLimit 3 center)
    (a b c : TripleLabel) (hab : a≠b) (hca : c≠a) (hcb : c≠b)
    (hpair : Tendsto (fun n => satelliteDistance (satellitesRelative (x n)) a.castSucc b.castSucc/
      tripleLowDiameter (satellitesRelative (x n))) atTop (𝓝 0)) :
    Tendsto (fun n => (theta n 2-theta n 0)/tripleLowDiameter (satellitesRelative (x n))) atTop (𝓝 1) := by
  obtain ⟨hrt,hunit,hmono,_,hspan⟩ := normalized_ordered_polar_limit_geometry eps mu x
    heps hepst hm hx r theta hr hpolar horder muLimit hmt qLimit hqt theta0 htheta
  have hrad := normalized_complete_lower_triple_nested_radial_limits eps mu x heps hepst hm hx
    hconv r theta hr hpolar horder muLimit hmt qLimit hqt theta0 htheta center htriple a b c hab hca hcb hpair
  have hgap (i j : TripleLabel) : Tendsto (fun n => theta n j.castSucc-theta n i.castSucc) atTop (𝓝 0) := by
    have hi := (continuous_apply i.castSucc).tendsto theta0 |>.comp htheta
    have hj := (continuous_apply j.castSucc).tendsto theta0 |>.comp htheta
    simpa only [complete_lower_triple_angles_equal qLimit theta0 hunit hmono hspan center htriple i j,
      sub_self,Function.comp_def] using hj.sub hi
  have hd (n : ℕ) : 0<tripleLowDiameter (polarSatellites (r n) (theta n)) := by
    rw [← hpolar n]
    exact tripleLowDiameter_pos _ (satellitesRelative_collisionFree (x n) (hx n).1)
  have hh := triple_width_distance_ratio_tendsto_one r theta
    (fun i => (continuous_apply i).tendsto (fun _ : Satellite => (1 : ℝ)) |>.comp hrt) hd
    (fun n => ⟨by linarith [(horder n 0 1 (by decide)).1],by linarith [(horder n 1 2 (by decide)).1]⟩)
    (hgap 0 1) (hgap 1 2) (by simpa only [hpolar] using hrad)
  simpa only [hpolar] using hh

end DominantFiveBody
