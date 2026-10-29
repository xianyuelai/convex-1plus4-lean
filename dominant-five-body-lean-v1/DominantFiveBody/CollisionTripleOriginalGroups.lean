import DominantFiveBody.CollisionTripleScaledCompact
import DominantFiveBody.CollisionTripleComplete

/-! # Proposition 4.3: the original equal-scaled-limit group route

The current-mass group averages, compact scaled-position extraction, and
the actual polar distance identity prove the original radial and width
conclusions without a regular/nested case split in this proof.
-/

noncomputable section
open scoped BigOperators ContDiff
open Filter Set Topology
namespace DominantFiveBody
set_option maxHeartbeats 1500000

theorem low_satellite_exists_tripleLabel (i : Satellite) (hi : i≠3) :
    ∃ j : TripleLabel,j.castSucc=i := by
  fin_cases i
  · exact ⟨0,rfl⟩
  · exact ⟨1,rfl⟩
  · exact ⟨2,rfl⟩
  · exact (hi rfl).elim

/-- The original source's chosen scaled limits determine actual polar
radius differences and width, with the cubic upper bound derived from
the earlier physical angular estimate rather than supplied by a caller. -/
theorem normalized_complete_lower_triple_original_group_geometry_of_scaled_limits
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
    (z : Satellite → Plane)
    (hzt : ∀ i : TripleLabel,Tendsto (fun n =>
      (tripleLowDiameter (satellitesRelative (x n)))⁻¹ •
        (satellitesRelative (x n) i.castSucc-satellitesRelative (x n) 0)) atTop (𝓝 (z i.castSucc))) :
    (∀ i j : TripleLabel,Tendsto (fun n => (r n j.castSucc-r n i.castSucc)/
      tripleLowDiameter (satellitesRelative (x n))) atTop (𝓝 0)) ∧
    Tendsto (fun n => (theta n 2-theta n 0)/
      tripleLowDiameter (satellitesRelative (x n))) atTop (𝓝 1) := by
  classical
  let q := fun n => satellitesRelative (x n)
  let d := fun n => tripleLowDiameter (q n)
  have hcf (n : ℕ) : RelativeCollisionFree (q n) := satellitesRelative_collisionFree _ (hx n).1
  have hd (n : ℕ) : 0<d n := tripleLowDiameter_pos _ (hcf n)
  obtain ⟨_,C,_,hC,hinitial⟩ := normalized_complete_lower_triple_initial_scales eps mu x
    heps hepst hm hx hconv r theta hr hpolar horder muLimit hmt qLimit hqt theta0 htt center htriple
  have hbound : ∃ C : ℝ,0<C ∧ ∀ᶠ n in atTop,(∑ i∈Finset.univ.erase (3 : Satellite),mu n i)/d n^3≤C := by
    refine ⟨C,hC,?_⟩
    filter_upwards [hinitial] with n hn
    have h3 := PositiveRatio.coordinate_le_one _ (hm n) 3
    have hc := hn.2.2.trans (by simpa only [mul_one] using mul_le_mul_of_nonneg_left h3 hC.le)
    simpa only [Finset.sum_erase_eq_sub (Finset.mem_univ (3 : Satellite)),Fin.sum_univ_four,
      add_sub_cancel_right,d,q] using hc
  obtain ⟨hrt,hunit,hmono,_,hspan⟩ := normalized_ordered_polar_limit_geometry eps mu x
    heps hepst hm hx r theta hr hpolar horder muLimit hmt qLimit hqt theta0 htt
  have hcenter : center=polarPoint 1 (theta0 0) := ((htriple 0).mpr (by decide)).symm.trans (hunit 0)
  have hcu : ‖center‖=1 := by rw [hcenter,polarPoint_norm,abs_one]
  have hsep : qLimit 3≠center := fun he => (htriple 3).mp he rfl
  have hcenterE : ∀ i∈Finset.univ.erase (3 : Satellite),qLimit i=center := by
    intro i hi
    exact (htriple i).mpr (Finset.mem_erase.mp hi).1
  have hdiam : ∀ n,∀ i∈Finset.univ.erase (3 : Satellite),∀ j∈Finset.univ.erase (3 : Satellite),
      satelliteDistance (q n) i j≤d n := by
    intro n i hi j hj
    obtain ⟨a,rfl⟩ := low_satellite_exists_tripleLabel i (Finset.mem_erase.mp hi).1
    obtain ⟨b,rfl⟩ := low_satellite_exists_tripleLabel j (Finset.mem_erase.mp hj).1
    exact tripleLowDiameter_bound _ a b
  have hztE : ∀ i∈Finset.univ.erase (3 : Satellite),Tendsto (fun n => (d n)⁻¹ • (q n i-q n 0))
      atTop (𝓝 (z i)) := by
    intro i hi
    obtain ⟨a,rfl⟩ := low_satellite_exists_tripleLabel i (Finset.mem_erase.mp hi).1
    exact hzt a
  have hroots (n : ℕ) (i : Satellite) : vectorResidual (eps n) (mu n) (q n) i=0 :=
    vectorResidual_zero_of_normalized _ _ _ (hx n) i
  have lowMem (i : TripleLabel) : i.castSucc∈Finset.univ.erase (3 : Satellite) := by
    fin_cases i <;> decide
  have hangle (i : TripleLabel) : Tendsto (fun n => theta n i.castSucc) atTop (𝓝 (theta0 0)) := by
    have heq := complete_lower_triple_angles_equal qLimit theta0 hunit hmono hspan center htriple i 0
    change theta0 i.castSucc=theta0 0 at heq
    simpa only [Function.comp_def,heq] using (continuous_apply i.castSucc).tendsto theta0 |>.comp htt
  have hnorm (i j : TripleLabel) (n : ℕ) :
      ‖(d n)⁻¹ • (polarPoint (r n j.castSucc) (theta n j.castSucc)-
        polarPoint (r n i.castSucc) (theta n i.castSucc))‖≤1 := by
    rw [norm_smul,Real.norm_eq_abs,abs_inv,abs_of_pos (hd n)]
    apply (inv_mul_le_iff₀ (hd n)).mpr
    have hb := tripleLowDiameter_bound (q n) j i
    simpa only [d,q,hpolar n,satelliteDistance,polarSatellites,mul_one] using hb
  have hrad : ∀ i j : TripleLabel,Tendsto (fun n => (r n j.castSucc-r n i.castSucc)/d n)
      atTop (𝓝 0) := by
    intro i j
    have hp := physical_triple_scaled_groups_radial_projection_limit eps mu q hepst hm hroots hcf
      qLimit hqt 3 center hcu hcenterE hsep d hd hdiam hbound 0 z hztE i.castSucc j.castSucc
      (lowMem i) (lowMem j)
    apply polar_scaled_radius_difference_tendsto_zero _ _ _ _ d (theta0 0)
      (hangle i) (hangle j) hd (hnorm i j)
    simpa only [q,hpolar,hcenter,polarSatellites] using hp
  have hgap (i j : TripleLabel) : Tendsto (fun n => theta n j.castSucc-theta n i.castSucc) atTop (𝓝 0) := by
    simpa only [sub_self] using (hangle j).sub (hangle i)
  have hdPolar (n : ℕ) : 0<tripleLowDiameter (polarSatellites (r n) (theta n)) := by
    rw [← hpolar n]
    exact hd n
  have hwidth := triple_width_distance_ratio_tendsto_one r theta
    (fun i => (continuous_apply i).tendsto (fun _ : Satellite => (1 : ℝ)) |>.comp hrt) hdPolar
    (fun n => ⟨by linarith [(horder n 0 1 (by decide)).1],by linarith [(horder n 1 2 (by decide)).1]⟩)
    (hgap 0 1) (hgap 1 2) (by simpa only [d,q,hpolar] using hrad)
  exact ⟨hrad,by simpa only [hpolar] using hwidth⟩

/-- Proposition 4.3's original compact equal-limit group argument,
promoted to the complete original sequence. -/
theorem normalized_complete_lower_triple_original_group_geometry
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
  have hsub (phi : ℕ → ℕ) (hphi : StrictMono phi) :
      ∃ psi : ℕ → ℕ,StrictMono psi ∧
        (∀ i j : TripleLabel,Tendsto (fun n => (r (phi (psi n)) j.castSucc-r (phi (psi n)) i.castSucc)/
          tripleLowDiameter (satellitesRelative (x (phi (psi n))))) atTop (𝓝 0)) ∧
        Tendsto (fun n => (theta (phi (psi n)) 2-theta (phi (psi n)) 0)/
          tripleLowDiameter (satellitesRelative (x (phi (psi n))))) atTop (𝓝 1) := by
    obtain ⟨psi,z,hpsi,hzt,_,_⟩ := lower_triple_scaled_positions_compact_subsequence
      (fun n => satellitesRelative (x (phi n)))
      (fun n => satellitesRelative_collisionFree _ (hx (phi n)).1)
    have hmono := hphi.comp hpsi
    have hg := normalized_complete_lower_triple_original_group_geometry_of_scaled_limits
      (eps ∘ phi ∘ psi) (mu ∘ phi ∘ psi) (x ∘ phi ∘ psi)
      (fun n => heps (phi (psi n))) (hepst.comp hmono.tendsto_atTop)
      (fun n => hm (phi (psi n))) (fun n => hx (phi (psi n))) (fun n => hconv (phi (psi n)))
      (r ∘ phi ∘ psi) (theta ∘ phi ∘ psi) (fun n => hr (phi (psi n)))
      (fun n => hpolar (phi (psi n))) (fun n => horder (phi (psi n)))
      muLimit (hmt.comp hmono.tendsto_atTop) qLimit (hqt.comp hmono.tendsto_atTop)
      theta0 (htt.comp hmono.tendsto_atTop) center htriple z hzt
    exact ⟨psi,hpsi,hg⟩
  constructor
  · intro i j
    apply real_tendsto_of_every_subsequence
    intro phi hphi
    obtain ⟨psi,hpsi,hrad,_⟩ := hsub phi hphi
    exact ⟨psi,hpsi,hrad i j⟩
  · apply real_tendsto_of_every_subsequence
    intro phi hphi
    obtain ⟨psi,hpsi,_,hwidth⟩ := hsub phi hphi
    exact ⟨psi,hpsi,hwidth⟩

end DominantFiveBody
