import DominantFiveBody.CollisionScaledAngularLimits

/-! # Original arbitrary-group angular contradiction in Proposition 4.3 -/
noncomputable section
open scoped BigOperators ContDiff
open Filter Set Topology
namespace DominantFiveBody
open Coorbital
set_option maxHeartbeats 1800000

theorem physical_triple_original_angular_groups_zero_cube_impossible
    (eps : ℕ → ℝ) (mu r theta : ℕ → Satellite → ℝ) (d : ℕ → ℝ)
    (heps : ∀ n,0≤eps n) (hepst : Tendsto eps atTop (𝓝 0))
    (hm : ∀ n,PositiveRatio (mu n)) (hr : ∀ n i,0<r n i)
    (hroot : ∀ n i,angularResidual (eps n) (mu n) (r n) (theta n) i=0)
    (p ref : Satellite) (psi angle0 : ℝ) (z : Satellite → Plane)
    (hd : ∀ n,0<d n) (hdt : Tendsto d atTop (𝓝 0))
    (hrt : ∀ i,Tendsto (fun n => r n i) atTop (𝓝 1))
    (hvp : Tendsto (fun n => theta n p) atTop (𝓝 angle0))
    (hvt : ∀ i∈Finset.univ.erase p,Tendsto (fun n => theta n i) atTop (𝓝 psi))
    (hne : angle0≠psi) (hpi : |angle0-psi|<Real.pi) (hgap0 : |psi-angle0|=h)
    (hmp : Tendsto (fun n => mu n p) atTop (𝓝 1))
    (hzt : ∀ i∈Finset.univ.erase p,Tendsto (fun n => (d n)⁻¹ •
      (polarSatellites (r n) (theta n) i-polarSatellites (r n) (theta n) ref)) atTop (𝓝 (z i)))
    (hrad : ∀ i∈Finset.univ.erase p,∀ j∈Finset.univ.erase p,
      Tendsto (fun n => (r n j-r n i)/d n) atTop (𝓝 0))
    (hgaps : ∀ᶠ n in atTop,∀ i∈Finset.univ.erase p,∀ j∈Finset.univ.erase p,
      |theta n j-theta n i|≤2*d n)
    (hnu : Tendsto (fun n => (∑ i∈Finset.univ.erase p,mu n i)/d n^3) atTop (𝓝 0))
    (a b : Satellite) (ha : a∈Finset.univ.erase p) (hb : b∈Finset.univ.erase p)
    (hzab : z a≠z b) : False := by
  classical
  let E := Finset.univ.erase p
  let q := fun n => polarSatellites (r n) (theta n)
  have hdir (i : Satellite) (hi : i∈E) (j : Satellite) (hj : j∈E) :
      Tendsto (fun n => (d n)⁻¹ • (q n j-q n i)) atTop (𝓝 (z j-z i)) := by
    convert! (hzt j hj).sub (hzt i hi) using 1
    funext n;module
  have hangle (i : Satellite) (hi : i∈E) (j : Satellite) (hj : j∈E) :
      Tendsto (fun n => (theta n j-theta n i)/d n) atTop
        (𝓝 (inner ℝ (z j-z i) (quarterTurn (polarPoint 1 psi)))) :=
    polar_scaled_angle_difference_limit _ _ _ _ d psi (z j-z i)
      (hrt i) (hrt j) (hvt i hi) (hvt j hj) (hdir i hi j hj)
  have hrbound : ∀ᶠ n in atTop,∀ i∈E,r n i≤2 := by
    have hall : ∀ᶠ n in atTop,∀ i : Satellite,r n i≤2 := by
      apply (eventually_all).mpr
      intro i
      exact ((hrt i).eventually (Iio_mem_nhds (by norm_num : (1 : ℝ)<2))).mono (fun _ hn => hn.le)
    exact hall.mono (fun n hn i _ => hn i)
  have hJrep (a : Satellite) (ha : a∈E) : Tendsto (fun n =>
      physicalSourceFullAngularField (eps n) (r n p) (theta n p) (r n a) (theta n a)/d n)
      atTop (𝓝 0) := by
    let S := E.filter (fun i => z i=z a)
    have hSsub : S⊆E := Finset.filter_subset _ _
    have haS : a∈S := Finset.mem_filter.mpr ⟨ha,rfl⟩
    have hS : S.Nonempty := ⟨a,haS⟩
    have hp : p∉S := fun h => (Finset.mem_erase.mp (hSsub h)).1 rfl
    have hclasses : ∀ i∈S,∀ j∈E\S,z i≠z j := by
      intro i hi j hj he
      have hiEq := (Finset.mem_filter.mp hi).2
      exact (Finset.mem_sdiff.mp hj).2 (Finset.mem_filter.mpr
        ⟨(Finset.mem_sdiff.mp hj).1,he.symm.trans hiEq⟩)
    obtain ⟨eta,heta,hsep⟩ := equal_scaled_class_cross_separation q d hd E S hSsub ref z hzt hclasses
    have hnearSet : Sᶜ.erase p=E\S := by
      ext i
      simp only [E,Finset.mem_erase,Finset.mem_compl,Finset.mem_sdiff,Finset.mem_univ,and_true]
    have hnear := actual_group_near_angular_scaled_tendsto_zero eps mu r theta d hm heps S hS p
      eta heta hd hdt hnu hr hrbound hSsub
      (hgaps.mono (fun n hn i hi j hj => hn i (hSsub hi) j
        (Finset.mem_erase.mpr ⟨(Finset.mem_erase.mp hj).1,Finset.mem_univ _⟩)))
      (by
        filter_upwards [hsep] with n hn
        intro i hi j hj
        have hs := hn i hi j (hnearSet ▸ hj)
        simpa only [q,satelliteDistance,norm_sub_rev] using hs)
    apply actual_current_angular_group_representative_scaled_limit eps mu r theta d hm hd hroot S hS p hp a hmp hnear
    intro i hi
    have hiE := hSsub hi
    have hz : z i=z a := (Finset.mem_filter.mp hi).2
    have hang : Tendsto (fun n => (theta n i-theta n a)/d n) atTop (𝓝 0) := by
      simpa only [hz,sub_self,inner_zero_left] using hangle a ha i hiE
    have ht := physicalSourceFullAngularField_moving_secant_limit eps (fun n => r n p) (fun n => theta n p)
      (fun n => r n a) (fun n => theta n a) (fun n => r n i) (fun n => theta n i)
      d angle0 psi 0 hepst (hrt p) hvp (hrt a) (hrt i) (hvt a ha) (hvt i hiE)
      hd (hrad a ha i hiE) hang hne hpi
    simpa only [zero_mul] using ht
  let omega := inner ℝ (z b-z a) (quarterTurn (polarPoint 1 psi))
  have hJactual := physicalSourceFullAngularField_moving_secant_limit eps (fun n => r n p) (fun n => theta n p)
    (fun n => r n a) (fun n => theta n a) (fun n => r n b) (fun n => theta n b)
    d angle0 psi omega hepst (hrt p) hvp (hrt a) (hrt b) (hvt a ha) (hvt b hb)
    hd (hrad a ha b hb) (hangle a ha b hb) hne hpi
  have hJzero : Tendsto (fun n =>
      (physicalSourceFullAngularField (eps n) (r n p) (theta n p) (r n b) (theta n b)-
        physicalSourceFullAngularField (eps n) (r n p) (theta n p) (r n a) (theta n a))/d n)
      atTop (𝓝 0) := by
    simpa only [sub_div,sub_self] using (hJrep b hb).sub (hJrep a ha)
  have homega : omega=0 := by
    have he := tendsto_nhds_unique hJactual hJzero
    rw [hgap0,kappa_h] at he
    linarith
  have hang0 : Tendsto (fun n => (theta n b-theta n a)/d n) atTop (𝓝 0) := by
    simpa only [show inner ℝ (z b-z a) (quarterTurn (polarPoint 1 psi))=0 from homega] using hangle a ha b hb
  have hvec0 := polar_scaled_displacement_tendsto (fun n => r n a) (fun n => theta n a)
    (fun n => r n b) (fun n => theta n b) d psi 0 (hrt a) (hrt b) (hvt a ha) (hvt b hb)
    hd (hrad a ha b hb) hang0
  have hlim0 : z b-z a=0 := by
    have hz := tendsto_nhds_unique (hdir a ha b hb) hvec0
    simpa only [zero_smul] using hz
  exact hzab (sub_eq_zero.mp hlim0).symm

theorem normalized_complete_lower_triple_original_angular_scaled_zero_cube_impossible
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
        (satellitesRelative (x n) i.castSucc-satellitesRelative (x n) 0)) atTop (𝓝 (z i.castSucc)))
    (hnu : Tendsto (fun n => (mu n 0+mu n 1+mu n 2)/
      tripleLowDiameter (satellitesRelative (x n))^3) atTop (𝓝 0))
    (a b : TripleLabel) (hzab : z a.castSucc≠z b.castSucc) : False := by
  classical
  let q := fun n => satellitesRelative (x n)
  let d := fun n => tripleLowDiameter (q n)
  have hcf (n : ℕ) : RelativeCollisionFree (q n) := satellitesRelative_collisionFree _ (hx n).1
  have hd (n : ℕ) : 0<d n := tripleLowDiameter_pos _ (hcf n)
  have hgeometry := normalized_complete_lower_triple_original_group_geometry_of_scaled_limits
    eps mu x heps hepst hm hx hconv r theta hr hpolar horder muLimit hmt qLimit hqt theta0 htt center htriple z hzt
  obtain ⟨hrt,hunit,hmono,_,hspan⟩ := normalized_ordered_polar_limit_geometry eps mu x
    heps hepst hm hx r theta hr hpolar horder muLimit hmt qLimit hqt theta0 htt
  have hrat (i : Satellite) : Tendsto (fun n => r n i) atTop (𝓝 1) :=
    (continuous_apply i).continuousAt.tendsto.comp hrt
  have htat (i : TripleLabel) : Tendsto (fun n => theta n i.castSucc) atTop (𝓝 (theta0 0)) := by
    have he := complete_lower_triple_angles_equal qLimit theta0 hunit hmono hspan center htriple i 0
    simpa only [Function.comp_def,he,show (0 : TripleLabel).castSucc=(0 : Satellite) from rfl] using
      (continuous_apply i.castSucc).continuousAt.tendsto.comp htt
  have htp : Tendsto (fun n => theta n 3) atTop (𝓝 (theta0 3)) :=
    (continuous_apply (3 : Satellite)).continuousAt.tendsto.comp htt
  have hq0 : qLimit 0=center := (htriple 0).mpr (by decide)
  have hdt := tripleLowDiameter_tendsto_zero _ qLimit hqt
    (((htriple 1).mpr (by decide)).trans hq0.symm)
    (((htriple 2).mpr (by decide)).trans hq0.symm)
  have hg := (normalized_complete_triple_limiting_exterior eps mu x heps hepst hm hx r theta hr hpolar horder
    muLimit hmt qLimit hqt theta0 htt 3 center htriple).2 0 (by decide)
  have hne : theta0 3≠theta0 0 := by
    intro he
    rw [he,sub_self,abs_zero] at hg
    have hh : 0<h := by unfold h;positivity
    linarith
  have hpi : |theta0 3-theta0 0|<Real.pi := by rw [hg];unfold h;linarith [Real.pi_pos]
  have hmp := (normalized_complete_lower_triple_mass_vanishes eps mu x heps hepst hm hx
    hconv r theta hr hpolar horder muLimit hmt qLimit hqt theta0 htt center htriple).2
  have hztE : ∀ i∈Finset.univ.erase (3 : Satellite),Tendsto (fun n => (d n)⁻¹ •
      (polarSatellites (r n) (theta n) i-polarSatellites (r n) (theta n) 0)) atTop (𝓝 (z i)) := by
    intro i hi
    obtain ⟨j,rfl⟩ := low_satellite_exists_tripleLabel i (Finset.mem_erase.mp hi).1
    simpa only [d,q,hpolar] using hzt j
  have hradE : ∀ i∈Finset.univ.erase (3 : Satellite),∀ j∈Finset.univ.erase (3 : Satellite),
      Tendsto (fun n => (r n j-r n i)/d n) atTop (𝓝 0) := by
    intro i hi j hj
    obtain ⟨u,rfl⟩ := low_satellite_exists_tripleLabel i (Finset.mem_erase.mp hi).1
    obtain ⟨v,rfl⟩ := low_satellite_exists_tripleLabel j (Finset.mem_erase.mp hj).1
    exact hgeometry.1 u v
  have hgapBound : ∀ᶠ n in atTop,∀ i∈Finset.univ.erase (3 : Satellite),∀ j∈Finset.univ.erase (3 : Satellite),
      |theta n j-theta n i|≤2*d n := by
    filter_upwards [hgeometry.2.eventually (Iio_mem_nhds (by norm_num : (1 : ℝ)<2))] with n hn
    have hW : theta n 2-theta n 0≤2*d n := (div_le_iff₀ (hd n)).mp hn.le
    have hmonoNow : Monotone (theta n) := by
      intro i j hij
      rcases eq_or_lt_of_le hij with rfl|hij
      · exact le_rfl
      · exact (sub_pos.mp (horder n i j hij).1).le
    intro i hi j hj
    have hi2 : i≤(2 : Satellite) := by
      obtain ⟨u,rfl⟩ := low_satellite_exists_tripleLabel i (Finset.mem_erase.mp hi).1
      fin_cases u <;> decide
    have hj2 : j≤(2 : Satellite) := by
      obtain ⟨u,rfl⟩ := low_satellite_exists_tripleLabel j (Finset.mem_erase.mp hj).1
      fin_cases u <;> decide
    exact abs_le.mpr ⟨by linarith [hmonoNow (Fin.zero_le j),hmonoNow hi2],
      by linarith [hmonoNow (Fin.zero_le i),hmonoNow hj2]⟩
  apply physical_triple_original_angular_groups_zero_cube_impossible eps mu r theta d
    (fun n => (heps n).le) hepst hm hr
    (fun n => (polarResiduals_zero_of_normalized (eps n) (mu n) (x n) (hx n)
      (hm n) (heps n) (r n) (theta n) (hr n) (hpolar n)).2)
    3 0 (theta0 0) (theta0 3) z hd hdt hrat htp
  · intro i hi
    obtain ⟨j,rfl⟩ := low_satellite_exists_tripleLabel i (Finset.mem_erase.mp hi).1
    exact htat j
  · exact hne
  · exact hpi
  · simpa only [abs_sub_comm] using hg
  · exact hmp
  · exact hztE
  · exact hradE
  · exact hgapBound
  · simpa only [Finset.sum_erase_eq_sub (Finset.mem_univ (3 : Satellite)),Fin.sum_univ_four,
      add_sub_cancel_right,d,q] using hnu
  · exact show a.castSucc∈Finset.univ.erase (3 : Satellite) from by fin_cases a <;> decide
  · exact show b.castSucc∈Finset.univ.erase (3 : Satellite) from by fin_cases b <;> decide
  · exact hzab

end DominantFiveBody
