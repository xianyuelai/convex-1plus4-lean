import DominantFiveBody.CollisionTripleNestedWidth
import DominantFiveBody.NewtonScaleTransport

/-! First-order geometry of an actual smaller pair in a lower triple.
Adjacency and the signed outer displacement are consequences of the
physical diameter and width limits, before a nested chart is used. -/

noncomputable section
open scoped BigOperators ContDiff
open Filter Set Topology
namespace DominantFiveBody
set_option maxHeartbeats 1000000

def lowNestedOrientation (a c : TripleLabel) : ℝ := if c<a then -1 else 1

theorem lowNestedOrientation_abs (a c : TripleLabel) : |lowNestedOrientation a c|=1 := by
  unfold lowNestedOrientation
  split_ifs <;> norm_num

theorem low_nested_adjacent_and_angle_limit (theta : ℕ → Satellite → ℝ) (d : ℕ → ℝ)
    (a b c : TripleLabel) (hab : a<b) (hca : c≠a) (hcb : c≠b)
    (hwidth : Tendsto (fun n => (theta n 2-theta n 0)/d n) atTop (𝓝 1))
    (hpair : Tendsto (fun n => (theta n b.castSucc-theta n a.castSucc)/d n) atTop (𝓝 0)) :
    ((a=0 ∧ b=1 ∧ c=2) ∨ (a=1 ∧ b=2 ∧ c=0)) ∧
    Tendsto (fun n => (theta n c.castSucc-theta n a.castSucc)/d n)
      atTop (𝓝 (lowNestedOrientation a c)) := by
  have hh : ∀ a b c : TripleLabel,a<b → c≠a → c≠b →
      (a=0 ∧ b=1 ∧ c=2) ∨ (a=0 ∧ b=2 ∧ c=1) ∨ (a=1 ∧ b=2 ∧ c=0) := by decide
  rcases hh a b c hab hca hcb with ⟨rfl,rfl,rfl⟩|⟨rfl,rfl,rfl⟩|⟨rfl,rfl,rfl⟩
  · exact ⟨Or.inl ⟨rfl,rfl,rfl⟩,hwidth⟩
  · have he : (1 : ℝ)=0 := tendsto_nhds_unique hwidth hpair
    norm_num at he
  · refine ⟨Or.inr ⟨rfl,rfl,rfl⟩,?_⟩
    have ht := hpair.sub hwidth
    convert! ht using 1
    · funext n
      change (theta n 0-theta n 1)/d n =
        (theta n 2-theta n 1)/d n-(theta n 2-theta n 0)/d n
      ring
    · norm_num [lowNestedOrientation]

theorem normalized_complete_lower_triple_nested_directions
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
    ((a=0 ∧ b=1 ∧ c=2) ∨ (a=1 ∧ b=2 ∧ c=0)) ∧
    Tendsto (fun n => (theta n b.castSucc-theta n a.castSucc)/
      tripleLowDiameter (satellitesRelative (x n))) atTop (𝓝 0) ∧
    (∀ i ∈ ({a,b} : Finset TripleLabel),
      Tendsto (fun n => (theta n c.castSucc-theta n i.castSucc)/
        tripleLowDiameter (satellitesRelative (x n))) atTop (𝓝 (lowNestedOrientation a c))) ∧
    (∀ i ∈ ({a,b} : Finset TripleLabel),
      Tendsto (fun n => (tripleLowDiameter (satellitesRelative (x n)))⁻¹ •
        (satellitesRelative (x n) c.castSucc-satellitesRelative (x n) i.castSucc))
        atTop (𝓝 ((lowNestedOrientation a c) • quarterTurn (polarPoint 1 (theta0 0))))) ∧
    (∀ i ∈ ({a,b} : Finset TripleLabel),
      Tendsto (fun n => satelliteDistance (satellitesRelative (x n)) i.castSucc c.castSucc/
        tripleLowDiameter (satellitesRelative (x n))) atTop (𝓝 1)) := by
  let d := fun n => tripleLowDiameter (satellitesRelative (x n))
  have hd (n : ℕ) : 0<d n := tripleLowDiameter_pos _ (satellitesRelative_collisionFree _ (hx n).1)
  obtain ⟨hrt,hunit,hmono,_,hspan⟩ := normalized_ordered_polar_limit_geometry eps mu x heps hepst hm hx
    r theta hr hpolar horder muLimit hmt qLimit hqt theta0 htt
  have hrat (i : Satellite) : Tendsto (fun n => r n i) atTop (𝓝 1) :=
    (continuous_apply i).continuousAt.tendsto.comp hrt
  have htat (i : TripleLabel) : Tendsto (fun n => theta n i.castSucc) atTop (𝓝 (theta0 0)) := by
    have he := complete_lower_triple_angles_equal qLimit theta0 hunit hmono hspan center htriple i 0
    simpa only [Function.comp_def,he,show (0 : TripleLabel).castSucc=(0 : Satellite) from rfl] using
      (continuous_apply i.castSucc).continuousAt.tendsto.comp htt
  have hrad := normalized_complete_lower_triple_nested_radial_limits eps mu x heps hepst hm hx
    hconv r theta hr hpolar horder muLimit hmt qLimit hqt theta0 htt center htriple a b c
    hab.ne hca hcb hpair
  have hwidth := normalized_complete_lower_triple_nested_width_limit eps mu x heps hepst hm hx
    hconv r theta hr hpolar horder muLimit hmt qLimit hqt theta0 htt center htriple a b c
    hab.ne hca hcb hpair
  have hcast : a.castSucc<b.castSucc := hab
  have hdefect := polar_scaled_angle_distance_defect
    (fun n => r n a.castSucc) (fun n => r n b.castSucc)
    (fun n => theta n a.castSucc) (fun n => theta n b.castSucc) d hd
    (hrat a.castSucc) (hrat b.castSucc)
    (by simpa only [sub_self] using (htat b).sub (htat a))
    (fun n => (horder n a.castSucc b.castSucc hcast).1.le) (hrad a b)
    (fun n => by simpa only [d,hpolar,satelliteDistance,polarSatellites] using
      tripleLowDiameter_bound (satellitesRelative (x n)) b a)
  have hgap : Tendsto (fun n => (theta n b.castSucc-theta n a.castSucc)/d n) atTop (𝓝 0) := by
    have hh := hpair.sub hdefect
    convert! hh using 1
    · funext n
      simp only [d,hpolar,satelliteDistance,polarSatellites]
      rw [norm_sub_rev (polarPoint (r n a.castSucc) _)]
      ring
    · norm_num
  obtain ⟨hadj,hangleA⟩ := low_nested_adjacent_and_angle_limit theta d a b c hab hca hcb hwidth hgap
  have hangleB : Tendsto (fun n => (theta n c.castSucc-theta n b.castSucc)/d n)
      atTop (𝓝 (lowNestedOrientation a c)) := by
    convert! hangleA.sub hgap using 1
    · funext n; ring
    · ring
  have hangle (i : TripleLabel) (hi : i∈({a,b} : Finset TripleLabel)) :
      Tendsto (fun n => (theta n c.castSucc-theta n i.castSucc)/d n)
        atTop (𝓝 (lowNestedOrientation a c)) := by
    rcases Finset.mem_insert.mp hi with rfl|hi
    · exact hangleA
    · exact Finset.mem_singleton.mp hi ▸ hangleB
  have hvector (i : TripleLabel) (hi : i∈({a,b} : Finset TripleLabel)) :
      Tendsto (fun n => (d n)⁻¹ •
        (satellitesRelative (x n) c.castSucc-satellitesRelative (x n) i.castSucc))
        atTop (𝓝 ((lowNestedOrientation a c) • quarterTurn (polarPoint 1 (theta0 0)))) := by
    have hh := polar_scaled_displacement_tendsto _ _ _ _ d (theta0 0) (lowNestedOrientation a c)
      (hrat i.castSucc) (hrat c.castSucc) (htat i) (htat c) hd (hrad i c) (hangle i hi)
    simpa only [hpolar,polarSatellites] using hh
  refine ⟨hadj,hgap,hangle,hvector,?_⟩
  intro i hi
  have hn := (hvector i hi).norm
  have hJ : ‖quarterTurn (polarPoint 1 (theta0 0))‖=1 := by
    rw [← Real.sqrt_sq (norm_nonneg _)]
    rw [← real_inner_self_eq_norm_sq,quarterTurn_inner_quarterTurn,real_inner_self_eq_norm_sq,
      polarPoint_norm,abs_one]
    norm_num
  simpa only [norm_smul,Real.norm_eq_abs,abs_inv,abs_of_pos (hd _),div_eq_mul_inv,mul_comm,
    satelliteDistance,norm_sub_rev,lowNestedOrientation_abs,hJ,mul_one] using hn

end DominantFiveBody
