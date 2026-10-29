import DominantFiveBody.NestedActualCaptureLimits
import DominantFiveBody.CollisionTripleNestedMacro
import DominantFiveBody.CollisionTripleNestedScale

/-! # Actual lower nested capture after the microscopic scale theorem

All macroscopic coordinates, permutation choices and gauge limits are
derived here. The three microscopic conclusions of Proposition 4.4
are the entry data for the last step.
-/

noncomputable section
open scoped BigOperators Matrix ContDiff
open Filter Set Topology
namespace DominantFiveBody
open Coorbital
set_option maxHeartbeats 1400000

def nestedLowRightPairPermutation : Equiv.Perm Satellite where
  toFun i := ![1, 2, 0, 3] i
  invFun i := ![2, 0, 1, 3] i
  left_inv i := by fin_cases i <;> rfl
  right_inv i := by fin_cases i <;> rfl

theorem normalized_complete_lower_triple_nested_original_capture_of_inner_limits
    (eps : ℕ → ℝ) (mu : ℕ → MassRatio) (x : ℕ → Configuration)
    (heps : ∀ n, 0 < eps n) (hepst : Tendsto eps atTop (𝓝 0))
    (hm : ∀ n, PositiveRatio (mu n))
    (hx : ∀ n, NormalizedCentralConfiguration (masses (eps n) (mu n)) (x n))
    (hconv : ∀ n, StrictConvexInOrder standardHullOrder (x n))
    (r theta : ℕ → Satellite → ℝ) (hr : ∀ n i, 0 < r n i)
    (hpolar : ∀ n, satellitesRelative (x n) = polarSatellites (r n) (theta n))
    (hzero : ∀ n, theta n 0 = 0) (horder : ∀ n, OrderedSemicircle (theta n))
    (muLimit : MassRatio) (hmt : Tendsto mu atTop (𝓝 muLimit))
    (qLimit : SatelliteConfiguration)
    (hqt : Tendsto (fun n => satellitesRelative (x n)) atTop (𝓝 qLimit))
    (theta0 : Satellite → ℝ) (htheta : Tendsto theta atTop (𝓝 theta0))
    (center : Plane) (htriple : CompleteLimitingSatelliteTriple qLimit 3 center)
    (a b c : TripleLabel) (hab : a < b) (hca : c ≠ a) (hcb : c ≠ b)
    (hpair : Tendsto (fun n => satelliteDistance (satellitesRelative (x n)) a.castSucc b.castSucc /
      tripleLowDiameter (satellitesRelative (x n))) atTop (𝓝 0))
    (hinner : Tendsto (fun n => (mu n a.castSucc + mu n b.castSucc) /
      satelliteDistance (satellitesRelative (x n)) a.castSucc b.castSucc ^ 3) atTop (𝓝 (27 / 4 : ℝ)))
    (hrinner : Tendsto (fun n => (r n b.castSucc - r n a.castSucc) /
      satelliteDistance (satellitesRelative (x n)) a.castSucc b.castSucc) atTop (𝓝 0))
    (htinner : Tendsto (fun n => (theta n b.castSucc - theta n a.castSucc) /
      satelliteDistance (satellitesRelative (x n)) a.castSucc b.castSucc) atTop (𝓝 1)) :
    Nonempty (CapturedBranches orderedSliceRoot orderedSliceNondegenerate orderedSliceEndpoint
      (fun n => (⟨mu n, hm n⟩ : PositiveMassRatio)) eps (fun n => polarSlice (r n) (theta n))) := by
  classical
  let d := fun n => tripleLowDiameter (satellitesRelative (x n))
  let s := fun n => satelliteDistance (satellitesRelative (x n)) a.castSucc b.castSucc
  have hd (n : ℕ) : 0 < d n := tripleLowDiameter_pos _ (satellitesRelative_collisionFree _ (hx n).1)
  have hcast : a.castSucc ≠ b.castSucc := by
    intro he
    exact hab.ne (Fin.ext (congrArg (fun i : Satellite => i.val) he))
  have hs (n : ℕ) : 0 < s n := norm_pos_iff.mpr
    (sub_ne_zero.mpr ((satellitesRelative_collisionFree _ (hx n).1).2 _ _ hcast))
  obtain ⟨hadj, _, houterAngle, _, _⟩ := normalized_complete_lower_triple_nested_directions eps mu x
    heps hepst hm hx hconv r theta hr hpolar horder muLimit hmt qLimit hqt theta0 htheta
    center htriple a b c hab hca hcb hpair
  obtain ⟨e, he0, he1, he2, he3⟩ : ∃ e : Equiv.Perm Satellite,
      e 0 = a.castSucc ∧ e 1 = b.castSucc ∧ e 2 = c.castSucc ∧ e 3 = 3 := by
    rcases hadj with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · exact ⟨Equiv.refl Satellite, rfl, rfl, rfl, rfl⟩
    · exact ⟨nestedLowRightPairPermutation, rfl, rfl, rfl, rfl⟩
  have hmacro := normalized_complete_lower_triple_nested_macro_mass_cube_limit eps mu x heps hepst
    hm hx hconv r theta hr hpolar horder muLimit hmt qLimit hqt theta0 htheta center htriple a b c hab hca hcb hpair
  have hradial := normalized_complete_lower_triple_nested_radial_limits eps mu x heps hepst hm hx hconv
    r theta hr hpolar horder muLimit hmt qLimit hqt theta0 htheta center htriple a b c hab.ne hca hcb hpair
  obtain ⟨hrt, hunit, hmono, hspanPos, hspan⟩ := normalized_ordered_polar_limit_geometry eps mu x
    heps hepst hm hx r theta hr hpolar horder muLimit hmt qLimit hqt theta0 htheta
  have hrat (i : Satellite) : Tendsto (fun n => r n i) atTop (𝓝 1) :=
    (continuous_apply i).continuousAt.tendsto.comp hrt
  have htheq (i : TripleLabel) : theta0 i.castSucc = theta0 0 := by
    simpa only [show (0 : TripleLabel).castSucc = (0 : Satellite) from rfl] using
      complete_lower_triple_angles_equal qLimit theta0 hunit hmono hspan center htriple i 0
  have hgap0 : theta0 0 - theta0 3 = -h := by
    have he := (normalized_complete_triple_limiting_exterior eps mu x heps hepst hm hx
      r theta hr hpolar horder muLimit hmt qLimit hqt theta0 htheta 3 center htriple).2 0 (by decide)
    rw [abs_of_pos hspanPos] at he
    linarith
  have hthetaGauge (i : TripleLabel) : Tendsto (fun n => theta n (e i.castSucc) - theta n 3)
      atTop (𝓝 ((-1) * h)) := by
    have hlow : ∃ k : TripleLabel, e i.castSucc = k.castSucc := by
      fin_cases i
      · exact ⟨a, he0⟩
      · exact ⟨b, he1⟩
      · exact ⟨c, he2⟩
    obtain ⟨k, hk⟩ := hlow
    have hi := (continuous_apply k.castSucc).continuousAt.tendsto.comp htheta
    have hp := (continuous_apply (3 : Satellite)).continuousAt.tendsto.comp htheta
    simpa only [hk, htheq k, hgap0, neg_one_mul, Function.comp_def] using hi.sub hp
  have hdt : Tendsto d atTop (𝓝 0) := tripleLowDiameter_tendsto_zero _ qLimit hqt
    (by rw [(htriple 1).mpr (by decide), (htriple 0).mpr (by decide)])
    (by rw [(htriple 2).mpr (by decide), (htriple 0).mpr (by decide)])
  have hmacroE : Tendsto (fun n => triplePhysicalClusterMass (mu n ∘ e) / d n ^ 3)
      atTop (𝓝 tripleD0) := by
    have he (n : ℕ) : triplePhysicalClusterMass (mu n ∘ e) = mu n 0 + mu n 1 + mu n 2 := by
      simp only [triplePhysicalClusterMass, Fin.sum_univ_three, Function.comp_apply]
      change mu n (e 0) + mu n (e 1) + mu n (e 2) = _
      rw [he0, he1, he2]
      exact three_distinct_low_masses_sum _ a b c hab.ne hca hcb
    simpa only [he, d, tripleD0] using hmacro
  have hinnerE : Tendsto (fun n => nestedPhysicalInnerMass (mu n ∘ e) / s n ^ 3)
      atTop (𝓝 (3 * tripleD0)) := by
    simpa only [nestedPhysicalInnerMass, Function.comp_apply, he0, he1, s,
      tripleD0, show (3 : ℝ) * (9 / 4) = 27 / 4 by norm_num] using hinner
  have hw : lowNestedOrientation a c = 1 ∨ lowNestedOrientation a c = -1 := by
    unfold lowNestedOrientation
    split_ifs <;> simp
  apply nested_original_ordered_capture_of_cubic_geometry (-1) (lowNestedOrientation a c)
    (Or.inr rfl) hw eps mu x heps hepst hm hx r theta hr hpolar hzero horder e 3 he3 d s hd hs
    hdt hpair hmacroE hinnerE hrat hthetaGauge
    (by simpa only [he2, he0, d] using hradial a c)
    (by simpa only [he2, he1, d] using hradial b c)
    (by simpa only [he2, he0, d] using houterAngle a (Finset.mem_insert_self _ _))
    (by simpa only [he2, he1, d] using houterAngle b (Finset.mem_insert_of_mem (Finset.mem_singleton_self _)))
    (by simpa only [he1, he0, s] using hrinner)
  simpa only [he1, he0, s] using htinner

theorem normalized_complete_lower_triple_nested_original_capture
    (eps : ℕ → ℝ) (mu : ℕ → MassRatio) (x : ℕ → Configuration)
    (heps : ∀ n, 0 < eps n) (hepst : Tendsto eps atTop (𝓝 0))
    (hm : ∀ n, PositiveRatio (mu n))
    (hx : ∀ n, NormalizedCentralConfiguration (masses (eps n) (mu n)) (x n))
    (hconv : ∀ n, StrictConvexInOrder standardHullOrder (x n))
    (r theta : ℕ → Satellite → ℝ) (hr : ∀ n i, 0 < r n i)
    (hpolar : ∀ n, satellitesRelative (x n) = polarSatellites (r n) (theta n))
    (hzero : ∀ n, theta n 0 = 0) (horder : ∀ n, OrderedSemicircle (theta n))
    (muLimit : MassRatio) (hmt : Tendsto mu atTop (𝓝 muLimit))
    (qLimit : SatelliteConfiguration)
    (hqt : Tendsto (fun n => satellitesRelative (x n)) atTop (𝓝 qLimit))
    (theta0 : Satellite → ℝ) (htheta : Tendsto theta atTop (𝓝 theta0))
    (center : Plane) (htriple : CompleteLimitingSatelliteTriple qLimit 3 center)
    (a b c : TripleLabel) (hab : a < b) (hca : c ≠ a) (hcb : c ≠ b)
    (hpair : Tendsto (fun n => satelliteDistance (satellitesRelative (x n)) a.castSucc b.castSucc /
      tripleLowDiameter (satellitesRelative (x n))) atTop (𝓝 0)) :
    Nonempty (CapturedBranches orderedSliceRoot orderedSliceNondegenerate orderedSliceEndpoint
      (fun n => (⟨mu n, hm n⟩ : PositiveMassRatio)) eps (fun n => polarSlice (r n) (theta n))) := by
  have hprecise := normalized_complete_lower_triple_nested_precise_scales eps mu x heps hepst hm hx
    hconv r theta hr hpolar horder muLimit hmt qLimit hqt theta0 htheta center htriple a b c hab hca hcb hpair
  exact normalized_complete_lower_triple_nested_original_capture_of_inner_limits eps mu x heps hepst hm hx
    hconv r theta hr hpolar hzero horder muLimit hmt qLimit hqt theta0 htheta center htriple a b c hab hca hcb
    hpair hprecise.2.2.2.2.1 hprecise.2.2.2.1 hprecise.2.2.1

end DominantFiveBody
