import DominantFiveBody.TriplePhysicalCaptureGeometry
import DominantFiveBody.CollisionUpperTriple
import DominantFiveBody.CollisionTripleMassLower
import DominantFiveBody.PairActualCapture

/-! # Actual upper triple capture with original physical labels

Reflection and reversed labels prove estimates only. The capture below
uses the actual physical sequence in the order (1,2,3,0), with positive
internal angular gaps and the genuine tau=+1 chart. Reflection is never
added to the final similarity relation.
-/

noncomputable section
open scoped BigOperators Matrix ContDiff
open Filter Set Topology
namespace DominantFiveBody
open Coorbital
set_option maxHeartbeats 1400000

def upperTripleChartPermutation : Equiv.Perm Satellite where
  toFun i := i + 1
  invFun i := i - 1
  left_inv i := by fin_cases i <;> rfl
  right_inv i := by fin_cases i <;> rfl

@[simp] theorem upperTripleChartPermutation_low (i : TripleLabel) :
    upperTripleChartPermutation i.castSucc = i.succ := by fin_cases i <;> rfl

@[simp] theorem upperTripleChartPermutation_exterior :
    upperTripleChartPermutation 3 = 0 := rfl

theorem normalized_complete_upper_triple_regular_actual_capture
    (eps : ℕ → ℝ) (mu : ℕ → MassRatio) (x : ℕ → Configuration)
    (heps : ∀ n, 0 < eps n) (hepst : Tendsto eps atTop (𝓝 0))
    (hm : ∀ n, PositiveRatio (mu n))
    (hx : ∀ n, NormalizedCentralConfiguration (masses (eps n) (mu n)) (x n))
    (hconv : ∀ n, StrictConvexInOrder standardHullOrder (x n))
    (r theta : ℕ → Satellite → ℝ) (hr : ∀ n i, 0 < r n i)
    (hpolar : ∀ n, satellitesRelative (x n) = polarSatellites (r n) (theta n))
    (horder : ∀ n, OrderedSemicircle (theta n))
    (muLimit : MassRatio) (hmt : Tendsto mu atTop (𝓝 muLimit))
    (qLimit : SatelliteConfiguration)
    (hqt : Tendsto (fun n => satellitesRelative (x n)) atTop (𝓝 qLimit))
    (theta0 : Satellite → ℝ) (htheta : Tendsto theta atTop (𝓝 theta0))
    (center : Plane) (htriple : CompleteLimitingSatelliteTriple qLimit 0 center)
    (eta : ℝ) (heta : 0 < eta)
    (hcomparable : ∀ᶠ n in atTop, ∀ i j : TripleLabel, i ≠ j →
      eta * tripleHighDiameter (satellitesRelative (x n)) ≤
        satelliteDistance (satellitesRelative (x n)) i.succ j.succ) :
    ∃ phi : ℕ → ℕ, StrictMono phi ∧
      Nonempty (TripleCapturedBranches (eps ∘ phi)
        (fun n => triplePhysicalScale (mu (phi n) ∘ upperTripleChartPermutation))
        (fun n => triplePhysicalWeights (mu (phi n) ∘ upperTripleChartPermutation))
        (fun n => tripleVariablesFromPolar (triplePhysicalScale (mu (phi n) ∘ upperTripleChartPermutation))
          (triplePhysicalWeights (mu (phi n) ∘ upperTripleChartPermutation))
          (r (phi n) ∘ upperTripleChartPermutation)
          (fun i => theta (phi n) (upperTripleChartPermutation i) - theta (phi n) 0)) 1) := by
  classical
  let e := upperTripleChartPermutation
  let d := fun n => tripleHighDiameter (satellitesRelative (x n))
  let t := fun n => triplePhysicalScale (mu n ∘ e)
  let nu := fun n => mu n 1 + mu n 2 + mu n 3
  let thetaG := fun n i => theta n (e i) - theta n 0
  have hme (n : ℕ) := positiveRatio_satellitePermutation _ (hm n) e
  have ht (n : ℕ) : 0 < t n := (triplePhysicalParameters_bounds _ (hme n)).1
  have hnuEq (n : ℕ) : triplePhysicalClusterMass (mu n ∘ e) = nu n := by
    simp [triplePhysicalClusterMass, Fin.sum_univ_three, Function.comp_apply,
      e, upperTripleChartPermutation_low, nu]
  have hrev (i : TripleLabel) : (i.castSucc : Satellite).rev = i.rev.succ := by fin_cases i <;> rfl
  have hd (n : ℕ) : 0 < d n := by
    change 0 < tripleHighDiameter (satellitesRelative (x n))
    rw [← tripleLowDiameter_mirror]
    exact tripleLowDiameter_pos _ (satellitesRelative_collisionFree _
      (mirrorConfiguration_normalized _ _ _ (hx n)).1)
  have hmt' : Tendsto (fun n => mu n ∘ Fin.revPerm) atTop (𝓝 (muLimit ∘ Fin.revPerm)) := by
    apply tendsto_pi_nhds.mpr
    intro i
    exact (continuous_apply i.rev).continuousAt.tendsto.comp hmt
  have htt' : Tendsto (fun n i => -theta n (Fin.rev i)) atTop (𝓝 (fun i => -theta0 (Fin.rev i))) := by
    apply tendsto_pi_nhds.mpr
    intro i
    exact ((continuous_apply i.rev).continuousAt.tendsto.comp htheta).neg
  have hcomp' : ∀ᶠ n in atTop, ∀ i j : TripleLabel, i ≠ j →
      eta * tripleLowDiameter (satellitesRelative (mirrorConfiguration (x n))) ≤
        satelliteDistance (satellitesRelative (mirrorConfiguration (x n))) i.castSucc j.castSucc := by
    filter_upwards [hcomparable] with n hn
    intro i j hij
    rw [tripleLowDiameter_mirror, mirrorConfiguration_pairDistance, hrev, hrev]
    exact hn i.rev j.rev (Fin.rev_injective.ne hij)
  obtain ⟨c, hc, hclower⟩ := normalized_complete_lower_triple_regular_mass_lower eps
    (fun n => mu n ∘ Fin.revPerm) (fun n => mirrorConfiguration (x n)) heps hepst
    (fun n => positiveRatio_satellitePermutation _ (hm n) Fin.revPerm)
    (fun n => mirrorConfiguration_normalized _ _ _ (hx n))
    (fun n => mirrorConfiguration_strictConvex _ (hconv n))
    (fun n => r n ∘ Fin.revPerm) (fun n i => -theta n (Fin.rev i))
    (fun n i => hr n i.rev) (fun n => mirrorConfiguration_polar _ _ _ (hpolar n))
    (fun n => mirrorAngles_ordered _ (horder n)) (muLimit ∘ Fin.revPerm) hmt'
    (fun i => planeReflection (qLimit (Fin.rev i))) (mirrorConfiguration_relative_limit x qLimit hqt)
    (fun i => -theta0 (Fin.rev i)) htt' (planeReflection center)
    (complete_upper_triple_mirror qLimit center htriple) eta heta hcomp'
  have hnuMirror := (normalized_complete_lower_triple_mass_vanishes eps
    (fun n => mu n ∘ Fin.revPerm) (fun n => mirrorConfiguration (x n)) heps hepst
    (fun n => positiveRatio_satellitePermutation _ (hm n) Fin.revPerm)
    (fun n => mirrorConfiguration_normalized _ _ _ (hx n))
    (fun n => mirrorConfiguration_strictConvex _ (hconv n))
    (fun n => r n ∘ Fin.revPerm) (fun n i => -theta n (Fin.rev i))
    (fun n i => hr n i.rev) (fun n => mirrorConfiguration_polar _ _ _ (hpolar n))
    (fun n => mirrorAngles_ordered _ (horder n)) (muLimit ∘ Fin.revPerm) hmt'
    (fun i => planeReflection (qLimit (Fin.rev i))) (mirrorConfiguration_relative_limit x qLimit hqt)
    (fun i => -theta0 (Fin.rev i)) htt' (planeReflection center)
    (complete_upper_triple_mirror qLimit center htriple)).1
  have hnu : Tendsto nu atTop (𝓝 0) := by
    convert! hnuMirror using 1
    funext n
    simp only [nu, Function.comp_apply, Fin.revPerm_apply]
    change mu n 1 + mu n 2 + mu n 3 = mu n 3 + mu n 2 + mu n 1
    ring
  have htlim : Tendsto t atTop (𝓝 0) := by
    have hf : t = (fun n => nu n ^ ((1 : ℝ) / 3)) := by
      funext n
      dsimp only [t, triplePhysicalScale]
      rw [hnuEq]
      rfl
    rw [hf]
    exact hnu.rpow_const_nhds_zero (p := (1 : ℝ) / 3) (by norm_num)
  obtain ⟨_, M, _, hM, hMinitial⟩ := normalized_complete_upper_triple_initial_scales eps mu x
    heps hepst hm hx hconv r theta hr hpolar horder muLimit hmt qLimit hqt theta0 htheta center htriple
  let k := min c 1
  let H := M + 1
  have hk : 0 < k := lt_min hc (by norm_num)
  have hH : 0 < H := by dsimp [H]; linarith
  have hratio : ∀ᶠ n in atTop, k ≤ t n / d n ∧ t n / d n ≤ H := by
    filter_upwards [hclower, hMinitial] with n hlow hupp
    have hl : c ≤ nu n / d n ^ 3 := by
      rw [tripleLowDiameter_mirror] at hlow
      convert! hlow using 1
      simp only [nu, d, Function.comp_apply, Fin.revPerm_apply]
      congr 1
      change mu n 1 + mu n 2 + mu n 3 = mu n 3 + mu n 2 + mu n 1
      ring
    have hup : nu n / d n ^ 3 ≤ M := hupp.2.2.trans (by
      have hh := PositiveRatio.coordinate_le_one (mu n) (hm n) 0
      nlinarith)
    have he : (t n / d n) ^ 3 = nu n / d n ^ 3 := by
      rw [div_pow]
      dsimp only [t]
      rw [triplePhysicalScale_cube _ (hme n), hnuEq]
    exact positive_cube_ratio_bounds _ _ c M (ht n) (hd n) hc hM (by rwa [he]) (by rwa [he])
  obtain ⟨hradial, hwidth⟩ := normalized_complete_upper_triple_regular_geometry eps mu x
    heps hepst hm hx hconv r theta hr hpolar horder muLimit hmt qLimit hqt theta0 htheta center htriple eta heta hcomparable
  obtain ⟨hrt, hunit, hmono, _, hspan⟩ := normalized_ordered_polar_limit_geometry eps mu x
    heps hepst hm hx r theta hr hpolar horder muLimit hmt qLimit hqt theta0 htheta
  have hrat (i : Satellite) : Tendsto (fun n => (r n ∘ e) i) atTop (𝓝 1) :=
    (continuous_apply (e i)).tendsto (fun _ : Satellite => (1 : ℝ)) |>.comp hrt
  have hthetaEq (i : TripleLabel) : theta0 i.succ = theta0 1 := by
    apply (unit_ordered_limit_equal_iff qLimit theta0 hunit hmono hspan i.succ 1).mp
    rw [(htriple i.succ).mpr (by exact Fin.succ_ne_zero i), (htriple 1).mpr (by decide)]
  have hgap0 : theta0 1 - theta0 0 = h := by
    have he := (normalized_complete_triple_limiting_exterior eps mu x heps hepst hm hx
      r theta hr hpolar horder muLimit hmt qLimit hqt theta0 htheta 0 center htriple).2 1 (by decide)
    rw [abs_of_nonpos (sub_nonpos.mpr (hmono (by decide : (0 : Satellite) ≤ 1)))] at he
    linarith
  have htt (i : TripleLabel) : Tendsto (fun n => thetaG n i.castSucc) atTop (𝓝 (1 * h)) := by
    have hi := (continuous_apply i.succ).tendsto theta0 |>.comp htheta
    have h0 := (continuous_apply (0 : Satellite)).tendsto theta0 |>.comp htheta
    simpa only [thetaG, e, upperTripleChartPermutation_low, hthetaEq i, hgap0, one_mul,
      Function.comp_def] using hi.sub h0
  have hphys (n : ℕ) := normalized_polar_reindex_sub_constant (eps n) (mu n) (x n)
    (heps n) (hm n) (hx n) (r n) (theta n) (hr n) (hpolar n) e (theta n 0)
  have hdistance (n : ℕ) (i j : TripleLabel) :
      satelliteDistance (polarSatellites (r n ∘ e) (thetaG n)) i.castSucc j.castSucc =
        satelliteDistance (satellitesRelative (x n)) i.succ j.succ := by
    rw [satelliteDistance_polar_sub_constant]
    simp only [hpolar, satelliteDistance, polarSatellites, Function.comp_apply, e,
      upperTripleChartPermutation_low]
  apply triplePhysical_actual_capture_of_scale_geometry eps (fun n => mu n ∘ e) (fun n => r n ∘ e)
    thetaG heps hepst hme (fun n i => hr n (e i))
    (fun n => by simp only [thetaG, e, upperTripleChartPermutation_exterior, sub_self])
    (fun n => (hphys n).1) (fun n => (hphys n).2) 1 (Or.inl rfl) hrat htt htlim
    d hd k H eta hk hH heta hratio
    (fun n i j hij => by
      simpa only [thetaG, e, upperTripleChartPermutation_low, sub_sub_sub_cancel_right] using
        (horder n i.succ j.succ (Fin.succ_lt_succ_iff.mpr hij)).1)
    (fun n i j => by
      rw [hdistance]
      have hh := tripleLowDiameter_bound (satellitesRelative (mirrorConfiguration (x n))) i.rev j.rev
      simpa only [tripleLowDiameter_mirror, mirrorConfiguration_pairDistance, hrev, Fin.rev_rev] using hh)
    (hcomparable.mono (fun n hn i j hij => by rw [hdistance]; exact hn i j hij))
    (fun i j => by simpa only [Function.comp_apply, e, upperTripleChartPermutation_low] using hradial i j)
  simpa only [thetaG, e, show upperTripleChartPermutation (2 : Satellite) = 3 from rfl,
    show upperTripleChartPermutation (0 : Satellite) = 1 from rfl,
    sub_sub_sub_cancel_right, d] using hwidth

end DominantFiveBody
