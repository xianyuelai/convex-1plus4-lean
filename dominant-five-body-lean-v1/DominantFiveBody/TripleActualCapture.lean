import DominantFiveBody.TripleActualCompactness
import DominantFiveBody.CollisionTripleMassLower
import DominantFiveBody.PairActualCapture

/-! # Actual capture of every comparable complete lower triple

All scales, compact bounds and the genuine scalar boundary seed are
derived from the physical normalized configurations. A subsequence of
current mass fractions is selected; individual limiting fractions may
vanish. The fixed exterior angle is obtained by subtracting its current
angle, with no change of the original satellite labels.
-/

noncomputable section
open scoped BigOperators Matrix ContDiff
open Filter Set Topology
namespace DominantFiveBody
open Coorbital
set_option maxHeartbeats 1400000

theorem normalized_complete_lower_triple_regular_actual_capture
    (eps : ℕ → ℝ) (mu : ℕ → MassRatio) (x : ℕ → Configuration)
    (heps : ∀ n, 0 < eps n) (hepst : Tendsto eps atTop (𝓝 0))
    (hm : ∀ n, PositiveRatio (mu n))
    (hx : ∀ n, NormalizedCentralConfiguration (masses (eps n) (mu n)) (x n))
    (hconv : ∀ n, StrictConvexInOrder ⟨Equiv.refl Label, rfl⟩ (x n))
    (r theta : ℕ → Satellite → ℝ) (hr : ∀ n i, 0 < r n i)
    (hpolar : ∀ n, satellitesRelative (x n) = polarSatellites (r n) (theta n))
    (horder : ∀ n i j, i < j → 0 < theta n j - theta n i ∧ theta n j - theta n i < Real.pi)
    (muLimit : MassRatio) (hmt : Tendsto mu atTop (𝓝 muLimit))
    (qLimit : SatelliteConfiguration)
    (hqt : Tendsto (fun n => satellitesRelative (x n)) atTop (𝓝 qLimit))
    (theta0 : Satellite → ℝ) (htheta : Tendsto theta atTop (𝓝 theta0))
    (center : Plane) (htriple : CompleteLimitingSatelliteTriple qLimit 3 center)
    (eta : ℝ) (heta : 0 < eta)
    (hcomparable : ∀ᶠ n in atTop, ∀ i j : TripleLabel, i ≠ j →
      eta * tripleLowDiameter (satellitesRelative (x n)) ≤ satelliteDistance (satellitesRelative (x n)) i.castSucc j.castSucc) :
    ∃ phi : ℕ → ℕ, StrictMono phi ∧
      Nonempty (TripleCapturedBranches (eps ∘ phi)
        (fun n => triplePhysicalScale (mu (phi n)))
        (fun n => triplePhysicalWeights (mu (phi n)))
        (fun n => tripleVariablesFromPolar (triplePhysicalScale (mu (phi n)))
          (triplePhysicalWeights (mu (phi n))) (r (phi n))
          (fun i => theta (phi n) i - theta (phi n) 3)) (-1)) := by
  classical
  let d := fun n => tripleLowDiameter (satellitesRelative (x n))
  let t := fun n => triplePhysicalScale (mu n)
  let nu := fun n => mu n 0 + mu n 1 + mu n 2
  let thetaG := fun n i => theta n i - theta n 3
  have ht (n : ℕ) : 0 < t n := (triplePhysicalParameters_bounds (mu n) (hm n)).1
  have hd (n : ℕ) : 0 < d n := tripleLowDiameter_pos _ (satellitesRelative_collisionFree (x n) (hx n).1)
  have hnuEq (n : ℕ) : triplePhysicalClusterMass (mu n) = nu n := by
    simp [triplePhysicalClusterMass, nu, Fin.sum_univ_three]
  obtain ⟨c, hc, hclower⟩ := normalized_complete_lower_triple_regular_mass_lower eps mu x heps hepst hm hx
    hconv r theta hr hpolar horder muLimit hmt qLimit hqt theta0 htheta center htriple eta heta hcomparable
  obtain ⟨_, M, _, hM, hMinitial⟩ := normalized_complete_lower_triple_initial_scales eps mu x heps hepst hm hx
    hconv r theta hr hpolar horder muLimit hmt qLimit hqt theta0 htheta center htriple
  let k := min c 1
  let H := M + 1
  have hk : 0 < k := lt_min hc (by norm_num)
  have hH : 0 < H := by dsimp [H]; linarith
  have hratio : ∀ᶠ n in atTop, k ≤ t n / d n ∧ t n / d n ≤ H := by
    filter_upwards [hclower, hMinitial] with n hlow hupp
    have he : (t n / d n) ^ 3 = nu n / d n ^ 3 := by
      rw [div_pow]
      dsimp only [t]
      rw [triplePhysicalScale_cube (mu n) (hm n), hnuEq]
    have hmu3 := PositiveRatio.coordinate_le_one (mu n) (hm n) 3
    have hup : nu n / d n ^ 3 ≤ M := hupp.2.2.trans (by nlinarith)
    exact positive_cube_ratio_bounds (t n) (d n) c M (ht n) (hd n) hc hM
      (by rwa [he]) (by rwa [he])
  have hradial := normalized_complete_lower_triple_regular_radial_limits eps mu x heps hepst hm hx
    hconv r theta hr hpolar horder muLimit hmt qLimit hqt theta0 htheta center htriple eta heta hcomparable
  have hradialT (i : Fin 2) : Tendsto (fun n =>
      (r n i.succ.castSucc - r n i.castSucc.castSucc) / t n) atTop (𝓝 0) :=
    zero_div_scale_of_ratio_lower _ t d k hk ht hd (hratio.mono (fun _ hn => hn.1))
      (hradial i.castSucc i.succ)
  obtain ⟨hrt, hunit, hmono, hspanPos, hspan⟩ := normalized_ordered_polar_limit_geometry eps mu x heps hepst hm hx
    r theta hr hpolar horder muLimit hmt qLimit hqt theta0 htheta
  have hrat (i : Satellite) : Tendsto (fun n => r n i) atTop (𝓝 1) :=
    (continuous_apply i).tendsto (fun _ : Satellite => (1 : ℝ)) |>.comp hrt
  have htat (i : Satellite) : Tendsto (fun n => theta n i) atTop (𝓝 (theta0 i)) :=
    (continuous_apply i).tendsto theta0 |>.comp htheta
  have hthetaEq (i j : TripleLabel) : theta0 i.castSucc = theta0 j.castSucc :=
    complete_lower_triple_angles_equal qLimit theta0 hunit hmono hspan center htriple i j
  have hgap0 : theta0 0 - theta0 3 = -h := by
    have he := (normalized_complete_triple_limiting_exterior eps mu x heps hepst hm hx
      r theta hr hpolar horder muLimit hmt qLimit hqt theta0 htheta 3 center htriple).2 0 (by decide)
    rw [abs_of_pos hspanPos] at he
    linarith
  have htG (i : TripleLabel) : Tendsto (fun n => thetaG n i.castSucc) atTop (𝓝 (-h)) := by
    have ht' := (htat i.castSucc).sub (htat 3)
    simpa only [thetaG, hthetaEq i 0,
      show (0 : TripleLabel).castSucc = (0 : Satellite) from rfl, hgap0] using ht'
  have hwidth := normalized_complete_lower_triple_regular_width_limit eps mu x heps hepst hm hx
    hconv r theta hr hpolar horder muLimit hmt qLimit hqt theta0 htheta center htriple eta heta hcomparable
  let gap := fun n (i : Fin 2) => theta n i.succ.castSucc - theta n i.castSucc.castSucc
  let distance := fun n (i : Fin 2) => satelliteDistance (satellitesRelative (x n))
    i.castSucc.castSucc i.succ.castSucc
  have hindices (i : Fin 2) : i.castSucc.castSucc < i.succ.castSucc := by fin_cases i <;> decide
  have hgaplim (i : Fin 2) : Tendsto (fun n => gap n i) atTop (𝓝 0) := by
    simpa only [gap, hthetaEq i.castSucc i.succ, sub_self] using (htat i.succ.castSucc).sub (htat i.castSucc.castSucc)
  have hdefect (i : Fin 2) : Tendsto (fun n => distance n i / d n - gap n i / d n) atTop (𝓝 0) := by
    have hh := polar_scaled_angle_distance_defect
      (fun n => r n i.castSucc.castSucc) (fun n => r n i.succ.castSucc)
      (fun n => theta n i.castSucc.castSucc) (fun n => theta n i.succ.castSucc) d hd
      (hrat i.castSucc.castSucc) (hrat i.succ.castSucc) (hgaplim i)
      (fun n => (horder n _ _ (hindices i)).1.le) (hradial i.castSucc i.succ)
      (fun n => by
        have hd' := tripleLowDiameter_bound (satellitesRelative (x n)) i.succ i.castSucc
        simpa only [d, hpolar, satelliteDistance, polarSatellites] using hd')
    simpa only [distance, gap, satelliteDistance, hpolar, polarSatellites, norm_sub_rev] using hh
  have hmonoN (n : ℕ) : Monotone (theta n) := by
    intro i j hij
    rcases hij.eq_or_lt with rfl | hlt
    · rfl
    · exact sub_nonneg.mp (horder n i j hlt).1.le
  have hgapBounds := regular_scaled_gap_bounds t d (fun n => theta n 2 - theta n 0) gap distance
    ht hd k H eta hk hH heta hratio hwidth
    (fun n i => ⟨(horder n _ _ (hindices i)).1.le, by
      have hlo := hmonoN n (Fin.zero_le i.castSucc.castSucc)
      have hhi := hmonoN n (show i.succ.castSucc ≤ (2 : Satellite) by fin_cases i <;> decide)
      dsimp only [gap]
      linarith⟩)
    (hcomparable.mono (fun n hn i => hn i.castSucc i.succ (by
      intro he; have hv := congrArg (fun j : TripleLabel => j.val) he; simp at hv))) hdefect
  have hnu : Tendsto nu atTop (𝓝 0) := (normalized_complete_lower_triple_mass_vanishes eps mu x
    heps hepst hm hx hconv r theta hr hpolar horder muLimit hmt qLimit hqt theta0 htheta center htriple).1
  have htlim : Tendsto t atTop (𝓝 0) := by
    have hf : t = (fun n => (nu n) ^ ((1 : ℝ) / 3)) := by
      funext n
      dsimp only [t, triplePhysicalScale]
      rw [hnuEq]
      rfl
    rw [hf]
    exact hnu.rpow_const_nhds_zero (p := (1 : ℝ) / 3) (by norm_num)
  have hgapG : ∀ᶠ n in atTop, ∀ i : Fin 2,
      (thetaG n i.succ.castSucc - thetaG n i.castSucc.castSucc) / t n ∈ Icc (eta / (2 * H)) (2 / k) := by
    have he (n : ℕ) (i : Fin 2) :
        (thetaG n i.succ.castSucc - thetaG n i.castSucc.castSucc) / t n = gap n i / t n := by
      dsimp only [thetaG, gap]; ring
    simpa only [he] using hgapBounds
  obtain ⟨phi, alpha0, g, hphi, ha0, hg, halim, hylim⟩ :=
    triple_actual_inverse_coordinates_compact_limits mu hm r thetaG (-h) hrat htG hradialT
      (eta / (2 * H)) (2 / k) (by positivity) hgapG
  refine ⟨phi, hphi, ?_⟩
  have hphys (n : ℕ) := normalized_polar_reindex_sub_constant (eps n) (mu n) (x n)
    (heps n) (hm n) (hx n) (r n) (theta n) (hr n) (hpolar n) (Equiv.refl Satellite) (theta n 3)
  apply triplePhysical_capture_of_regular_scaled_limits alpha0 ha0 g (hg 0) (hg 1) (-1) (Or.inr rfl)
    (eps ∘ phi) (mu ∘ phi) (r ∘ phi) (thetaG ∘ phi)
    (fun n => heps (phi n)) (fun n => hm (phi n)) (fun n => hr (phi n))
    (fun n => sub_self _) (fun n => (hphys (phi n)).1) (fun n => (hphys (phi n)).2)
    (hepst.comp hphi.tendsto_atTop) (htlim.comp hphi.tendsto_atTop) halim
  simpa only [neg_one_mul, Function.comp_def] using hylim

end DominantFiveBody
