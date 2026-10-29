import DominantFiveBody.TripleActualCompactness
import DominantFiveBody.CollisionTripleWidth

/-! Physical geometry and proved scale bounds imply actual triple capture.
This common bridge applies to both endpoint orientations. -/

noncomputable section
open scoped BigOperators Matrix ContDiff
open Filter Set Topology
namespace DominantFiveBody
open Coorbital
set_option maxHeartbeats 1000000

theorem triplePhysical_actual_capture_of_scale_geometry
    (eps : ℕ → ℝ) (mu : ℕ → MassRatio) (r theta : ℕ → Satellite → ℝ)
    (heps : ∀ n, 0 < eps n) (hepst : Tendsto eps atTop (𝓝 0))
    (hm : ∀ n, PositiveRatio (mu n)) (hr : ∀ n i, 0 < r n i)
    (hfixed : ∀ n, theta n 3 = 0)
    (hcf : ∀ n, RelativeCollisionFree (polarSatellites (r n) (theta n)))
    (hphysical : ∀ n, NormalizedCentralConfiguration (masses (eps n) (mu n))
      (centeredFromRelative (eps n) (mu n) (polarSatellites (r n) (theta n))))
    (tau : ℝ) (htau : tau = 1 ∨ tau = -1)
    (hrt : ∀ i, Tendsto (fun n => r n i) atTop (𝓝 1))
    (htt : ∀ i : TripleLabel, Tendsto (fun n => theta n i.castSucc) atTop (𝓝 (tau * h)))
    (htlim : Tendsto (fun n => triplePhysicalScale (mu n)) atTop (𝓝 0))
    (d : ℕ → ℝ) (hd : ∀ n, 0 < d n)
    (k H eta : ℝ) (hk : 0 < k) (hH : 0 < H) (heta : 0 < eta)
    (hratio : ∀ᶠ n in atTop, k ≤ triplePhysicalScale (mu n) / d n ∧
      triplePhysicalScale (mu n) / d n ≤ H)
    (horder : ∀ (n : ℕ) (i j : TripleLabel), i < j → 0 < theta n j.castSucc - theta n i.castSucc)
    (hdiam : ∀ (n : ℕ) (i j : TripleLabel),
      satelliteDistance (polarSatellites (r n) (theta n)) i.castSucc j.castSucc ≤ d n)
    (hcomparable : ∀ᶠ n in atTop, ∀ i j : TripleLabel, i ≠ j →
      eta * d n ≤ satelliteDistance (polarSatellites (r n) (theta n)) i.castSucc j.castSucc)
    (hradial : ∀ i j : TripleLabel, Tendsto (fun n => (r n j.castSucc - r n i.castSucc) / d n)
      atTop (𝓝 0))
    (hwidth : Tendsto (fun n => (theta n 2 - theta n 0) / d n) atTop (𝓝 1)) :
    ∃ phi : ℕ → ℕ, StrictMono phi ∧
      Nonempty (TripleCapturedBranches (eps ∘ phi)
        (fun n => triplePhysicalScale (mu (phi n))) (fun n => triplePhysicalWeights (mu (phi n)))
        (fun n => tripleVariablesFromPolar (triplePhysicalScale (mu (phi n)))
          (triplePhysicalWeights (mu (phi n))) (r (phi n)) (theta (phi n))) tau) := by
  classical
  let t := fun n => triplePhysicalScale (mu n)
  have ht (n : ℕ) : 0 < t n := (triplePhysicalParameters_bounds _ (hm n)).1
  have hradialT (i : Fin 2) : Tendsto (fun n =>
      (r n i.succ.castSucc - r n i.castSucc.castSucc) / t n) atTop (𝓝 0) :=
    zero_div_scale_of_ratio_lower _ t d k hk ht hd (hratio.mono (fun _ hn => hn.1))
      (hradial i.castSucc i.succ)
  let gap := fun n (i : Fin 2) => theta n i.succ.castSucc - theta n i.castSucc.castSucc
  let distance := fun n (i : Fin 2) => satelliteDistance (polarSatellites (r n) (theta n))
    i.castSucc.castSucc i.succ.castSucc
  have hindices (i : Fin 2) : i.castSucc < i.succ := by fin_cases i <;> decide
  have hgaplim (i : Fin 2) : Tendsto (fun n => gap n i) atTop (𝓝 0) := by
    simpa only [gap, sub_self] using (htt i.succ).sub (htt i.castSucc)
  have hdefect (i : Fin 2) : Tendsto (fun n => distance n i / d n - gap n i / d n) atTop (𝓝 0) := by
    have hh := polar_scaled_angle_distance_defect
      (fun n => r n i.castSucc.castSucc) (fun n => r n i.succ.castSucc)
      (fun n => theta n i.castSucc.castSucc) (fun n => theta n i.succ.castSucc) d hd
      (hrt i.castSucc.castSucc) (hrt i.succ.castSucc) (hgaplim i)
      (fun n => (horder n _ _ (hindices i)).le) (hradial i.castSucc i.succ)
      (fun n => hdiam n i.succ i.castSucc)
    simpa only [distance, gap, satelliteDistance, polarSatellites, norm_sub_rev] using hh
  have hmonoN (n : ℕ) : Monotone (fun i : TripleLabel => theta n i.castSucc) := by
    intro i j hij
    rcases hij.eq_or_lt with rfl | hlt
    · rfl
    · exact sub_nonneg.mp (horder n i j hlt).le
  have hgapBounds := regular_scaled_gap_bounds t d (fun n => theta n 2 - theta n 0) gap distance
    ht hd k H eta hk hH heta hratio hwidth
    (fun n i => ⟨(horder n _ _ (hindices i)).le, by
      have hlo := hmonoN n (Fin.zero_le i.castSucc)
      have hhi := hmonoN n (Fin.le_last i.succ)
      change theta n i.succ.castSucc ≤ theta n 2 at hhi
      change theta n 0 ≤ theta n i.castSucc.castSucc at hlo
      dsimp only [gap]
      linarith⟩)
    (hcomparable.mono (fun n hn i => hn i.castSucc i.succ (ne_of_lt (hindices i)))) hdefect
  obtain ⟨phi, alpha0, g, hphi, ha0, hg, halim, hylim⟩ :=
    triple_actual_inverse_coordinates_compact_limits mu hm r theta (tau * h) hrt htt hradialT
      (eta / (2 * H)) (2 / k) (by positivity) hgapBounds
  refine ⟨phi, hphi, ?_⟩
  apply triplePhysical_capture_of_regular_scaled_limits alpha0 ha0 g (hg 0) (hg 1) tau htau
    (eps ∘ phi) (mu ∘ phi) (r ∘ phi) (theta ∘ phi)
    (fun n => heps (phi n)) (fun n => hm (phi n)) (fun n => hr (phi n))
    (fun n => hfixed (phi n)) (fun n => hcf (phi n)) (fun n => hphysical (phi n))
    (hepst.comp hphi.tendsto_atTop) (htlim.comp hphi.tendsto_atTop) halim
  simpa only [Function.comp_def] using hylim

end DominantFiveBody
