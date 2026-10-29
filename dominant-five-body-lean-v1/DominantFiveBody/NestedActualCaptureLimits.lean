import DominantFiveBody.PairActualCapture
import DominantFiveBody.NestedSequenceCapture
import DominantFiveBody.NestedOriginalOrderedCapture
import DominantFiveBody.OrderedSliceSequences

/-! # Actual nested scales in the physical inverse coordinates

The two positive cubic mass limits determine the actual scale factors.
All weighted means use current fractions; no convergence of alpha is
assumed. Subsequence selection of alpha takes place only at capture.
-/

noncomputable section
open scoped BigOperators Matrix ContDiff
open Filter Set Topology
namespace DominantFiveBody
open Coorbital
set_option maxHeartbeats 1400000

theorem nestedPhysicalScale_mul_eta (mu : MassRatio) (hm : PositiveRatio mu) :
    nestedPhysicalScale mu * nestedPhysicalEta mu =
      (nestedPhysicalInnerMass mu) ^ ((1 : ℝ) / 3) := by
  have hnu := triplePhysicalClusterMass_pos mu hm
  have hxi := nestedPhysicalInnerMass_pos mu hm
  unfold nestedPhysicalScale triplePhysicalScale nestedPhysicalEta
  change (triplePhysicalClusterMass mu) ^ ((1 : ℝ) / 3) *
    (nestedPhysicalInnerMass mu / triplePhysicalClusterMass mu) ^ ((1 : ℝ) / 3) = _
  rw [← Real.mul_rpow hnu.le (div_pos hxi hnu).le]
  congr 1
  field_simp

theorem positive_two_scale_fraction_identity (xi nu s d : ℝ)
    (hs : 0 < s) (hd : 0 < d) (hnu : 0 < nu) :
    xi / nu = ((xi / s ^ 3) / (nu / d ^ 3)) * (s / d) ^ 3 := by
  field_simp [hs.ne', hd.ne', hnu.ne']

theorem nestedVariablesFromPolar_tendsto_of_cubic_geometry
    (mu : ℕ → MassRatio) (hm : ∀ n, PositiveRatio (mu n))
    (r theta : ℕ → Satellite → ℝ) (psi omega : ℝ)
    (d s : ℕ → ℝ) (hd : ∀ n, 0 < d n) (hs : ∀ n, 0 < s n)
    (hdt : Tendsto d atTop (𝓝 0)) (hsd : Tendsto (fun n => s n / d n) atTop (𝓝 0))
    (hmacro : Tendsto (fun n => triplePhysicalClusterMass (mu n) / d n ^ 3) atTop (𝓝 tripleD0))
    (hinner : Tendsto (fun n => nestedPhysicalInnerMass (mu n) / s n ^ 3) atTop (𝓝 (3 * tripleD0)))
    (hrt : ∀ i, Tendsto (fun n => r n i) atTop (𝓝 1))
    (htt : ∀ i : TripleLabel, Tendsto (fun n => theta n i.castSucc) atTop (𝓝 psi))
    (hr02 : Tendsto (fun n => (r n 2 - r n 0) / d n) atTop (𝓝 0))
    (hr12 : Tendsto (fun n => (r n 2 - r n 1) / d n) atTop (𝓝 0))
    (ht02 : Tendsto (fun n => (theta n 2 - theta n 0) / d n) atTop (𝓝 omega))
    (ht12 : Tendsto (fun n => (theta n 2 - theta n 1) / d n) atTop (𝓝 omega))
    (hr01 : Tendsto (fun n => (r n 1 - r n 0) / s n) atTop (𝓝 0))
    (ht01 : Tendsto (fun n => (theta n 1 - theta n 0) / s n) atTop (𝓝 1)) :
    Tendsto (fun n => nestedPhysicalScale (mu n)) atTop (𝓝 0) ∧
      Tendsto (fun n => nestedPhysicalEta (mu n)) atTop (𝓝 0) ∧
      Tendsto (fun n => nestedVariablesFromPolar (nestedPhysicalScale (mu n))
        (nestedPhysicalEta (mu n)) (nestedPhysicalAlpha (mu n)) (r n) (theta n)) atTop
        (𝓝 (nestedBasePoint psi omega)) := by
  let nu := fun n => triplePhysicalClusterMass (mu n)
  let xi := fun n => nestedPhysicalInnerMass (mu n)
  let t := fun n => nestedPhysicalScale (mu n)
  let eta := fun n => nestedPhysicalEta (mu n)
  let alpha := fun n => nestedPhysicalAlpha (mu n)
  have hnu (n : ℕ) : 0 < nu n := triplePhysicalClusterMass_pos _ (hm n)
  have hxi (n : ℕ) : 0 < xi n := nestedPhysicalInnerMass_pos _ (hm n)
  have ha (n : ℕ) : 0 < alpha n ∧ alpha n < 1 := (nestedPhysicalParameters_bounds _ (hm n)).2.2.2.2
  have he (n : ℕ) : 0 < eta n ∧ eta n < 1 :=
    ⟨(nestedPhysicalParameters_bounds _ (hm n)).2.2.1,
      (nestedPhysicalParameters_bounds _ (hm n)).2.2.2.1⟩
  have hnut : Tendsto nu atTop (𝓝 0) := by
    have hh := hmacro.mul (hdt.pow 3)
    convert! hh using 1
    · funext n
      dsimp only [nu]
      field_simp [(hd n).ne']
    · norm_num
  have htlim : Tendsto t atTop (𝓝 0) := by
    have hf : t = (fun n => nu n ^ ((1 : ℝ) / 3)) := by
      funext n; rfl
    rw [hf]
    exact hnut.rpow_const_nhds_zero (p := (1 : ℝ) / 3) (by norm_num)
  have hfrac : Tendsto (fun n => xi n / nu n) atTop (𝓝 0) := by
    have hh := (hinner.div hmacro tripleD0_pos.ne').mul (hsd.pow 3)
    convert! hh using 1
    · funext n
      exact positive_two_scale_fraction_identity _ _ _ _ (hs n) (hd n) (hnu n)
    · norm_num
  have hetalim : Tendsto eta atTop (𝓝 0) := by
    have hf : eta = (fun n => (xi n / nu n) ^ ((1 : ℝ) / 3)) := by
      funext n; rfl
    rw [hf]
    exact hfrac.rpow_const_nhds_zero (p := (1 : ℝ) / 3) (by norm_num)
  have hDt : Tendsto (fun n => d n / t n) atTop (𝓝 (pairBoundaryScale tripleD0)) :=
    pair_positive_cube_scale_tendsto nu d tripleD0 hnu hd tripleD0_pos hmacro
  have hSt : Tendsto (fun n => s n / (t n * eta n)) atTop (𝓝 (pairBoundaryScale (3 * tripleD0))) := by
    simpa only [t, eta, nestedPhysicalScale_mul_eta _ (hm _)] using
      pair_positive_cube_scale_tendsto xi s (3 * tripleD0) hxi hs
        (mul_pos (by norm_num : (0 : ℝ) < 3) tripleD0_pos) hinner
  have hr0t : Tendsto (fun n => (r n 2 - r n 0) / t n) atTop (𝓝 0) := by
    convert! hr02.mul hDt using 1
    · funext n; field_simp [(hd n).ne']
    · ring
  have hr1t : Tendsto (fun n => (r n 2 - r n 1) / t n) atTop (𝓝 0) := by
    convert! hr12.mul hDt using 1
    · funext n; field_simp [(hd n).ne']
    · ring
  have ht0t : Tendsto (fun n => (theta n 2 - theta n 0) / t n) atTop (𝓝 (omega * pairBoundaryScale tripleD0)) := by
    convert! ht02.mul hDt using 1
    funext n; field_simp [(hd n).ne']
  have ht1t : Tendsto (fun n => (theta n 2 - theta n 1) / t n) atTop (𝓝 (omega * pairBoundaryScale tripleD0)) := by
    convert! ht12.mul hDt using 1
    funext n; field_simp [(hd n).ne']
  have hu : Tendsto (fun n => nestedRowOuterDifference (t n) (alpha n) (r n)) atTop (𝓝 0) := by
    have hh := current_unit_interval_combination_tendsto alpha _ _ 0 ha hr0t hr1t
    convert! hh using 1
    funext n; unfold nestedRowOuterDifference nestedPairAverage; ring
  have hZ : Tendsto (fun n => nestedRowOuterDifference (t n) (alpha n) (theta n))
      atTop (𝓝 (omega * pairBoundaryScale tripleD0)) := by
    have hh := current_unit_interval_combination_tendsto alpha _ _ _ ha ht0t ht1t
    convert! hh using 1
    funext n; unfold nestedRowOuterDifference nestedPairAverage; ring
  have hv : Tendsto (fun n => nestedRowInnerDifference (t n) (eta n) (r n)) atTop (𝓝 0) := by
    convert! hr01.mul hSt using 1
    · funext n; unfold nestedRowInnerDifference; field_simp [(hs n).ne']
    · ring
  have hz : Tendsto (fun n => nestedRowInnerDifference (t n) (eta n) (theta n))
      atTop (𝓝 (pairBoundaryScale (3 * tripleD0))) := by
    convert! ht01.mul hSt using 1
    · funext n; unfold nestedRowInnerDifference; field_simp [(hs n).ne']
    · ring
  have hRpair : Tendsto (fun n => nestedPairAverage (alpha n) (r n)) atTop (𝓝 1) :=
    current_unit_interval_combination_tendsto alpha _ _ 1 ha (hrt 0) (hrt 1)
  have hPpair : Tendsto (fun n => nestedPairAverage (alpha n) (theta n)) atTop (𝓝 psi) :=
    current_unit_interval_combination_tendsto alpha _ _ psi ha (htt 0) (htt 1)
  have hR : Tendsto (fun n => nestedRowAverage (eta n) (alpha n) (r n)) atTop (𝓝 1) := by
    exact current_unit_interval_combination_tendsto (fun n => eta n ^ 3) _ _ 1
      (fun n => ⟨pow_pos (he n).1 3, pow_lt_one₀ (he n).1.le (he n).2 (by decide)⟩) hRpair (hrt 2)
  have hP : Tendsto (fun n => nestedRowAverage (eta n) (alpha n) (theta n)) atTop (𝓝 psi) := by
    exact current_unit_interval_combination_tendsto (fun n => eta n ^ 3) _ _ psi
      (fun n => ⟨pow_pos (he n).1 3, pow_lt_one₀ (he n).1.le (he n).2 (by decide)⟩) hPpair (htt 2)
  refine ⟨htlim, hetalim, ?_⟩
  apply tendsto_pi_nhds.mpr
  intro i
  fin_cases i
  all_goals simp only [nestedVariablesFromPolar_eq, nestedBasePoint, nestedUnitPoint]
  · exact hrt 3
  · exact hR
  · exact hu
  · exact hv
  · exact hP
  · exact hZ
  · exact hz

theorem nestedPhysical_actual_capture_of_cubic_geometry
    (tau omega : ℝ) (htau : tau = 1 ∨ tau = -1) (homega : omega = 1 ∨ omega = -1)
    (eps : ℕ → ℝ) (mu : ℕ → MassRatio) (r theta : ℕ → Satellite → ℝ)
    (heps : ∀ n, 0 < eps n) (hepst : Tendsto eps atTop (𝓝 0))
    (hm : ∀ n, PositiveRatio (mu n)) (hr : ∀ n i, 0 < r n i) (hfixed : ∀ n, theta n 3 = 0)
    (hcf : ∀ n, RelativeCollisionFree (polarSatellites (r n) (theta n)))
    (hphysical : ∀ n, NormalizedCentralConfiguration (masses (eps n) (mu n))
      (centeredFromRelative (eps n) (mu n) (polarSatellites (r n) (theta n))))
    (d s : ℕ → ℝ) (hd : ∀ n, 0 < d n) (hs : ∀ n, 0 < s n)
    (hdt : Tendsto d atTop (𝓝 0)) (hsd : Tendsto (fun n => s n / d n) atTop (𝓝 0))
    (hmacro : Tendsto (fun n => triplePhysicalClusterMass (mu n) / d n ^ 3) atTop (𝓝 tripleD0))
    (hinner : Tendsto (fun n => nestedPhysicalInnerMass (mu n) / s n ^ 3) atTop (𝓝 (3 * tripleD0)))
    (hrt : ∀ i, Tendsto (fun n => r n i) atTop (𝓝 1))
    (htt : ∀ i : TripleLabel, Tendsto (fun n => theta n i.castSucc) atTop (𝓝 (tau * h)))
    (hr02 : Tendsto (fun n => (r n 2 - r n 0) / d n) atTop (𝓝 0))
    (hr12 : Tendsto (fun n => (r n 2 - r n 1) / d n) atTop (𝓝 0))
    (ht02 : Tendsto (fun n => (theta n 2 - theta n 0) / d n) atTop (𝓝 omega))
    (ht12 : Tendsto (fun n => (theta n 2 - theta n 1) / d n) atTop (𝓝 omega))
    (hr01 : Tendsto (fun n => (r n 1 - r n 0) / s n) atTop (𝓝 0))
    (ht01 : Tendsto (fun n => (theta n 1 - theta n 0) / s n) atTop (𝓝 1)) :
    ∃ phi : ℕ → ℕ, StrictMono phi ∧
      Nonempty (NestedCapturedBranches (eps ∘ phi)
        (fun n => nestedPhysicalScale (mu (phi n))) (fun n => nestedPhysicalEta (mu (phi n)))
        (fun n => nestedPhysicalAlpha (mu (phi n)))
        (fun n => nestedVariablesFromPolar (nestedPhysicalScale (mu (phi n)))
          (nestedPhysicalEta (mu (phi n))) (nestedPhysicalAlpha (mu (phi n)))
          (r (phi n)) (theta (phi n))) tau omega) := by
  obtain ⟨ht, he, hy⟩ := nestedVariablesFromPolar_tendsto_of_cubic_geometry mu hm r theta (tau * h) omega
    d s hd hs hdt hsd hmacro hinner hrt htt hr02 hr12 ht02 ht12 hr01 ht01
  obtain ⟨_, _, phi, hphi, hc⟩ := nestedPhysical_subsequence_capture_of_scaled_limits tau omega
    htau homega eps mu r theta heps hm hr hfixed hcf hphysical hepst ht he hy
  exact ⟨phi, hphi, by simpa only [Function.comp_def] using hc⟩

theorem nested_original_ordered_capture_of_cubic_geometry
    (tau omega : ℝ) (htau : tau = 1 ∨ tau = -1) (homega : omega = 1 ∨ omega = -1)
    (eps : ℕ → ℝ) (mu : ℕ → MassRatio) (x : ℕ → Configuration)
    (heps : ∀ n, 0 < eps n) (hepst : Tendsto eps atTop (𝓝 0))
    (hm : ∀ n, PositiveRatio (mu n))
    (hx : ∀ n, NormalizedCentralConfiguration (masses (eps n) (mu n)) (x n))
    (r theta : ℕ → Satellite → ℝ) (hr : ∀ n i, 0 < r n i)
    (hpolar : ∀ n, satellitesRelative (x n) = polarSatellites (r n) (theta n))
    (hzero : ∀ n, theta n 0 = 0) (horder : ∀ n, OrderedSemicircle (theta n))
    (e : Equiv.Perm Satellite) (anchor : Satellite) (heanchor : e 3 = anchor)
    (d s : ℕ → ℝ) (hd : ∀ n, 0 < d n) (hs : ∀ n, 0 < s n)
    (hdt : Tendsto d atTop (𝓝 0)) (hsd : Tendsto (fun n => s n / d n) atTop (𝓝 0))
    (hmacro : Tendsto (fun n => triplePhysicalClusterMass (mu n ∘ e) / d n ^ 3) atTop (𝓝 tripleD0))
    (hinner : Tendsto (fun n => nestedPhysicalInnerMass (mu n ∘ e) / s n ^ 3) atTop (𝓝 (3 * tripleD0)))
    (hrt : ∀ i, Tendsto (fun n => r n i) atTop (𝓝 1))
    (htt : ∀ i : TripleLabel, Tendsto (fun n => theta n (e i.castSucc) - theta n anchor)
      atTop (𝓝 (tau * h)))
    (hr02 : Tendsto (fun n => (r n (e 2) - r n (e 0)) / d n) atTop (𝓝 0))
    (hr12 : Tendsto (fun n => (r n (e 2) - r n (e 1)) / d n) atTop (𝓝 0))
    (ht02 : Tendsto (fun n => (theta n (e 2) - theta n (e 0)) / d n) atTop (𝓝 omega))
    (ht12 : Tendsto (fun n => (theta n (e 2) - theta n (e 1)) / d n) atTop (𝓝 omega))
    (hr01 : Tendsto (fun n => (r n (e 1) - r n (e 0)) / s n) atTop (𝓝 0))
    (ht01 : Tendsto (fun n => (theta n (e 1) - theta n (e 0)) / s n) atTop (𝓝 1)) :
    Nonempty (CapturedBranches orderedSliceRoot orderedSliceNondegenerate orderedSliceEndpoint
      (fun n => (⟨mu n, hm n⟩ : PositiveMassRatio)) eps (fun n => polarSlice (r n) (theta n))) := by
  let thetaG := fun n i => theta n (e i) - theta n anchor
  have hmE (n : ℕ) := positiveRatio_satellitePermutation _ (hm n) e
  have hphys (n : ℕ) := normalized_polar_reindex_sub_constant (eps n) (mu n) (x n)
    (heps n) (hm n) (hx n) (r n) (theta n) (hr n) (hpolar n) e (theta n anchor)
  obtain ⟨phi, hphi, ⟨c⟩⟩ := nestedPhysical_actual_capture_of_cubic_geometry tau omega htau homega
    eps (fun n => mu n ∘ e) (fun n => r n ∘ e) thetaG heps hepst hmE
    (fun n i => hr n (e i)) (fun n => by simp only [thetaG, heanchor, sub_self])
    (fun n => (hphys n).1) (fun n => (hphys n).2) d s hd hs hdt hsd hmacro hinner
    (fun i => hrt (e i)) htt hr02 hr12
    (by simpa only [thetaG, sub_sub_sub_cancel_right] using ht02)
    (by simpa only [thetaG, sub_sub_sub_cancel_right] using ht12) hr01
    (by simpa only [thetaG, sub_sub_sub_cancel_right] using ht01)
  have hc := c.toOriginalOrderedSlice (mu ∘ phi) (eps ∘ phi) (r ∘ phi) (theta ∘ phi) e anchor
    heanchor tau omega (fun n => hm (phi n)) (fun n => hr (phi n))
    (fun n => hzero (phi n)) (fun n => horder (phi n))
  let p : ℕ → PositiveMassRatio := fun n => ⟨mu n, hm n⟩
  let y := fun n => polarSlice (r n) (theta n)
  have hc' : Nonempty (CapturedBranches orderedSliceRoot orderedSliceNondegenerate orderedSliceEndpoint
      (p ∘ phi) (eps ∘ phi) (y ∘ phi)) := hc
  exact hc'.map (CapturedBranches.liftSubsequence p eps y phi hphi)

end DominantFiveBody
