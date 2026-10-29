import DominantFiveBody.NestedActualCaptureLimits
import DominantFiveBody.CollisionTripleNestedComplete

/-! Individual original inverse scale limits and current-fraction entry
of the complete seven-coordinate vector. Alpha convergence is absent. -/
noncomputable section
open scoped BigOperators Matrix ContDiff
open Filter Set Topology
namespace DominantFiveBody
open Coorbital
set_option maxHeartbeats 1400000

theorem nestedSource_individual_inverse_limits
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
        (𝓝 (nestedBasePoint psi omega)) ∧
      Tendsto (fun n => d n / nestedPhysicalScale (mu n)) atTop
        (𝓝 (pairBoundaryScale tripleD0)) ∧
      Tendsto (fun n => s n / (nestedPhysicalScale (mu n) * nestedPhysicalEta (mu n))) atTop
        (𝓝 (pairBoundaryScale (3 * tripleD0))) ∧
      Tendsto (fun n => nestedRowOuterDifference (nestedPhysicalScale (mu n))
        (nestedPhysicalAlpha (mu n)) (r n)) atTop (𝓝 0) ∧
      Tendsto (fun n => nestedRowInnerDifference (nestedPhysicalScale (mu n))
        (nestedPhysicalEta (mu n)) (r n)) atTop (𝓝 0) ∧
      Tendsto (fun n => nestedRowInnerDifference (nestedPhysicalScale (mu n))
        (nestedPhysicalEta (mu n)) (theta n)) atTop
        (𝓝 (pairBoundaryScale (3 * tripleD0))) ∧
      Tendsto (fun n => (theta n 2 - theta n 0) / nestedPhysicalScale (mu n)) atTop
        (𝓝 (omega * pairBoundaryScale tripleD0)) ∧
      Tendsto (fun n => (theta n 2 - theta n 1) / nestedPhysicalScale (mu n)) atTop
        (𝓝 (omega * pairBoundaryScale tripleD0)) ∧
      Tendsto (fun n => nestedRowOuterDifference (nestedPhysicalScale (mu n))
        (nestedPhysicalAlpha (mu n)) (theta n)) atTop
        (𝓝 (omega * pairBoundaryScale tripleD0)) := by
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
  refine ⟨htlim, hetalim, ?_, hDt, hSt, hu, hv, hz, ht0t, ht1t, hZ⟩
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


/-- Parameter and all seven variable entries use the current alpha itself
as center. Consequently no limit or subsequence of alpha is needed. -/
theorem nestedSource_common_balls_without_alpha_limit
    (eps t eta alpha : ℕ → ℝ) (y : ℕ → NestedChartVariables) (psi omega d r : ℝ)
    (heps : Tendsto eps atTop (𝓝 0)) (ht : Tendsto t atTop (𝓝 0))
    (heta : Tendsto eta atTop (𝓝 0))
    (hy : Tendsto y atTop (𝓝 (nestedBasePoint psi omega))) (hd : 0 < d) (hr : 0 < r) :
    ∀ᶠ n in atTop,
      dist (nestedParameter (eps n) (t n) (eta n) (alpha n))
        (nestedParameter 0 0 0 (alpha n)) < d ∧
      dist (y n) (nestedBasePoint psi omega) < r := by
  have he : ∀ᶠ n in atTop, |eps n| < d := by
    simpa only [Metric.mem_ball, Real.dist_eq, sub_zero] using
      heps.eventually (Metric.ball_mem_nhds (0 : ℝ) hd)
  have htn : ∀ᶠ n in atTop, |t n| < d := by
    simpa only [Metric.mem_ball, Real.dist_eq, sub_zero] using
      ht.eventually (Metric.ball_mem_nhds (0 : ℝ) hd)
  have hen : ∀ᶠ n in atTop, |eta n| < d := by
    simpa only [Metric.mem_ball, Real.dist_eq, sub_zero] using
      heta.eventually (Metric.ball_mem_nhds (0 : ℝ) hd)
  have hyn : ∀ᶠ n in atTop, dist (y n) (nestedBasePoint psi omega) < r :=
    hy.eventually (Metric.ball_mem_nhds _ hr)
  filter_upwards [he, htn, hen, hyn] with n hn hnt hne hny
  refine ⟨?_, hny⟩
  apply (dist_pi_lt_iff hd).mpr
  intro i
  fin_cases i
  · simpa [nestedParameter, Real.dist_eq] using hn
  · simpa [nestedParameter, Real.dist_eq] using hnt
  · simpa [nestedParameter, Real.dist_eq] using hne
  · simpa [nestedParameter] using hd

/-- The pre-chart quantitative radial estimate converts to the original
u2=O(epsilon) using the finite positive inverse scale limit. -/
theorem nestedSource_radial_Oepsilon_from_original_bound
    (eps t eta s dr : ℕ → ℝ) (C z0 : ℝ)
    (heps : ∀ n, 0 ≤ eps n) (ht : ∀ n, 0 < t n) (heta : ∀ n, 0 < eta n)
    (hC : 0 < C) (hz0 : 0 < z0)
    (hbound : ∀ᶠ n in atTop, |dr n| ≤ C * eps n * s n)
    (hscale : Tendsto (fun n => s n / (t n * eta n)) atTop (𝓝 z0)) :
    ∃ K : ℝ, 0 < K ∧ ∀ᶠ n in atTop, |dr n / (t n * eta n)| ≤ K * eps n := by
  have hnear : ∀ᶠ n in atTop, s n / (t n * eta n) < z0 + 1 :=
    hscale.eventually (Iio_mem_nhds (by linarith : z0 < z0 + 1))
  refine ⟨C * (z0 + 1), mul_pos hC (by linarith), ?_⟩
  filter_upwards [hbound, hnear] with n hb hn
  have hp : 0 < t n * eta n := mul_pos (ht n) (heta n)
  rw [abs_div, abs_of_pos hp]
  calc
    |dr n| / (t n * eta n) ≤ (C * eps n * s n) / (t n * eta n) :=
      div_le_div_of_nonneg_right hb hp.le
    _ = (C * eps n) * (s n / (t n * eta n)) := by ring
    _ ≤ (C * eps n) * (z0 + 1) :=
      mul_le_mul_of_nonneg_left hn.le (mul_nonneg hC.le (heps n))
    _ = C * (z0 + 1) * eps n := by ring

end DominantFiveBody
