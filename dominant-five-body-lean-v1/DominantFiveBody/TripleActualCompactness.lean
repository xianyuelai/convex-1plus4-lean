import DominantFiveBody.TripleActualCaptureLimits
import DominantFiveBody.CollisionTripleRegularScale
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity

/-! # Compact selection of actual regular-triple inverse coordinates

The only bounds used here are bounds on the actual current cubic scale
and on the current adjacent angular gaps. No limiting scalar root is
postulated. The complete boundary equations are recovered afterwards.
-/

noncomputable section
open scoped BigOperators Matrix ContDiff
open Filter Set Topology
namespace DominantFiveBody
set_option maxHeartbeats 1000000

theorem positive_cube_ratio_bounds (t d c M : ℝ) (ht : 0 < t) (hd : 0 < d)
    (hc : 0 < c) (hM : 0 < M) (hlow : c ≤ (t / d) ^ 3) (hupp : (t / d) ^ 3 ≤ M) :
    min c 1 ≤ t / d ∧ t / d ≤ M + 1 := by
  have htd : 0 < t / d := div_pos ht hd
  constructor
  · by_cases h1 : 1 ≤ t / d
    · exact (min_le_right _ _).trans h1
    · have hsmall : t / d ≤ 1 := le_of_not_ge h1
      have hsq : (t / d) ^ 2 ≤ 1 := by nlinarith
      have hcube : (t / d) ^ 3 ≤ t / d := by
        nlinarith [mul_le_mul_of_nonneg_left hsq htd.le]
      exact (min_le_left _ _).trans (hlow.trans hcube)
  · by_contra hn
    have hlarge : M + 1 < t / d := lt_of_not_ge hn
    have h1 : 1 < t / d := by linarith
    have hsq : 1 ≤ (t / d) ^ 2 := by nlinarith
    have hcube : t / d ≤ (t / d) ^ 3 := by
      nlinarith [mul_le_mul_of_nonneg_left hsq htd.le]
    linarith

theorem zero_div_scale_of_ratio_lower (a t d : ℕ → ℝ) (k : ℝ)
    (hk : 0 < k) (ht : ∀ n, 0 < t n) (hd : ∀ n, 0 < d n)
    (hbound : ∀ᶠ n in atTop, k ≤ t n / d n)
    (halim : Tendsto (fun n => a n / d n) atTop (𝓝 0)) :
    Tendsto (fun n => a n / t n) atTop (𝓝 0) := by
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  have hupp : ∀ᶠ n in atTop, ‖a n / t n‖ ≤ (1 / k) * ‖a n / d n‖ := by
    filter_upwards [hbound] with n hn
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_div, abs_div, abs_of_pos (ht n), abs_of_pos (hd n)]
    have hscale : k * d n ≤ t n := (le_div_iff₀ (hd n)).mp hn
    have hh := mul_le_mul_of_nonneg_left (one_div_le_one_div_of_le (mul_pos hk (hd n)) hscale)
      (abs_nonneg (a n))
    convert! hh using 1 <;> ring
  have hzero : Tendsto (fun n => (1 / k) * ‖a n / d n‖) atTop (𝓝 0) := by
    simpa only [norm_zero, mul_zero] using halim.norm.const_mul (1 / k)
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hzero
    (Eventually.of_forall (fun n => norm_nonneg _)) hupp

theorem regular_scaled_gap_bounds (t d W : ℕ → ℝ) (gap distance : ℕ → Fin 2 → ℝ)
    (ht : ∀ n, 0 < t n) (hd : ∀ n, 0 < d n)
    (k H eta : ℝ) (hk : 0 < k) (hH : 0 < H) (heta : 0 < eta)
    (hratio : ∀ᶠ n in atTop, k ≤ t n / d n ∧ t n / d n ≤ H)
    (hW : Tendsto (fun n => W n / d n) atTop (𝓝 1))
    (hgap : ∀ n i, 0 ≤ gap n i ∧ gap n i ≤ W n)
    (hcomparable : ∀ᶠ n in atTop, ∀ i, eta * d n ≤ distance n i)
    (hdefect : ∀ i, Tendsto (fun n => distance n i / d n - gap n i / d n) atTop (𝓝 0)) :
    ∀ᶠ n in atTop, ∀ i, gap n i / t n ∈ Icc (eta / (2 * H)) (2 / k) := by
  have hdef : ∀ᶠ n in atTop, ∀ i, distance n i / d n - gap n i / d n < eta / 2 := by
    exact (Filter.eventually_all).mpr (fun i => (hdefect i).eventually (Iio_mem_nhds (by positivity)))
  filter_upwards [hratio, hcomparable, hdef, hW.eventually (Iio_mem_nhds (by norm_num : (1 : ℝ) < 2))]
    with n hn hcomp herror hwidth
  intro i
  have htd := div_pos (ht n) (hd n)
  have hdist : eta ≤ distance n i / d n := (le_div_iff₀ (hd n)).mpr (hcomp i)
  have hlow : eta / 2 ≤ gap n i / d n := by linarith [herror i]
  have hupp : gap n i / d n ≤ 2 :=
    ((div_le_div_iff_of_pos_right (hd n)).mpr (hgap n i).2).trans hwidth.le
  have he : gap n i / t n = (gap n i / d n) / (t n / d n) := by
    field_simp [(ht n).ne', (hd n).ne']
  rw [he]
  constructor
  · apply (le_div_iff₀ htd).mpr
    have hb := mul_le_mul_of_nonneg_left hn.2
      (div_pos heta (mul_pos (by norm_num : (0 : ℝ) < 2) hH)).le
    have heq : eta / (2 * H) * H = eta / 2 := by field_simp
    rw [heq] at hb
    exact hb.trans hlow
  · apply (div_le_iff₀ htd).mpr
    have hb := mul_le_mul_of_nonneg_left hn.1 (div_pos (by norm_num : (0 : ℝ) < 2) hk).le
    have heq : 2 / k * k = (2 : ℝ) := by field_simp
    rw [heq] at hb
    exact hupp.trans hb

theorem triple_actual_inverse_coordinates_compact_limits
    (mu : ℕ → MassRatio) (hm : ∀ n, PositiveRatio (mu n))
    (r theta : ℕ → Satellite → ℝ) (psi : ℝ)
    (hrt : ∀ i, Tendsto (fun n => r n i) atTop (𝓝 1))
    (htt : ∀ i : TripleLabel, Tendsto (fun n => theta n i.castSucc) atTop (𝓝 psi))
    (hradial : ∀ i : Fin 2, Tendsto (fun n =>
      (r n i.succ.castSucc - r n i.castSucc.castSucc) / triplePhysicalScale (mu n)) atTop (𝓝 0))
    (k B : ℝ) (hk : 0 < k)
    (hgap : ∀ᶠ n in atTop, ∀ i : Fin 2,
      (theta n i.succ.castSucc - theta n i.castSucc.castSucc) / triplePhysicalScale (mu n) ∈ Icc k B) :
    ∃ (phi : ℕ → ℕ) (alpha0 : TripleVector) (g : TripleGaps), StrictMono phi ∧
      TripleWeights alpha0 ∧ (∀ i, 0 < g i) ∧
      Tendsto (fun n => triplePhysicalWeights (mu (phi n))) atTop (𝓝 alpha0) ∧
      Tendsto (fun n => tripleVariablesFromPolar (triplePhysicalScale (mu (phi n)))
        (triplePhysicalWeights (mu (phi n))) (r (phi n)) (theta (phi n))) atTop
        (𝓝 (tripleUnitPoint psi g)) := by
  let alpha := fun n => triplePhysicalWeights (mu n)
  let gap := fun n (i : Fin 2) =>
    (theta n i.succ.castSucc - theta n i.castSucc.castSucc) / triplePhysicalScale (mu n)
  let S : Set (TripleVector × TripleGaps) :=
    {a : TripleVector | ∀ i, a i ∈ Icc (0 : ℝ) 1} ×ˢ {g : TripleGaps | ∀ i, g i ∈ Icc k B}
  have hS : IsCompact S := (isCompact_pi_infinite (fun _ : TripleLabel => isCompact_Icc)).prod
    (isCompact_pi_infinite (fun _ : Fin 2 => isCompact_Icc))
  have ha (n : ℕ) (i : TripleLabel) : alpha n i ∈ Icc (0 : ℝ) 1 := by
    have hpos := (triplePhysicalWeights_positive (mu n) (hm n) i).le
    refine ⟨hpos, ?_⟩
    rw [← triplePhysicalWeights_sum (mu n) (hm n)]
    exact Finset.single_le_sum (fun j _ => (triplePhysicalWeights_positive (mu n) (hm n) j).le)
      (Finset.mem_univ i)
  have hf : ∃ᶠ n in atTop, (alpha n, gap n) ∈ S :=
    (hgap.mono (fun n hn => ⟨ha n, hn⟩)).frequently
  obtain ⟨z, hz, phi, hphi, hzt⟩ := hS.tendsto_subseq' hf
  have halim : Tendsto (fun n => alpha (phi n)) atTop (𝓝 z.1) :=
    continuous_fst.continuousAt.tendsto.comp hzt
  have hglim : Tendsto (fun n => gap (phi n)) atTop (𝓝 z.2) :=
    continuous_snd.continuousAt.tendsto.comp hzt
  have hasum : ∑ i, z.1 i = 1 := by
    have hc : Continuous (fun a : TripleVector => ∑ i, a i) := by fun_prop
    have ht := hc.continuousAt.tendsto.comp halim
    have he : (fun n => ∑ i, alpha (phi n) i) = (fun _ : ℕ => (1 : ℝ)) :=
      funext (fun n => triplePhysicalWeights_sum (mu (phi n)) (hm (phi n)))
    change Tendsto (fun n => ∑ i, alpha (phi n) i) atTop (𝓝 (∑ i, z.1 i)) at ht
    rw [he] at ht
    exact tendsto_nhds_unique ht tendsto_const_nhds
  refine ⟨phi, z.1, z.2, hphi, ⟨fun i => (hz.1 i).1, hasum⟩,
    fun i => hk.trans_le (hz.2 i).1, halim, ?_⟩
  have hr1 (i : Satellite) := (hrt i).comp hphi.tendsto_atTop
  have ht1 (i : TripleLabel) := (htt i).comp hphi.tendsto_atTop
  have ha1 (i : TripleLabel) := (continuous_apply i).tendsto z.1 |>.comp halim
  have hg1 (i : Fin 2) := (continuous_apply i).tendsto z.2 |>.comp hglim
  have hu1 (i : Fin 2) := (hradial i).comp hphi.tendsto_atTop
  have hs1 : z.1 0 + z.1 1 + z.1 2 = 1 := by simpa only [Fin.sum_univ_three] using hasum
  apply tendsto_pi_nhds.mpr
  intro i
  fin_cases i
  · exact hr1 3
  · have ht := ((ha1 0).mul (hr1 0) |>.add ((ha1 1).mul (hr1 1))).add ((ha1 2).mul (hr1 2))
    simpa [tripleVariablesFromPolar, tripleFromFixedSlice, tripleRawSlice,
      tripleVariableProjection, smul_eq_mul, alpha, Function.comp_def, tripleUnitPoint, hs1] using ht
  · simpa [tripleVariablesFromPolar, tripleFromFixedSlice, tripleRawSlice,
      tripleVariableProjection, smul_eq_mul, div_eq_mul_inv, mul_comm, Function.comp_def, tripleUnitPoint] using hu1 0
  · simpa [tripleVariablesFromPolar, tripleFromFixedSlice, tripleRawSlice,
      tripleVariableProjection, smul_eq_mul, div_eq_mul_inv, mul_comm, Function.comp_def, tripleUnitPoint] using hu1 1
  · have ht := ((ha1 0).mul (ht1 0) |>.add ((ha1 1).mul (ht1 1))).add ((ha1 2).mul (ht1 2))
    have heq : z.1 0 * psi + z.1 1 * psi + z.1 2 * psi = psi := by linear_combination psi * hs1
    rw [heq] at ht
    simpa [tripleVariablesFromPolar, tripleFromFixedSlice, tripleRawSlice,
      tripleVariableProjection, smul_eq_mul, alpha, Function.comp_def, tripleUnitPoint] using ht
  · simpa [tripleVariablesFromPolar, tripleFromFixedSlice, tripleRawSlice,
      tripleVariableProjection, smul_eq_mul, div_eq_mul_inv, mul_comm, gap, Function.comp_def, tripleUnitPoint] using hg1 0
  · simpa [tripleVariablesFromPolar, tripleFromFixedSlice, tripleRawSlice,
      tripleVariableProjection, smul_eq_mul, div_eq_mul_inv, mul_comm, gap, Function.comp_def, tripleUnitPoint] using hg1 1

end DominantFiveBody
