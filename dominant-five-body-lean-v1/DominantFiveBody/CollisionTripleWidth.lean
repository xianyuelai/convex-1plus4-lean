import DominantFiveBody.CollisionTripleRegularScale

/-! # Angular width versus the actual triple diameter

The exact polar distance identity converts radial o(d) into W/d -> 1.
No positive lower bound for an individual internal distance is needed in
this geometric bridge; it also applies to the nested grouping branch.
-/

noncomputable section
open scoped BigOperators Matrix ContDiff
open Filter Set Topology

namespace DominantFiveBody
set_option maxHeartbeats 1200000

theorem polar_scaled_distance_square (ra rb va vb d : ℝ) :
    (‖polarPoint rb vb - polarPoint ra va‖ / d) ^ 2 =
      ((rb - ra) / d) ^ 2 + ra * rb * Real.sinc ((vb - va) / 2) ^ 2 * ((vb - va) / d) ^ 2 := by
  rw [div_pow, polar_distance_sq, ← sinc_mul_argument ((vb - va) / 2)]
  simp only [div_pow]
  ring

theorem polar_scaled_angle_distance_defect
    (ra rb va vb d : ℕ → ℝ) (hd : ∀ n, 0 < d n)
    (hra : Tendsto ra atTop (𝓝 1)) (hrb : Tendsto rb atTop (𝓝 1))
    (hgap : Tendsto (fun n => vb n - va n) atTop (𝓝 0))
    (hgapPos : ∀ n, 0 ≤ vb n - va n)
    (hrdiff : Tendsto (fun n => (rb n - ra n) / d n) atTop (𝓝 0))
    (hdist : ∀ n, ‖polarPoint (rb n) (vb n) - polarPoint (ra n) (va n)‖ ≤ d n) :
    Tendsto (fun n => ‖polarPoint (rb n) (vb n) - polarPoint (ra n) (va n)‖ / d n -
      (vb n - va n) / d n) atTop (𝓝 0) := by
  let x := fun n => ‖polarPoint (rb n) (vb n) - polarPoint (ra n) (va n)‖ / d n
  let a := fun n => (vb n - va n) / d n
  let c := fun n => ra n * rb n * Real.sinc ((vb n - va n) / 2) ^ 2
  have heq (n : ℕ) : x n ^ 2 = ((rb n - ra n) / d n) ^ 2 + c n * a n ^ 2 :=
    polar_scaled_distance_square _ _ _ _ _
  have hxn (n : ℕ) : 0 ≤ x n := div_nonneg (norm_nonneg _) (hd n).le
  have han (n : ℕ) : 0 ≤ a n := div_nonneg (hgapPos n) (hd n).le
  have hx1 (n : ℕ) : x n ≤ 1 := by
    exact (div_le_one (hd n)).mpr (hdist n)
  have hsinc : Tendsto (fun n => Real.sinc ((vb n - va n) / 2)) atTop (𝓝 1) := by
    simpa only [Function.comp_def, zero_div, Real.sinc_zero] using
      Real.continuous_sinc.continuousAt.tendsto.comp (hgap.div_const 2)
  have hct : Tendsto c atTop (𝓝 1) := by
    simpa only [c, one_mul, one_pow] using (hra.mul hrb).mul (hsinc.pow 2)
  have hbound : ∀ᶠ n in atTop, a n ≤ 2 := by
    filter_upwards [hct.eventually (Ioi_mem_nhds (by norm_num : (1 / 2 : ℝ) < 1))] with n hn
    have hprod := mul_le_mul_of_nonneg_right hn.le (sq_nonneg (a n))
    nlinarith [sq_nonneg ((rb n - ra n) / d n), heq n, hxn n, han n, hx1 n]
  have hterm : Tendsto (fun n => (c n - 1) * a n ^ 2) atTop (𝓝 0) := by
    apply tendsto_zero_iff_norm_tendsto_zero.mpr
    have hupp : ∀ᶠ n in atTop, ‖(c n - 1) * a n ^ 2‖ ≤ 4 * ‖c n - 1‖ := by
      filter_upwards [hbound] with n hn
      rw [Real.norm_eq_abs, abs_mul, abs_pow, abs_of_nonneg (han n), Real.norm_eq_abs]
      have hb : a n ^ 2 ≤ 4 := by nlinarith [han n]
      simpa only [mul_comm] using mul_le_mul_of_nonneg_left hb (abs_nonneg (c n - 1))
    have hl : Tendsto (fun n => 4 * ‖c n - 1‖) atTop (𝓝 0) := by
      simpa only [sub_self, norm_zero, mul_zero] using ((hct.sub_const 1).norm.const_mul 4)
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hl
      (Eventually.of_forall (fun n => norm_nonneg _)) hupp
  have hsq : Tendsto (fun n => x n ^ 2 - a n ^ 2) atTop (𝓝 0) := by
    have ht := (hrdiff.pow 2).add hterm
    convert ht using 1
    · funext n
      rw [heq]
      ring
    · norm_num
  have hsqrt : Tendsto (fun n => Real.sqrt |x n ^ 2 - a n ^ 2|) atTop (𝓝 0) := by
    simpa only [Function.comp_def, Real.norm_eq_abs, abs_zero, Real.sqrt_zero] using
      Real.continuous_sqrt.continuousAt.tendsto.comp hsq.norm
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  have hupp (n : ℕ) : ‖x n - a n‖ ≤ Real.sqrt |x n ^ 2 - a n ^ 2| := by
    rw [Real.norm_eq_abs]
    have hsqdef : (x n - a n) ^ 2 ≤ |x n ^ 2 - a n ^ 2| := by
      by_cases hxa : a n ≤ x n
      · rw [abs_of_nonneg (by nlinarith [hxn n, han n] : 0 ≤ x n ^ 2 - a n ^ 2)]
        nlinarith [hxn n, han n]
      · rw [abs_of_nonpos (by nlinarith [hxn n, han n] : x n ^ 2 - a n ^ 2 ≤ 0)]
        nlinarith [hxn n, han n]
    have hs := Real.sq_sqrt (abs_nonneg (x n ^ 2 - a n ^ 2))
    have hsn := Real.sqrt_nonneg |x n ^ 2 - a n ^ 2|
    have hdn := abs_nonneg (x n - a n)
    nlinarith [sq_abs (x n - a n)]
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hsqrt
    (Eventually.of_forall (fun n => norm_nonneg _)) (Eventually.of_forall hupp)

theorem triple_width_distance_ratio_tendsto_one
    (r theta : ℕ → Satellite → ℝ)
    (hr : ∀ i, Tendsto (fun n => r n i) atTop (𝓝 1))
    (hd : ∀ n, 0 < tripleLowDiameter (polarSatellites (r n) (theta n)))
    (horder : ∀ n, theta n 0 ≤ theta n 1 ∧ theta n 1 ≤ theta n 2)
    (hgap01 : Tendsto (fun n => theta n 1 - theta n 0) atTop (𝓝 0))
    (hgap12 : Tendsto (fun n => theta n 2 - theta n 1) atTop (𝓝 0))
    (hradial : ∀ i j : TripleLabel, Tendsto (fun n => (r n j.castSucc - r n i.castSucc) /
      tripleLowDiameter (polarSatellites (r n) (theta n))) atTop (𝓝 0)) :
    Tendsto (fun n => (theta n 2 - theta n 0) / tripleLowDiameter (polarSatellites (r n) (theta n)))
      atTop (𝓝 1) := by
  let d := fun n => tripleLowDiameter (polarSatellites (r n) (theta n))
  let x := fun n (i j : Satellite) => ‖polarPoint (r n j) (theta n j) - polarPoint (r n i) (theta n i)‖ / d n
  let a := fun n (i j : Satellite) => (theta n j - theta n i) / d n
  have hdefect (i j : TripleLabel) (hgapPos : ∀ n, 0 ≤ theta n j.castSucc - theta n i.castSucc)
      (hgap : Tendsto (fun n => theta n j.castSucc - theta n i.castSucc) atTop (𝓝 0)) :
      Tendsto (fun n => x n i.castSucc j.castSucc - a n i.castSucc j.castSucc) atTop (𝓝 0) := by
    apply polar_scaled_angle_distance_defect _ _ _ _ d hd (hr i.castSucc) (hr j.castSucc) hgap
    · exact hgapPos
    · exact hradial i j
    · intro n
      have h := tripleLowDiameter_bound (polarSatellites (r n) (theta n)) i j
      change ‖polarPoint (r n i.castSucc) (theta n i.castSucc) - polarPoint (r n j.castSucc) (theta n j.castSucc)‖ ≤ _ at h
      rw [norm_sub_rev] at h
      exact h
  have hgap02 : Tendsto (fun n => theta n 2 - theta n 0) atTop (𝓝 0) := by
    convert hgap01.add hgap12 using 1
    · funext n; ring
    · norm_num
  have h01 := hdefect 0 1 (fun n => sub_nonneg.mpr (horder n).1) hgap01
  have h02 := hdefect 0 2 (fun n => sub_nonneg.mpr ((horder n).1.trans (horder n).2)) hgap02
  have h12 := hdefect 1 2 (fun n => sub_nonneg.mpr (horder n).2) hgap12
  let E := fun n => |x n 0 1 - a n 0 1| + |x n 0 2 - a n 0 2| + |x n 1 2 - a n 1 2|
  have hEt : Tendsto E atTop (𝓝 0) := by
    convert! (h01.norm.add h02.norm).add h12.norm using 1
    norm_num [E, Real.norm_eq_abs]
  have hwidthBound (n : ℕ) : |a n 0 2 - 1| ≤ E n := by
    have hmax : max (x n 0 1) (max (x n 0 2) (x n 1 2)) = 1 := by
      dsimp [x]
      rw [max_div_div_right (hd n).le, max_div_div_right (hd n).le]
      change d n / d n = 1
      exact div_self (hd n).ne'
    have ha01 : a n 0 1 ≤ a n 0 2 := (div_le_div_iff_of_pos_right (hd n)).mpr (by linarith [(horder n).2])
    have ha12 : a n 1 2 ≤ a n 0 2 := (div_le_div_iff_of_pos_right (hd n)).mpr (by linarith [(horder n).1])
    have hx02 : x n 0 2 ≤ 1 := by rw [← hmax]; exact (le_max_left _ _).trans (le_max_right _ _)
    have hx01 : x n 0 1 ≤ a n 0 2 + E n := by
      have h := le_abs_self (x n 0 1 - a n 0 1)
      dsimp [E]
      linarith [abs_nonneg (x n 0 2 - a n 0 2), abs_nonneg (x n 1 2 - a n 1 2)]
    have hx02' : x n 0 2 ≤ a n 0 2 + E n := by
      have h := le_abs_self (x n 0 2 - a n 0 2)
      dsimp [E]
      linarith [abs_nonneg (x n 0 1 - a n 0 1), abs_nonneg (x n 1 2 - a n 1 2)]
    have hx12 : x n 1 2 ≤ a n 0 2 + E n := by
      have h := le_abs_self (x n 1 2 - a n 1 2)
      dsimp [E]
      linarith [abs_nonneg (x n 0 1 - a n 0 1), abs_nonneg (x n 0 2 - a n 0 2)]
    have hlow : 1 ≤ a n 0 2 + E n := by rw [← hmax]; exact max_le hx01 (max_le hx02' hx12)
    apply abs_le.mpr
    constructor
    · linarith
    · have h := neg_le_abs (x n 0 2 - a n 0 2)
      dsimp [E]
      linarith [abs_nonneg (x n 0 1 - a n 0 1), abs_nonneg (x n 1 2 - a n 1 2)]
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hEt
    (Eventually.of_forall (fun n => norm_nonneg _))
    (Eventually.of_forall (fun n => by simpa only [Real.norm_eq_abs] using hwidthBound n))

theorem complete_lower_triple_angles_equal (q : SatelliteConfiguration) (theta : Satellite → ℝ)
    (hpolar : ∀ i, q i = polarPoint 1 (theta i)) (hmono : Monotone theta)
    (hspan : theta 3 - theta 0 < Real.pi) (center : Plane)
    (htriple : CompleteLimitingSatelliteTriple q 3 center) (i j : TripleLabel) :
    theta i.castSucc = theta j.castSucc := by
  apply (unit_ordered_limit_equal_iff q theta hpolar hmono hspan i.castSucc j.castSucc).mp
  have hi : i.castSucc ≠ (3 : Satellite) := by fin_cases i <;> decide
  have hj : j.castSucc ≠ (3 : Satellite) := by fin_cases j <;> decide
  rw [(htriple i.castSucc).mpr hi, (htriple j.castSucc).mpr hj]

theorem normalized_complete_lower_triple_regular_width_limit
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
    Tendsto (fun n => (theta n 2 - theta n 0) / tripleLowDiameter (satellitesRelative (x n)))
      atTop (𝓝 1) := by
  obtain ⟨hrt, hunit, hmono, _, hspan⟩ := normalized_ordered_polar_limit_geometry eps mu x heps hepst hm hx
    r theta hr hpolar horder muLimit hmt qLimit hqt theta0 htheta
  have hrad := normalized_complete_lower_triple_regular_radial_limits eps mu x heps hepst hm hx
    hconv r theta hr hpolar horder muLimit hmt qLimit hqt theta0 htheta center htriple eta heta hcomparable
  have hgap (i j : TripleLabel) : Tendsto (fun n => theta n j.castSucc - theta n i.castSucc) atTop (𝓝 0) := by
    have hi := (continuous_apply i.castSucc).tendsto theta0 |>.comp htheta
    have hj := (continuous_apply j.castSucc).tendsto theta0 |>.comp htheta
    simpa only [complete_lower_triple_angles_equal qLimit theta0 hunit hmono hspan center htriple i j,
      sub_self, Function.comp_def] using hj.sub hi
  have hd (n : ℕ) : 0 < tripleLowDiameter (polarSatellites (r n) (theta n)) := by
    rw [← hpolar n]
    exact tripleLowDiameter_pos _ (satellitesRelative_collisionFree (x n) (hx n).1)
  have hh := triple_width_distance_ratio_tendsto_one r theta
    (fun i => (continuous_apply i).tendsto (fun _ : Satellite => (1 : ℝ)) |>.comp hrt) hd
    (fun n => ⟨by linarith [(horder n 0 1 (by decide)).1], by linarith [(horder n 1 2 (by decide)).1]⟩)
    (hgap 0 1) (hgap 1 2) (by simpa only [hpolar] using hrad)
  simpa only [hpolar] using hh

end DominantFiveBody
