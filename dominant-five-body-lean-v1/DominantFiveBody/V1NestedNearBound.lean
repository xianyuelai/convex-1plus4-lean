import DominantFiveBody.CollisionUpperRectangleGeometry
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

/-! # The v1 near-source radial-derivative estimate

The displayed estimate added to the submitted manuscript at lines 495--496
is first proved with explicit local constants. The two actual endpoint
triple theorems then obtain all local hypotheses from the previously proved
uniform geometry of the entire moving pair rectangle. No positive lower
bound on the current near-source mass is used.
-/

noncomputable section
open Filter Set Topology
namespace DominantFiveBody
set_option maxHeartbeats 1600000

/-- A local quantitative version of the vanishing near-source contribution.
The absolute source-radius bound, tangential gap bound and lower distance
bound will be derived from the actual moving-rectangle geometry below. -/
theorem physicalSourceAngularRadialDerivative_near_display_bound
    (mass s angle rho v d : ℝ) (hm : 0 ≤ mass) (hd : 0 < d)
    (hs : |s| ≤ 2) (hgap : |angle - v| ≤ 2 * d)
    (hsep : d / 2 ≤ ‖polarPoint rho v - polarPoint s angle‖) :
    |mass * physicalSourceAngularRadialDerivative s angle rho v| ≤
      1536 * (mass / d ^ 3) * (|rho - s| / d + d) := by
  let D := ‖polarPoint rho v - polarPoint s angle‖
  have hD : 0 < D := lt_of_lt_of_le (by positivity : 0 < d / 2) hsep
  have hsin : |Real.sin (angle - v)| ≤ 2 * d := Real.abs_sin_le_abs.trans hgap
  have hgapSq : (angle - v) ^ 2 ≤ (2 * d) ^ 2 := by
    simpa only [sq_abs] using
      (sq_le_sq₀ (abs_nonneg (angle - v)) (by positivity : 0 ≤ 2 * d)).mpr hgap
  have hcos : |1 - Real.cos (angle - v)| ≤ 2 * d ^ 2 := by
    rw [abs_of_nonneg (sub_nonneg.mpr (Real.cos_le_one _))]
    nlinarith [Real.one_sub_sq_div_two_le_cos (x := angle - v)]
  have hproj : |rho - s * Real.cos (angle - v)| ≤ 4 * (|rho - s| + d ^ 2) := by
    calc
      |rho - s * Real.cos (angle - v)| =
          |(rho - s) + s * (1 - Real.cos (angle - v))| := by congr 1; ring
      _ ≤ |rho - s| + |s * (1 - Real.cos (angle - v))| := abs_add_le _ _
      _ = |rho - s| + |s| * |1 - Real.cos (angle - v)| := by rw [abs_mul]
      _ ≤ |rho - s| + 2 * (2 * d ^ 2) := by gcongr
      _ ≤ 4 * (|rho - s| + d ^ 2) := by nlinarith [abs_nonneg (rho - s)]
  have hden : (d / 2) ^ 5 ≤ D ^ 5 := pow_le_pow_left₀ (by positivity) hsep 5
  have habs : |mass * physicalSourceAngularRadialDerivative s angle rho v| =
      (3 * mass * |s| * |Real.sin (angle - v)| *
        |rho - s * Real.cos (angle - v)|) / D ^ 5 := by
    unfold physicalSourceAngularRadialDerivative
    simp only [abs_mul, abs_neg, abs_of_nonneg hm, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 3),
      abs_inv, abs_pow, abs_of_nonneg (norm_nonneg _), div_eq_mul_inv, D]
    ring
  calc
    |mass * physicalSourceAngularRadialDerivative s angle rho v| =
        (3 * mass * |s| * |Real.sin (angle - v)| *
          |rho - s * Real.cos (angle - v)|) / D ^ 5 := habs
    _ ≤ (48 * mass * d * (|rho - s| + d ^ 2)) / D ^ 5 := by
      apply div_le_div_of_nonneg_right _ (by positivity)
      calc
        _ ≤ 3 * mass * 2 * (2 * d) * (4 * (|rho - s| + d ^ 2)) := by gcongr
        _ = _ := by ring
    _ ≤ (48 * mass * d * (|rho - s| + d ^ 2)) / (d / 2) ^ 5 := by
      exact div_le_div_of_nonneg_left (by positivity) (by positivity) hden
    _ = 1536 * (mass / d ^ 3) * (|rho - s| / d + d) := by
      field_simp [ne_of_gt hd]
      ring

/-- The explicit local estimate holds eventually on the entire pair polar
rectangle whenever the already-proved uniform first-order geometry holds.
Masses may vanish and are not required to have a positive lower bound. -/
theorem physical_nested_polar_rectangle_near_display_bound
    (mass rc vc ra va rb vb d : ℕ → ℝ) (omega : ℝ)
    (hm : ∀ n, 0 ≤ mass n) (hd : ∀ n, 0 < d n)
    (hrc : Tendsto rc atTop (𝓝 1)) (homega : omega ^ 2 = 1)
    (hgeometry : ∀ eta : ℝ, 0 < eta → ∀ᶠ n in atTop,
      ∀ rho ∈ uIcc (ra n) (rb n), ∀ v ∈ uIcc (va n) (vb n),
        |(vc n - v) / d n - omega| < eta ∧ |(rho - rc n) / d n| < eta ∧
        |‖polarPoint rho v - polarPoint (rc n) (vc n)‖ / d n - 1| < eta) :
    ∀ᶠ n in atTop, ∀ rho ∈ uIcc (ra n) (rb n), ∀ v ∈ uIcc (va n) (vb n),
      |mass n * physicalSourceAngularRadialDerivative (rc n) (vc n) rho v| ≤
        1536 * (mass n / d n ^ 3) * (|rho - rc n| / d n + d n) := by
  have hs := hrc.eventually
    (Ioo_mem_nhds (by norm_num : (0 : ℝ) < 1) (by norm_num : (1 : ℝ) < 2))
  have homegaAbs : |omega| = 1 := by nlinarith [sq_abs omega, abs_nonneg omega]
  filter_upwards [hs, hgeometry (1 / 2) (by norm_num)] with n hsn hgn
  intro rho hrho v hv
  have hg := hgn rho hrho v hv
  have hquot : |(vc n - v) / d n| ≤ 2 := by
    calc
      |(vc n - v) / d n| = |((vc n - v) / d n - omega) + omega| := by congr 1; ring
      _ ≤ |(vc n - v) / d n - omega| + |omega| := abs_add_le _ _
      _ ≤ 2 := by rw [homegaAbs]; linarith [hg.1]
  have hgap : |vc n - v| ≤ 2 * d n := by
    have hquot' : |vc n - v| / d n ≤ 2 := by
      simpa only [abs_div, abs_of_pos (hd n)] using hquot
    exact (div_le_iff₀ (hd n)).mp hquot'
  have hdist : (1 / 2 : ℝ) ≤ ‖polarPoint rho v - polarPoint (rc n) (vc n)‖ / d n := by
    linarith [(abs_lt.mp hg.2.2).1]
  have hsep : d n / 2 ≤ ‖polarPoint rho v - polarPoint (rc n) (vc n)‖ := by
    have hh := (le_div_iff₀ (hd n)).mp hdist
    linarith
  exact physicalSourceAngularRadialDerivative_near_display_bound
    (mass n) (rc n) (vc n) rho v (d n) (hm n) (hd n)
    (by rw [abs_of_pos hsn.1]; exact hsn.2.le) hgap hsep

/-- Submitted-manuscript near-source display bound on an actual lower
endpoint nested triple, with every target in the moving pair rectangle. -/
theorem normalized_complete_lower_triple_nested_rectangle_near_display_bound
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
    (theta0 : Satellite → ℝ) (htt : Tendsto theta atTop (𝓝 theta0))
    (center : Plane) (htriple : CompleteLimitingSatelliteTriple qLimit 3 center)
    (a b c : TripleLabel) (hab : a < b) (hca : c ≠ a) (hcb : c ≠ b)
    (hpair : Tendsto (fun n => satelliteDistance (satellitesRelative (x n)) a.castSucc b.castSucc /
      tripleLowDiameter (satellitesRelative (x n))) atTop (𝓝 0)) :
    ∀ᶠ n in atTop,
      ∀ rho ∈ uIcc (r n a.castSucc) (r n b.castSucc),
      ∀ v ∈ uIcc (theta n a.castSucc) (theta n b.castSucc),
        |mu n c.castSucc * physicalSourceAngularRadialDerivative (r n c.castSucc)
          (theta n c.castSucc) rho v| ≤
        1536 * (mu n c.castSucc / tripleLowDiameter (satellitesRelative (x n)) ^ 3) *
          (|rho - r n c.castSucc| / tripleLowDiameter (satellitesRelative (x n)) +
            tripleLowDiameter (satellitesRelative (x n))) := by
  have hgeom := normalized_complete_lower_triple_nested_rectangle_near_geometry_uniform
    eps mu x heps hepst hm hx hconv r theta hr hpolar horder muLimit hmt qLimit hqt
    theta0 htt center htriple a b c hab hca hcb hpair
  have hrt := (normalized_ordered_polar_limit_geometry eps mu x heps hepst hm hx
    r theta hr hpolar horder muLimit hmt qLimit hqt theta0 htt).1
  have hrc : Tendsto (fun n => r n c.castSucc) atTop (𝓝 1) :=
    (continuous_apply c.castSucc).continuousAt.tendsto.comp hrt
  have homega : (lowNestedOrientation a c) ^ 2 = 1 := by
    unfold lowNestedOrientation
    split_ifs <;> norm_num
  exact physical_nested_polar_rectangle_near_display_bound
    (fun n => mu n c.castSucc) (fun n => r n c.castSucc) (fun n => theta n c.castSucc)
    (fun n => r n a.castSucc) (fun n => theta n a.castSucc)
    (fun n => r n b.castSucc) (fun n => theta n b.castSucc)
    (fun n => tripleLowDiameter (satellitesRelative (x n))) (lowNestedOrientation a c)
    (fun n => ((hm n).1 c.castSucc).le)
    (fun n => tripleLowDiameter_pos _ (satellitesRelative_collisionFree _ (hx n).1))
    hrc homega hgeom

/-- The same bound for the upper endpoint block. The original hypotheses
are unchanged, and all targets of its actual pair rectangle are covered. -/
theorem normalized_complete_upper_triple_nested_rectangle_near_display_bound
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
    (theta0 : Satellite → ℝ) (htt : Tendsto theta atTop (𝓝 theta0))
    (center : Plane) (htriple : CompleteLimitingSatelliteTriple qLimit 0 center)
    (a b c : TripleLabel) (hab : a < b) (hca : c ≠ a) (hcb : c ≠ b)
    (hpair : Tendsto (fun n => satelliteDistance (satellitesRelative (x n)) a.succ b.succ /
      tripleHighDiameter (satellitesRelative (x n))) atTop (𝓝 0)) :
    ∀ᶠ n in atTop,
      ∀ rho ∈ uIcc (r n a.succ) (r n b.succ),
      ∀ v ∈ uIcc (theta n a.succ) (theta n b.succ),
        |mu n c.succ * physicalSourceAngularRadialDerivative (r n c.succ)
          (theta n c.succ) rho v| ≤
        1536 * (mu n c.succ / tripleHighDiameter (satellitesRelative (x n)) ^ 3) *
          (|rho - r n c.succ| / tripleHighDiameter (satellitesRelative (x n)) +
            tripleHighDiameter (satellitesRelative (x n))) := by
  have hgeom := normalized_complete_upper_triple_nested_rectangle_near_geometry_uniform
    eps mu x heps hepst hm hx hconv r theta hr hpolar horder muLimit hmt qLimit hqt
    theta0 htt center htriple a b c hab hca hcb hpair
  have hrt := (normalized_ordered_polar_limit_geometry eps mu x heps hepst hm hx
    r theta hr hpolar horder muLimit hmt qLimit hqt theta0 htt).1
  have hrc : Tendsto (fun n => r n c.succ) atTop (𝓝 1) :=
    (continuous_apply c.succ).continuousAt.tendsto.comp hrt
  have homega : (lowNestedOrientation a c) ^ 2 = 1 := by
    unfold lowNestedOrientation
    split_ifs <;> norm_num
  have hd (n : ℕ) : 0 < tripleHighDiameter (satellitesRelative (x n)) := by
    have hcf := satellitesRelative_collisionFree _ (hx n).1
    exact (norm_pos_iff.mpr (sub_ne_zero.mpr (hcf.2 3 2 (by decide)))).trans_le
      (le_max_left _ _)
  exact physical_nested_polar_rectangle_near_display_bound
    (fun n => mu n c.succ) (fun n => r n c.succ) (fun n => theta n c.succ)
    (fun n => r n a.succ) (fun n => theta n a.succ)
    (fun n => r n b.succ) (fun n => theta n b.succ)
    (fun n => tripleHighDiameter (satellitesRelative (x n))) (lowNestedOrientation a c)
    (fun n => ((hm n).1 c.succ).le) hd hrc homega hgeom

/-- The displayed upper-bound expression itself tends to zero uniformly,
provided its current mass divided by the cube scale has a finite limit.
No positivity or positive lower mass-share assumption enters this limit. -/
theorem physical_nested_polar_rectangle_near_display_rhs_vanishes
    (mass rc ra va rb vb d : ℕ → ℝ) (L : ℝ)
    (hd : ∀ n, 0 < d n) (hdt : Tendsto d atTop (𝓝 0))
    (hmc : Tendsto (fun n => mass n / d n ^ 3) atTop (𝓝 L))
    (hrad : ∀ eta : ℝ, 0 < eta → ∀ᶠ n in atTop,
      ∀ rho ∈ uIcc (ra n) (rb n), ∀ v ∈ uIcc (va n) (vb n),
        |(rho - rc n) / d n| < eta) :
    ∀ eta : ℝ, 0 < eta → ∀ᶠ n in atTop,
      ∀ rho ∈ uIcc (ra n) (rb n), ∀ v ∈ uIcc (va n) (vb n),
        |1536 * (mass n / d n ^ 3) * (|rho - rc n| / d n + d n)| < eta := by
  let S : ℕ → Set (ℝ × ℝ) := fun n => uIcc (ra n) (rb n) ×ˢ uIcc (va n) (vb n)
  let F : ℕ → (ℝ × ℝ) → ℝ := fun n z =>
    1536 * (mass n / d n ^ 3) * (|z.1 - rc n| / d n + d n)
  have hseq : ∀ z : ℕ → ℝ × ℝ, (∀ n, z n ∈ S n) →
      Tendsto (fun n => F n (z n)) atTop (𝓝 0) := by
    intro z hz
    have hradz : Tendsto (fun n => ((z n).1 - rc n) / d n) atTop (𝓝 0) := by
      apply Metric.tendsto_nhds.mpr
      intro eta heta
      filter_upwards [hrad eta heta] with n hn
      simpa only [Real.dist_eq, sub_zero] using hn (z n).1 (hz n).1 (z n).2 (hz n).2
    have habsz : Tendsto (fun n => |(z n).1 - rc n| / d n) atTop (𝓝 0) := by
      have hh := hradz.abs
      simp only [abs_zero] at hh
      convert! hh using 1
      funext n
      rw [abs_div, abs_of_pos (hd n)]
    have ht := ((tendsto_const_nhds : Tendsto (fun _ : ℕ => (1536 : ℝ))
      atTop (𝓝 1536)).mul hmc).mul (habsz.add hdt)
    simpa only [F, add_zero, mul_zero] using ht
  have hu := limit_on_moving_sets_of_all_selections S (fun n => (ra n, va n))
    (fun _ => ⟨left_mem_uIcc, left_mem_uIcc⟩) F 0 hseq
  intro eta heta
  filter_upwards [hu eta heta] with n hn
  intro rho hrho v hv
  simpa only [F, Real.dist_eq, sub_zero] using hn (rho, v) ⟨hrho, hv⟩

/-- The right side of the submitted near-source display is uniformly o(1)
on the entire actual lower-triple pair rectangle. -/
theorem normalized_complete_lower_triple_nested_rectangle_near_display_rhs_vanishes
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
    (theta0 : Satellite → ℝ) (htt : Tendsto theta atTop (𝓝 theta0))
    (center : Plane) (htriple : CompleteLimitingSatelliteTriple qLimit 3 center)
    (a b c : TripleLabel) (hab : a < b) (hca : c ≠ a) (hcb : c ≠ b)
    (hpair : Tendsto (fun n => satelliteDistance (satellitesRelative (x n)) a.castSucc b.castSucc /
      tripleLowDiameter (satellitesRelative (x n))) atTop (𝓝 0)) :
    ∀ eta : ℝ, 0 < eta → ∀ᶠ n in atTop,
      ∀ rho ∈ uIcc (r n a.castSucc) (r n b.castSucc),
      ∀ v ∈ uIcc (theta n a.castSucc) (theta n b.castSucc),
        |1536 * (mu n c.castSucc / tripleLowDiameter (satellitesRelative (x n)) ^ 3) *
          (|rho - r n c.castSucc| / tripleLowDiameter (satellitesRelative (x n)) +
            tripleLowDiameter (satellitesRelative (x n)))| < eta := by
  have hgeom := normalized_complete_lower_triple_nested_rectangle_near_geometry_uniform
    eps mu x heps hepst hm hx hconv r theta hr hpolar horder muLimit hmt qLimit hqt
    theta0 htt center htriple a b c hab hca hcb hpair
  have hfull := normalized_complete_lower_triple_nested_precise_scales
    eps mu x heps hepst hm hx hconv r theta hr hpolar horder muLimit hmt qLimit hqt
    theta0 htt center htriple a b c hab hca hcb hpair
  have hq0 : qLimit 0 = center := (htriple 0).mpr (by decide)
  have hdt := tripleLowDiameter_tendsto_zero _ qLimit hqt
    (((htriple 1).mpr (by decide)).trans hq0.symm)
    (((htriple 2).mpr (by decide)).trans hq0.symm)
  apply physical_nested_polar_rectangle_near_display_rhs_vanishes
    (fun n => mu n c.castSucc) (fun n => r n c.castSucc)
    (fun n => r n a.castSucc) (fun n => theta n a.castSucc)
    (fun n => r n b.castSucc) (fun n => theta n b.castSucc)
    (fun n => tripleLowDiameter (satellitesRelative (x n))) (9 / 4)
    (fun n => tripleLowDiameter_pos _ (satellitesRelative_collisionFree _ (hx n).1))
    hdt hfull.2.2.2.2.2.1
  intro eta heta
  filter_upwards [hgeom eta heta] with n hn
  exact fun rho hrho v hv => (hn rho hrho v hv).2.1

/-- Uniform o(1) for the same displayed right side on the actual upper
endpoint block. Its mass-cube bound and first-order geometry are consequences
of the original physical hypotheses, not additional assumptions. -/
theorem normalized_complete_upper_triple_nested_rectangle_near_display_rhs_vanishes
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
    (theta0 : Satellite → ℝ) (htt : Tendsto theta atTop (𝓝 theta0))
    (center : Plane) (htriple : CompleteLimitingSatelliteTriple qLimit 0 center)
    (a b c : TripleLabel) (hab : a < b) (hca : c ≠ a) (hcb : c ≠ b)
    (hpair : Tendsto (fun n => satelliteDistance (satellitesRelative (x n)) a.succ b.succ /
      tripleHighDiameter (satellitesRelative (x n))) atTop (𝓝 0)) :
    ∀ eta : ℝ, 0 < eta → ∀ᶠ n in atTop,
      ∀ rho ∈ uIcc (r n a.succ) (r n b.succ),
      ∀ v ∈ uIcc (theta n a.succ) (theta n b.succ),
        |1536 * (mu n c.succ / tripleHighDiameter (satellitesRelative (x n)) ^ 3) *
          (|rho - r n c.succ| / tripleHighDiameter (satellitesRelative (x n)) +
            tripleHighDiameter (satellitesRelative (x n)))| < eta := by
  have hgeom := normalized_complete_upper_triple_nested_rectangle_near_geometry_uniform
    eps mu x heps hepst hm hx hconv r theta hr hpolar horder muLimit hmt qLimit hqt
    theta0 htt center htriple a b c hab hca hcb hpair
  have hfull := normalized_complete_upper_triple_nested_scale_complete
    eps mu x heps hepst hm hx hconv r theta hr hpolar horder muLimit hmt qLimit hqt
    theta0 htt center htriple a b c hab hca hcb hpair
  have hnu (n : ℕ) : 0 < mu n 1 + mu n 2 + mu n 3 := by
    have h1 := (hm n).1 1
    have h2 := (hm n).1 2
    have h3 := (hm n).1 3
    linarith
  have hscaledXi : Tendsto (fun n => (mu n a.succ + mu n b.succ) /
      tripleHighDiameter (satellitesRelative (x n)) ^ 3) atTop (𝓝 (0 : ℝ)) := by
    convert! hfull.2.1.mul hfull.2.2.1 using 1
    · funext n
      field_simp [ne_of_gt (hnu n)]
    · norm_num
  have hsum (n : ℕ) : mu n 1 + mu n 2 + mu n 3 =
      mu n a.succ + mu n b.succ + mu n c.succ := by
    fin_cases a <;> fin_cases b <;> fin_cases c
    all_goals simp_all
    all_goals ring
  have hmc : Tendsto (fun n => mu n c.succ /
      tripleHighDiameter (satellitesRelative (x n)) ^ 3) atTop (𝓝 (9 / 4 : ℝ)) := by
    convert! hfull.2.2.1.sub hscaledXi using 1
    · funext n
      rw [← sub_div]
      congr 1
      linarith [hsum n]
    · norm_num
  have hd (n : ℕ) : 0 < tripleHighDiameter (satellitesRelative (x n)) := by
    have hcf := satellitesRelative_collisionFree _ (hx n).1
    exact (norm_pos_iff.mpr (sub_ne_zero.mpr (hcf.2 3 2 (by decide)))).trans_le
      (le_max_left _ _)
  have ht (i : Satellite) : Tendsto (fun n => satellitesRelative (x n) i) atTop (𝓝 (qLimit i)) :=
    (continuous_apply i).continuousAt.tendsto.comp hqt
  have hq (i : Satellite) (hi : i ≠ 0) : qLimit i = center := (htriple i).mpr hi
  have ht32 : Tendsto (fun n => ‖satellitesRelative (x n) 3 - satellitesRelative (x n) 2‖)
      atTop (𝓝 0) := by simpa only [hq 3 (by decide), hq 2 (by decide), sub_self, norm_zero]
        using ((ht 3).sub (ht 2)).norm
  have ht31 : Tendsto (fun n => ‖satellitesRelative (x n) 3 - satellitesRelative (x n) 1‖)
      atTop (𝓝 0) := by simpa only [hq 3 (by decide), hq 1 (by decide), sub_self, norm_zero]
        using ((ht 3).sub (ht 1)).norm
  have ht21 : Tendsto (fun n => ‖satellitesRelative (x n) 2 - satellitesRelative (x n) 1‖)
      atTop (𝓝 0) := by simpa only [hq 2 (by decide), hq 1 (by decide), sub_self, norm_zero]
        using ((ht 2).sub (ht 1)).norm
  have hdt : Tendsto (fun n => tripleHighDiameter (satellitesRelative (x n))) atTop (𝓝 0) := by
    simpa only [tripleHighDiameter, max_self] using ht32.max (ht31.max ht21)
  apply physical_nested_polar_rectangle_near_display_rhs_vanishes
    (fun n => mu n c.succ) (fun n => r n c.succ)
    (fun n => r n a.succ) (fun n => theta n a.succ)
    (fun n => r n b.succ) (fun n => theta n b.succ)
    (fun n => tripleHighDiameter (satellitesRelative (x n))) (9 / 4) hd hdt hmc
  intro eta heta
  filter_upwards [hgeom eta heta] with n hn
  exact fun rho hrho v hv => (hn rho hrho v hv).2.1

end DominantFiveBody
