import DominantFiveBody.CollisionTripleInitialScale

/-! # Actual comparable-triple radial scales

Once all three internal distances are comparable to the actual diameter,
each unresolved internal force is bounded directly. The exact midpoint
identity then gives radial differences of order epsilon times diameter.
-/

noncomputable section
open scoped BigOperators Matrix ContDiff
open Filter Set Topology

namespace DominantFiveBody
set_option maxHeartbeats 1200000

theorem PositiveRatio.coordinate_le_one (mu : MassRatio) (hm : PositiveRatio mu) (i : Satellite) :
    mu i ≤ 1 := by
  have h := Finset.single_le_sum (fun j (_ : j ∈ (Finset.univ : Finset Satellite)) => (hm.1 j).le)
    (Finset.mem_univ i)
  rwa [hm.2] at h

theorem newtonTargetField_norm (source target : Plane) (hsep : source ≠ target) :
    ‖newtonTargetField source target‖ = 1 / ‖source - target‖ ^ 2 := by
  have hn : 0 < ‖source - target‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hsep)
  unfold newtonTargetField
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr (pow_pos hn 3))]
  field_simp

theorem separated_moving_source_newton_difference_bound
    (q : ℕ → SatelliteConfiguration) (q0 : SatelliteConfiguration) (hq : Tendsto q atTop (𝓝 q0))
    (a b p : Satellite) (c : Plane) (hqa : q0 a = c) (hqb : q0 b = c) (hsep : q0 p ≠ c) :
    ∃ K : ℝ, 0 < K ∧ ∀ᶠ n in atTop,
      ‖newtonTargetField (q n p) (q n b) - newtonTargetField (q n p) (q n a)‖ ≤
        K * satelliteDistance (q n) a b := by
  have hqat : Tendsto (fun n => q n a) atTop (𝓝 c) := by
    simpa only [Function.comp_def, hqa] using (continuous_apply a).tendsto q0 |>.comp hq
  have hqbt : Tendsto (fun n => q n b) atTop (𝓝 c) := by
    simpa only [Function.comp_def, hqb] using (continuous_apply b).tendsto q0 |>.comp hq
  have hpt : Tendsto (fun n => q n p) atTop (𝓝 (q0 p)) := by
    simpa only [Function.comp_def] using (continuous_apply p).tendsto q0 |>.comp hq
  obtain ⟨K, U, hU, hLip⟩ := ((physicalNewtonTargetField_joint_contDiffAt (q0 p) c hsep).of_le
    (by norm_num : (1 : ℕ∞ω) ≤ ∞)).exists_lipschitzOnWith
  refine ⟨(K : ℝ) + 1, by positivity, ?_⟩
  filter_upwards [(hpt.prodMk_nhds hqat).eventually hU, (hpt.prodMk_nhds hqbt).eventually hU] with n hUa hUb
  have h := hLip.dist_le_mul _ hUb _ hUa
  have hd : dist (q n p, q n b) (q n p, q n a) = satelliteDistance (q n) a b := by
    rw [Prod.dist_eq, dist_self, max_eq_right dist_nonneg, dist_eq_norm, norm_sub_rev]
    rfl
  rw [hd, dist_eq_norm] at h
  exact h.trans (mul_le_mul_of_nonneg_right (by linarith : (K : ℝ) ≤ (K : ℝ) + 1) (norm_nonneg _))

theorem internal_newton_norm_bound (d eta M : ℝ) (mu : MassRatio) (q : SatelliteConfiguration)
    (a b c : Satellite) (hm : PositiveRatio mu) (hd : 0 < d) (heta : 0 < eta) (hM : 0 < M)
    (hac : a ≠ c) (hbc : b ≠ c) (hcf : RelativeCollisionFree q)
    (hca : eta * d ≤ satelliteDistance q c a) (hcb : eta * d ≤ satelliteDistance q c b)
    (hnu : (mu a + mu b + mu c) / d ^ 3 ≤ M) :
    ‖mu c • (newtonTargetField (q c) (q b) - newtonTargetField (q c) (q a))‖ ≤
      (2 * M / eta ^ 2) * d := by
  have hnua : mu c ≤ mu a + mu b + mu c := by linarith [hm.1 a, hm.1 b]
  have hmass : mu c ≤ M * d ^ 3 := hnua.trans ((div_le_iff₀ (pow_pos hd 3)).mp hnu)
  have hdenA : 0 < satelliteDistance q c a := norm_pos_iff.mpr (sub_ne_zero.mpr (hcf.2 c a hac.symm))
  have hdenB : 0 < satelliteDistance q c b := norm_pos_iff.mpr (sub_ne_zero.mpr (hcf.2 c b hbc.symm))
  have hpowA := pow_le_pow_left₀ (mul_pos heta hd).le hca 2
  have hpowB := pow_le_pow_left₀ (mul_pos heta hd).le hcb 2
  have hnormA : ‖newtonTargetField (q c) (q a)‖ ≤ 1 / (eta * d) ^ 2 := by
    rw [newtonTargetField_norm _ _ (hcf.2 c a hac.symm)]
    exact one_div_le_one_div_of_le (sq_pos_of_pos (mul_pos heta hd)) hpowA
  have hnormB : ‖newtonTargetField (q c) (q b)‖ ≤ 1 / (eta * d) ^ 2 := by
    rw [newtonTargetField_norm _ _ (hcf.2 c b hbc.symm)]
    exact one_div_le_one_div_of_le (sq_pos_of_pos (mul_pos heta hd)) hpowB
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos (hm.1 c)]
  calc
    _ ≤ mu c * (‖newtonTargetField (q c) (q b)‖ + ‖newtonTargetField (q c) (q a)‖) :=
      mul_le_mul_of_nonneg_left (norm_sub_le _ _) (hm.1 c).le
    _ ≤ (M * d ^ 3) * (1 / (eta * d) ^ 2 + 1 / (eta * d) ^ 2) :=
      mul_le_mul hmass (add_le_add hnormB hnormA) (by positivity) (by positivity)
    _ = (2 * M / eta ^ 2) * d := by field_simp; ring

theorem pair_coefficient_le_of_triple_cube (d eta M : ℝ) (mu : MassRatio) (q : SatelliteConfiguration)
    (a b c : Satellite) (hm : PositiveRatio mu) (hd : 0 < d) (heta : 0 < eta) (hM : 0 < M)
    (hcf : RelativeCollisionFree q) (hab : a ≠ b)
    (habd : eta * d ≤ satelliteDistance q a b)
    (hnu : (mu a + mu b + mu c) / d ^ 3 ≤ M) :
    (mu a + mu b) / satelliteDistance q a b ^ 3 ≤ M / eta ^ 3 := by
  have hden : 0 < satelliteDistance q a b := norm_pos_iff.mpr (sub_ne_zero.mpr (hcf.2 a b hab))
  have hmass : mu a + mu b ≤ M * d ^ 3 := by
    have h := (div_le_iff₀ (pow_pos hd 3)).mp hnu
    linarith [hm.1 c]
  have hpow := pow_le_pow_left₀ (mul_pos heta hd).le habd 3
  apply (div_le_iff₀ (pow_pos hden 3)).mpr
  have hscale := mul_le_mul_of_nonneg_left hpow (div_pos hM (pow_pos heta 3)).le
  have he : M / eta ^ 3 * (eta * d) ^ 3 = M * d ^ 3 := by field_simp
  rw [he] at hscale
  exact hmass.trans hscale

theorem physical_pair_radial_bound_absolute (eps L d : ℝ) (mu r theta : Satellite → ℝ)
    (a b : Satellite) (hab : a ≠ b) (hr : ∀ i, 0 < r i) (heps : 0 ≤ eps)
    (hroot : ∀ i, vectorResidual eps mu (polarSatellites r theta) i = 0)
    (hlambda : eps * (mu a + mu b) / satelliteDistance (polarSatellites r theta) a b ^ 3 ≤ 1 / 2)
    (hcos : 1 / 2 ≤ Real.cos ((theta b - theta a) / 2))
    (hP : ‖pairExteriorField mu (polarSatellites r theta) a b (polarPoint (r b) (theta b)) -
      pairExteriorField mu (polarSatellites r theta) a b (polarPoint (r a) (theta a))‖ ≤ L * d) :
    |r b - r a| ≤ 4 * L * eps * d := by
  let lambda := eps * (mu a + mu b) / satelliteDistance (polarSatellites r theta) a b ^ 3
  let A := 1 + (r a + r b) / (r a ^ 2 * r b ^ 2) - lambda
  have hA : 1 / 2 ≤ A := by
    have hp : 0 < (r a + r b) / (r a ^ 2 * r b ^ 2) := div_pos (add_pos (hr a) (hr b))
      (mul_pos (sq_pos_of_pos (hr a)) (sq_pos_of_pos (hr b)))
    dsimp [A, lambda]
    linarith
  have hmid := physical_pair_midpoint_identity eps mu r theta a b hab hr hroot
  rw [primaryRadialScalar_difference (r a) (r b) lambda (hr a).ne' (hr b).ne'] at hmid
  change (r b - r a) * A * Real.cos ((theta b - theta a) / 2) = _ at hmid
  have heq := congrArg abs hmid
  rw [abs_mul, abs_mul, abs_of_nonneg (show 0 ≤ A by linarith),
    abs_of_nonneg (show 0 ≤ Real.cos ((theta b - theta a) / 2) by linarith),
    abs_mul, abs_neg, abs_of_nonneg heps] at heq
  have hinner := abs_real_inner_le_norm
    (pairExteriorField mu (polarSatellites r theta) a b (polarPoint (r b) (theta b)) -
      pairExteriorField mu (polarSatellites r theta) a b (polarPoint (r a) (theta a)))
    (polarPoint 1 ((theta a + theta b) / 2))
  rw [polarPoint_norm, abs_one, mul_one] at hinner
  have hupper := mul_le_mul_of_nonneg_left (hinner.trans hP) heps
  have hlower : |r b - r a| / 4 ≤ |r b - r a| * A * Real.cos ((theta b - theta a) / 2) := by
    have h1 := mul_le_mul_of_nonneg_left hA (abs_nonneg (r b - r a))
    have h2 := mul_le_mul_of_nonneg_left hcos
      (mul_nonneg (abs_nonneg (r b - r a)) (by linarith : 0 ≤ A))
    nlinarith
  rw [← heq] at hupper
  nlinarith

theorem comparable_triple_pair_radial_tendsto_zero
    (eps : ℕ → ℝ) (mu r theta : ℕ → Satellite → ℝ) (d : ℕ → ℝ)
    (heps : ∀ n, 0 < eps n) (hepst : Tendsto eps atTop (𝓝 0))
    (hm : ∀ n, PositiveRatio (mu n)) (hr : ∀ n i, 0 < r n i)
    (hroot : ∀ n i, vectorResidual (eps n) (mu n) (polarSatellites (r n) (theta n)) i = 0)
    (hcf : ∀ n, RelativeCollisionFree (polarSatellites (r n) (theta n)))
    (q0 : SatelliteConfiguration)
    (hqt : Tendsto (fun n => polarSatellites (r n) (theta n)) atTop (𝓝 q0))
    (a b c p : Satellite) (hab : a ≠ b) (hca : c ≠ a) (hcb : c ≠ b)
    (hpa : p ≠ a) (hpb : p ≠ b) (hcp : c ≠ p) (center : Plane)
    (hqa : q0 a = center) (hqb : q0 b = center) (hsep : q0 p ≠ center)
    (hgap : Tendsto (fun n => theta n b - theta n a) atTop (𝓝 0))
    (eta M : ℝ) (heta : 0 < eta) (hM : 0 < M) (hd : ∀ n, 0 < d n)
    (hscale : ∀ᶠ n in atTop,
      satelliteDistance (polarSatellites (r n) (theta n)) a b ≤ d n ∧
      eta * d n ≤ satelliteDistance (polarSatellites (r n) (theta n)) a b ∧
      eta * d n ≤ satelliteDistance (polarSatellites (r n) (theta n)) c a ∧
      eta * d n ≤ satelliteDistance (polarSatellites (r n) (theta n)) c b ∧
      (mu n a + mu n b + mu n c) / d n ^ 3 ≤ M) :
    Tendsto (fun n => (r n b - r n a) / d n) atTop (𝓝 0) := by
  classical
  let q := fun n => polarSatellites (r n) (theta n)
  have hcMem : c ∈ pairExteriorLabels a b := Finset.mem_erase.mpr ⟨hcb, Finset.mem_erase.mpr ⟨hca, Finset.mem_univ c⟩⟩
  have hpMem : p ∈ pairExteriorLabels a b := Finset.mem_erase.mpr ⟨hpb, Finset.mem_erase.mpr ⟨hpa, Finset.mem_univ p⟩⟩
  have hset := pairExteriorLabels_eq_two a b c p hab hcMem hpMem hcp
  obtain ⟨K, hK, hNewton⟩ := separated_moving_source_newton_difference_bound q q0 hqt a b p center hqa hqb hsep
  let L := 2 * M / eta ^ 2 + K
  have hL : 0 < L := by dsimp [L]; positivity
  have hP : ∀ᶠ n in atTop,
      ‖pairExteriorField (mu n) (q n) a b (q n b) - pairExteriorField (mu n) (q n) a b (q n a)‖ ≤ L * d n := by
    filter_upwards [hscale, hNewton] with n hn hN
    have hnear := internal_newton_norm_bound (d n) eta M (mu n) (q n) a b c
      (hm n) (hd n) heta hM hca.symm hcb.symm (hcf n) hn.2.2.1 hn.2.2.2.1 hn.2.2.2.2
    have heq : pairExteriorField (mu n) (q n) a b (q n b) - pairExteriorField (mu n) (q n) a b (q n a) =
        mu n c • (newtonTargetField (q n c) (q n b) - newtonTargetField (q n c) (q n a)) +
        mu n p • (newtonTargetField (q n p) (q n b) - newtonTargetField (q n p) (q n a)) := by
      simp only [pairExteriorField_eq_newton_sum, hset, Finset.sum_pair hcp]
      module
    rw [heq]
    have hpNorm : ‖mu n p • (newtonTargetField (q n p) (q n b) - newtonTargetField (q n p) (q n a))‖ ≤ K * d n := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos ((hm n).1 p)]
      have h1 := mul_le_mul_of_nonneg_left (hN.trans (mul_le_mul_of_nonneg_left hn.1 hK.le)) ((hm n).1 p).le
      have h2 := mul_le_mul_of_nonneg_right (PositiveRatio.coordinate_le_one (mu n) (hm n) p)
        (mul_pos hK (hd n)).le
      exact h1.trans (by simpa only [one_mul] using h2)
    calc
      _ ≤ ‖mu n c • (newtonTargetField (q n c) (q n b) - newtonTargetField (q n c) (q n a))‖ +
        ‖mu n p • (newtonTargetField (q n p) (q n b) - newtonTargetField (q n p) (q n a))‖ := norm_add_le _ _
      _ ≤ (2 * M / eta ^ 2) * d n + K * d n := add_le_add hnear hpNorm
      _ = L * d n := by dsimp [L]; ring
  have hLambda : ∀ᶠ n in atTop,
      eps n * (mu n a + mu n b) / satelliteDistance (q n) a b ^ 3 ≤ 1 / 2 := by
    have he : Tendsto (fun n => eps n * (M / eta ^ 3)) atTop (𝓝 0) := by simpa using hepst.mul_const (M / eta ^ 3)
    filter_upwards [hscale, he.eventually (Iio_mem_nhds (by norm_num : (0 : ℝ) < 1 / 2))] with n hn heN
    have hcoef := pair_coefficient_le_of_triple_cube (d n) eta M (mu n) (q n) a b c
      (hm n) (hd n) heta hM (hcf n) hab hn.2.1 hn.2.2.2.2
    have hscaled : eps n * (mu n a + mu n b) / satelliteDistance (q n) a b ^ 3 ≤ eps n * (M / eta ^ 3) := by
      simpa only [mul_div_assoc] using mul_le_mul_of_nonneg_left hcoef (heps n).le
    exact hscaled.trans heN.le
  have hcos : Tendsto (fun n => Real.cos ((theta n b - theta n a) / 2)) atTop (𝓝 1) := by
    simpa only [zero_div, Real.cos_zero, Function.comp_def] using Real.continuous_cos.continuousAt.tendsto.comp (hgap.div_const 2)
  have hbound : ∀ᶠ n in atTop, |r n b - r n a| ≤ 4 * L * eps n * d n := by
    filter_upwards [hP, hLambda, hcos.eventually (Ioi_mem_nhds (by norm_num : (1 / 2 : ℝ) < 1))] with n hPN hLambdaN hcosN
    exact physical_pair_radial_bound_absolute (eps n) L (d n) (mu n) (r n) (theta n) a b hab
      (hr n) (heps n).le (hroot n) hLambdaN hcosN.le hPN
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  have hupp : ∀ᶠ n in atTop, ‖(r n b - r n a) / d n‖ ≤ 4 * L * eps n := by
    filter_upwards [hbound] with n hn
    rw [Real.norm_eq_abs, abs_div, abs_of_pos (hd n)]
    exact (div_le_iff₀ (hd n)).mpr hn
  have hlim : Tendsto (fun n => 4 * L * eps n) atTop (𝓝 0) := by simpa using hepst.const_mul (4 * L)
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hlim
    (Eventually.of_forall (fun n => norm_nonneg _)) hupp

theorem tripleLowDiameter_bound (q : SatelliteConfiguration) (i j : TripleLabel) :
    satelliteDistance q i.castSucc j.castSucc ≤ tripleLowDiameter q := by
  have h := tripleLowDiameter_bounds q
  have hn : 0 ≤ tripleLowDiameter q := (norm_nonneg _).trans h.1
  fin_cases i <;> fin_cases j
  · simpa only [satelliteDistance, sub_self, norm_zero] using hn
  · change ‖q 0 - q 1‖ ≤ _; rw [norm_sub_rev]; exact h.1
  · change ‖q 0 - q 2‖ ≤ _; rw [norm_sub_rev]; exact h.2.1
  · exact h.1
  · simpa only [satelliteDistance, sub_self, norm_zero] using hn
  · change ‖q 1 - q 2‖ ≤ _; rw [norm_sub_rev]; exact h.2.2
  · exact h.2.1
  · exact h.2.2
  · simpa only [satelliteDistance, sub_self, norm_zero] using hn

theorem three_distinct_low_masses_sum (mu : MassRatio) (a b c : TripleLabel)
    (hab : a ≠ b) (hca : c ≠ a) (hcb : c ≠ b) :
    mu a.castSucc + mu b.castSucc + mu c.castSucc = mu 0 + mu 1 + mu 2 := by
  fin_cases a <;> fin_cases b <;> fin_cases c <;> simp_all <;> ring

/-- Actual comparable complete triples have radial differences o(d).
Only the selected comparable-distance case is required as a scale-class
input; all force bounds come from the actual normalized configurations. -/
theorem normalized_complete_lower_triple_regular_radial_limits
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
    ∀ i j : TripleLabel, Tendsto (fun n => (r n j.castSucc - r n i.castSucc) /
      tripleLowDiameter (satellitesRelative (x n))) atTop (𝓝 0) := by
  classical
  obtain ⟨_, M, _, hM, hinitial⟩ := normalized_complete_lower_triple_initial_scales eps mu x heps hepst hm hx
    hconv r theta hr hpolar horder muLimit hmt qLimit hqt theta0 htheta center htriple
  obtain ⟨_, hunit, hmono, _, hspan⟩ := normalized_ordered_polar_limit_geometry eps mu x heps hepst hm hx
    r theta hr hpolar horder muLimit hmt qLimit hqt theta0 htheta
  have hbound (i j : Satellite) : |theta0 i - theta0 j| < Real.pi := by
    have hiLo := hmono (Fin.zero_le i)
    have hjLo := hmono (Fin.zero_le j)
    have hiHi := hmono (Fin.le_last i)
    have hjHi := hmono (Fin.le_last j)
    change theta0 i ≤ theta0 3 at hiHi
    change theta0 j ≤ theta0 3 at hjHi
    exact abs_lt.mpr ⟨by linarith, by linarith⟩
  have hthetaEq (i j : TripleLabel) : theta0 i.castSucc = theta0 j.castSucc := by
    have hip : i.castSucc ≠ (3 : Satellite) := by fin_cases i <;> decide
    have hjp : j.castSucc ≠ (3 : Satellite) := by fin_cases j <;> decide
    by_contra hne
    apply polarUnit_ne_of_angle_ne (theta0 i.castSucc) (theta0 j.castSucc) hne
      (by simpa only [abs_sub_comm] using hbound i.castSucc j.castSucc)
    rw [← hunit i.castSucc, ← hunit j.castSucc, (htriple i.castSucc).mpr hip, (htriple j.castSucc).mpr hjp]
  have hvectorRoots (n : ℕ) : ∀ k, vectorResidual (eps n) (mu n) (polarSatellites (r n) (theta n)) k = 0 := by
    rw [← hpolar n]
    exact vectorResidual_zero_of_normalized (eps n) (mu n) (x n) (hx n)
  have hcf (n : ℕ) : RelativeCollisionFree (polarSatellites (r n) (theta n)) := by
    rw [← hpolar n]
    exact satellitesRelative_collisionFree (x n) (hx n).1
  have hqpolar : Tendsto (fun n => polarSatellites (r n) (theta n)) atTop (𝓝 qLimit) := by
    simpa only [hpolar] using hqt
  have hd (n : ℕ) : 0 < tripleLowDiameter (satellitesRelative (x n)) :=
    tripleLowDiameter_pos _ (satellitesRelative_collisionFree (x n) (hx n).1)
  intro i j
  by_cases hij : i = j
  · subst j
    simpa only [sub_self, zero_div] using (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (𝓝 0))
  obtain ⟨c, hci, hcj⟩ := Fin.exists_ne_and_ne_of_two_lt i j (by decide)
  have castNe {a b : TripleLabel} (hne : a ≠ b) : a.castSucc ≠ b.castSucc := by
    intro he
    apply hne
    apply Fin.ext
    exact congrArg (fun k : Satellite => k.val) he
  have lowNe (a : TripleLabel) : (3 : Satellite) ≠ a.castSucc := by fin_cases a <;> decide
  have hqa : qLimit i.castSucc = center := (htriple i.castSucc).mpr (lowNe i).symm
  have hqb : qLimit j.castSucc = center := (htriple j.castSucc).mpr (lowNe j).symm
  have hsep : qLimit 3 ≠ center := fun he => (htriple 3).mp he rfl
  have hgap : Tendsto (fun n => theta n j.castSucc - theta n i.castSucc) atTop (𝓝 0) := by
    have hi := (continuous_apply i.castSucc).tendsto theta0 |>.comp htheta
    have hj := (continuous_apply j.castSucc).tendsto theta0 |>.comp htheta
    simpa only [hthetaEq i j, sub_self, Function.comp_def] using hj.sub hi
  apply comparable_triple_pair_radial_tendsto_zero eps mu r theta
    (fun n => tripleLowDiameter (satellitesRelative (x n))) heps hepst hm hr hvectorRoots hcf
    qLimit hqpolar i.castSucc j.castSucc c.castSucc 3 (castNe hij) (castNe hci) (castNe hcj)
    (lowNe i) (lowNe j) (lowNe c).symm center hqa hqb hsep hgap eta M heta hM hd
  filter_upwards [hcomparable, hinitial] with n hn hinit
  rw [← hpolar n]
  have hmass : (mu n i.castSucc + mu n j.castSucc + mu n c.castSucc) /
      tripleLowDiameter (satellitesRelative (x n)) ^ 3 ≤ M := by
    rw [three_distinct_low_masses_sum (mu n) i j c hij hci hcj]
    have h3 := PositiveRatio.coordinate_le_one (mu n) (hm n) 3
    have hC : M * mu n 3 ≤ M := by
      simpa only [mul_one] using mul_le_mul_of_nonneg_left h3 hM.le
    exact hinit.2.2.trans hC
  exact ⟨tripleLowDiameter_bound _ i j, hn i j hij, hn c i hci, hn c j hcj, hmass⟩

end DominantFiveBody
