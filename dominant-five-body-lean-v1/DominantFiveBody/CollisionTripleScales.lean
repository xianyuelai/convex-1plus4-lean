import DominantFiveBody.CollisionClassification
import DominantFiveBody.TripleActualCaptureLimits

/-! # Actual complete-triple collision estimates

Source Proposition `prop:triple-scale`. The current cluster weights are
used before taking a limit. All angular equations remain mass-divided;
the exterior mass and the cluster mass are cancelled only when positive.
-/

noncomputable section
open scoped BigOperators Matrix ContDiff
open Filter Set Topology

namespace DominantFiveBody
open Coorbital
set_option maxHeartbeats 800000

def tripleClusterLabels (p : Satellite) : Finset Satellite := Finset.univ.erase p

def actualTripleMass (mu : MassRatio) (p : Satellite) : ℝ :=
  ∑ i ∈ tripleClusterLabels p, mu i

theorem tripleClusterLabels_nonempty (p : Satellite) : (tripleClusterLabels p).Nonempty := by
  fin_cases p <;> decide

theorem actualTripleMass_pos (mu : MassRatio) (hm : PositiveRatio mu) (p : Satellite) :
    0 < actualTripleMass mu p :=
  Finset.sum_pos (fun i _ => hm.1 i) (tripleClusterLabels_nonempty p)

theorem actualTripleMass_add_exterior (mu : MassRatio) (hm : PositiveRatio mu) (p : Satellite) :
    actualTripleMass mu p + mu p = 1 := by
  rw [actualTripleMass, tripleClusterLabels, Finset.sum_erase_add _ _ (Finset.mem_univ p), hm.2]

/-- The original weighted cut cancels every triple internal interaction.
The unique exterior mass is positive and is cancelled before any limit. -/
theorem physical_triple_weighted_full_angular_average (eps : ℝ) (mu r theta : Satellite → ℝ)
    (p : Satellite) (hmp : 0 < mu p)
    (hroot : ∀ i, angularResidual eps mu r theta i = 0) :
    ∑ i ∈ tripleClusterLabels p, mu i *
      physicalSourceFullAngularField eps (r p) (theta p) (r i) (theta i) = 0 := by
  have hcut := full_angular_cut eps mu r theta hroot (tripleClusterLabels p)
  have hcomp : (tripleClusterLabels p)ᶜ = {p} := by ext i; simp [tripleClusterLabels]
  rw [hcomp] at hcut
  simp only [Finset.sum_singleton, fullAngularPair] at hcut
  have heq : (∑ i ∈ tripleClusterLabels p, mu i * mu p * fullAngularMatrix eps r theta i p) =
      (∑ i ∈ tripleClusterLabels p, mu i * fullAngularMatrix eps r theta i p) * mu p := by
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro i _
    ring
  rw [heq] at hcut
  simpa only [fullAngularMatrix_eq_physicalSourceFullAngularField] using
    (mul_eq_zero.mp hcut).resolve_right hmp.ne'

/-- A finite average with current positive weights has the common limit
of its summands, even if all weights vanish or oscillate. -/
theorem current_positive_finset_weighted_average_tendsto {ι : Type*}
    (S : Finset ι) (hS : S.Nonempty) (w A : ℕ → ι → ℝ) (L : ℝ)
    (hw : ∀ n, ∀ i ∈ S, 0 < w n i)
    (hA : ∀ i ∈ S, Tendsto (fun n => A n i) atTop (𝓝 L)) :
    Tendsto (fun n => (∑ i ∈ S, w n i * A n i) / (∑ i ∈ S, w n i)) atTop (𝓝 L) := by
  have hsum (n : ℕ) : 0 < ∑ i ∈ S, w n i := Finset.sum_pos (hw n) hS
  apply tendsto_order.mpr
  constructor
  · intro c hc
    have hall : ∀ᶠ n in atTop, ∀ i ∈ S, c < A n i := by
      exact (eventually_all_finset S).mpr (fun i hi => (hA i hi).eventually (Ioi_mem_nhds hc))
    filter_upwards [hall] with n hn
    apply (lt_div_iff₀ (hsum n)).mpr
    rw [Finset.mul_sum]
    apply Finset.sum_lt_sum_of_nonempty hS
    intro i hi
    nlinarith [mul_lt_mul_of_pos_left (hn i hi) (hw n i hi)]
  · intro c hc
    have hall : ∀ᶠ n in atTop, ∀ i ∈ S, A n i < c := by
      exact (eventually_all_finset S).mpr (fun i hi => (hA i hi).eventually (Iio_mem_nhds hc))
    filter_upwards [hall] with n hn
    apply (div_lt_iff₀ (hsum n)).mpr
    rw [Finset.mul_sum]
    apply Finset.sum_lt_sum_of_nonempty hS
    intro i hi
    nlinarith [mul_lt_mul_of_pos_left (hn i hi) (hw n i hi)]

theorem physicalSourceFullAngularField_unit_kernel (angle psi : ℝ)
    (hne : angle ≠ psi) (hpi : |angle - psi| < Real.pi) :
    physicalSourceFullAngularField 0 1 angle 1 psi = coorbitalKernel (angle - psi) := by
  simpa [physicalSourceFullAngularField, physicalSourceAngularField] using
    physicalSourceAngularField_unit_kernel angle psi hne hpi

/-- A complete triple's unique exterior angle is at the actual kernel
zero. Neither the cluster weights nor the exterior weight need a positive
limit, and no limiting mass shares are assumed. -/
theorem actual_triple_exterior_kernel_zero
    (eps : ℕ → ℝ) (mu r theta : ℕ → Satellite → ℝ)
    (heps : Tendsto eps atTop (𝓝 0)) (hm : ∀ n, PositiveRatio (mu n))
    (hr : ∀ i, Tendsto (fun n => r n i) atTop (𝓝 1))
    (theta0 : Satellite → ℝ) (htheta : Tendsto theta atTop (𝓝 theta0))
    (p : Satellite) (psi : ℝ) (hcluster : ∀ i, i ≠ p → theta0 i = psi)
    (hne : theta0 p ≠ psi) (hpi : |theta0 p - psi| < Real.pi)
    (hroot : ∀ n i, angularResidual (eps n) (mu n) (r n) (theta n) i = 0) :
    coorbitalKernel (theta0 p - psi) = 0 := by
  have htat (i : Satellite) : Tendsto (fun n => theta n i) atTop (𝓝 (theta0 i)) := by
    simpa only [Function.comp_def] using (continuous_apply i).tendsto theta0 |>.comp htheta
  have hterm (i : Satellite) (hi : i ∈ tripleClusterLabels p) :
      Tendsto (fun n => physicalSourceFullAngularField (eps n) (r n p) (theta n p) (r n i) (theta n i))
        atTop (𝓝 (coorbitalKernel (theta0 p - psi))) := by
    have hci := hcluster i (Finset.mem_erase.mp hi).1
    have hc := (physicalSourceFullAngularField_joint_contDiffAt
      (0, ((1, theta0 p), (1, psi))) (by norm_num)
      (polarUnit_ne_of_angle_ne (theta0 p) psi hne (by simpa only [abs_sub_comm] using hpi))).continuousAt
    have ht := hc.tendsto.comp (heps.prodMk_nhds (((hr p).prodMk_nhds (htat p)).prodMk_nhds
      ((hr i).prodMk_nhds (by simpa only [hci] using htat i))))
    simpa only [Function.comp_def, physicalSourceFullAngularField_unit_kernel (theta0 p) psi hne hpi] using ht
  have hmean := current_positive_finset_weighted_average_tendsto
    (tripleClusterLabels p) (tripleClusterLabels_nonempty p) mu
    (fun n i => physicalSourceFullAngularField (eps n) (r n p) (theta n p) (r n i) (theta n i))
    (coorbitalKernel (theta0 p - psi)) (fun n i _ => (hm n).1 i) hterm
  have hzero : Tendsto (fun n => (∑ i ∈ tripleClusterLabels p, mu n i *
      physicalSourceFullAngularField (eps n) (r n p) (theta n p) (r n i) (theta n i)) /
      (∑ i ∈ tripleClusterLabels p, mu n i)) atTop (𝓝 0) := by
    simp only [physical_triple_weighted_full_angular_average _ _ _ _ p ((hm _).1 p) (hroot _), zero_div]
    exact tendsto_const_nhds
  exact tendsto_nhds_unique hmean hzero

theorem actual_triple_exterior_gap
    (eps : ℕ → ℝ) (mu r theta : ℕ → Satellite → ℝ)
    (heps : Tendsto eps atTop (𝓝 0)) (hm : ∀ n, PositiveRatio (mu n))
    (hr : ∀ i, Tendsto (fun n => r n i) atTop (𝓝 1))
    (theta0 : Satellite → ℝ) (htheta : Tendsto theta atTop (𝓝 theta0))
    (p : Satellite) (psi : ℝ) (hcluster : ∀ i, i ≠ p → theta0 i = psi)
    (hne : theta0 p ≠ psi) (hpi : |theta0 p - psi| < Real.pi)
    (hroot : ∀ n i, angularResidual (eps n) (mu n) (r n) (theta n) i = 0) :
    |theta0 p - psi| = h :=
  (coorbitalKernel_zero_iff_abs_eq_h (sub_ne_zero.mpr hne) hpi).mp
    (actual_triple_exterior_kernel_zero eps mu r theta heps hm hr theta0 htheta p psi hcluster hne hpi hroot)

theorem ordered_complete_triple_is_endpoint (theta0 : Satellite → ℝ) (hmono : Monotone theta0)
    (p : Satellite) (psi : ℝ) (hcluster : ∀ i, i ≠ p → theta0 i = psi)
    (hne : theta0 p ≠ psi) : p = 0 ∨ p = 3 := by
  fin_cases p
  · exact Or.inl rfl
  · have h0 := hcluster 0 (by decide)
    have h3 := hcluster 3 (by decide)
    have hlo := hmono (by decide : (0 : Satellite) ≤ 1)
    have hhi := hmono (by decide : (1 : Satellite) ≤ 3)
    exact False.elim (hne (by rw [h0] at hlo; rw [h3] at hhi; exact le_antisymm hhi hlo))
  · have h0 := hcluster 0 (by decide)
    have h3 := hcluster 3 (by decide)
    have hlo := hmono (by decide : (0 : Satellite) ≤ 2)
    have hhi := hmono (by decide : (2 : Satellite) ≤ 3)
    exact False.elim (hne (by rw [h0] at hlo; rw [h3] at hhi; exact le_antisymm hhi hlo))
  · exact Or.inr rfl

/-- The actual normalized collision sequence supplies both the unit
radii and the angular equations used in the exterior-gap theorem. -/
theorem normalized_complete_triple_exterior_gap
    (eps : ℕ → ℝ) (mu : ℕ → MassRatio) (x : ℕ → Configuration)
    (heps : ∀ n, 0 < eps n) (hepst : Tendsto eps atTop (𝓝 0))
    (hm : ∀ n, PositiveRatio (mu n))
    (hx : ∀ n, NormalizedCentralConfiguration (masses (eps n) (mu n)) (x n))
    (r theta : ℕ → Satellite → ℝ) (hr : ∀ n i, 0 < r n i)
    (hpolar : ∀ n, satellitesRelative (x n) = polarSatellites (r n) (theta n))
    (horder : ∀ n i j, i < j → 0 < theta n j - theta n i ∧ theta n j - theta n i < Real.pi)
    (theta0 : Satellite → ℝ) (htheta : Tendsto theta atTop (𝓝 theta0))
    (p : Satellite) (psi : ℝ) (hcluster : ∀ i, i ≠ p → theta0 i = psi)
    (hne : theta0 p ≠ psi) (hpi : |theta0 p - psi| < Real.pi) :
    (p = 0 ∨ p = 3) ∧ |theta0 p - psi| = h := by
  have hmono : Monotone theta0 := by
    intro i j hij
    rcases hij.eq_or_lt with rfl | hlt
    · rfl
    · have hi := (continuous_apply i).tendsto theta0 |>.comp htheta
      have hj := (continuous_apply j).tendsto theta0 |>.comp htheta
      exact sub_nonneg.mp (ge_of_tendsto (hj.sub hi)
        (Eventually.of_forall (fun n => (horder n i j hlt).1.le)))
  have hrat (i : Satellite) : Tendsto (fun n => r n i) atTop (𝓝 1) := by
    convert! dominant_satellite_radius_tendsto eps mu x heps hepst hm hx i using 1
    funext n
    rw [hpolar n]
    simp only [polarSatellites, polarPoint_norm, abs_of_pos (hr n i)]
  have hroots (n : ℕ) := (polarResiduals_zero_of_normalized (eps n) (mu n) (x n) (hx n)
    (hm n) (heps n) (r n) (theta n) (hr n) (hpolar n)).2
  exact ⟨ordered_complete_triple_is_endpoint theta0 hmono p psi hcluster hne,
    actual_triple_exterior_gap eps mu r theta hepst hm hrat theta0 htheta p psi hcluster hne hpi hroots⟩

/-- Full physical triple entry: the angle separation and endpoint class
are derived from the actual collision equivalence class. -/
theorem normalized_complete_triple_limiting_exterior
    (eps : ℕ → ℝ) (mu : ℕ → MassRatio) (x : ℕ → Configuration)
    (heps : ∀ n, 0 < eps n) (hepst : Tendsto eps atTop (𝓝 0))
    (hm : ∀ n, PositiveRatio (mu n))
    (hx : ∀ n, NormalizedCentralConfiguration (masses (eps n) (mu n)) (x n))
    (r theta : ℕ → Satellite → ℝ) (hr : ∀ n i, 0 < r n i)
    (hpolar : ∀ n, satellitesRelative (x n) = polarSatellites (r n) (theta n))
    (horder : ∀ n i j, i < j → 0 < theta n j - theta n i ∧ theta n j - theta n i < Real.pi)
    (muLimit : MassRatio) (hmt : Tendsto mu atTop (𝓝 muLimit))
    (qLimit : SatelliteConfiguration)
    (hqt : Tendsto (fun n => satellitesRelative (x n)) atTop (𝓝 qLimit))
    (theta0 : Satellite → ℝ) (htheta : Tendsto theta atTop (𝓝 theta0))
    (p : Satellite) (c : Plane) (htriple : CompleteLimitingSatelliteTriple qLimit p c) :
    (p = 0 ∨ p = 3) ∧ ∀ i, i ≠ p → |theta0 p - theta0 i| = h := by
  obtain ⟨_, hunit, hmono, _, hspan⟩ := normalized_ordered_polar_limit_geometry eps mu x
    heps hepst hm hx r theta hr hpolar horder muLimit hmt qLimit hqt theta0 htheta
  have hbound (i j : Satellite) : |theta0 i - theta0 j| < Real.pi := by
    have hiLo := hmono (Fin.zero_le i)
    have hjLo := hmono (Fin.zero_le j)
    have hiHi := hmono (Fin.le_last i)
    have hjHi := hmono (Fin.le_last j)
    change theta0 i ≤ theta0 3 at hiHi
    change theta0 j ≤ theta0 3 at hjHi
    exact abs_lt.mpr ⟨by linarith, by linarith⟩
  obtain ⟨a, ha⟩ := tripleClusterLabels_nonempty p
  have hap : a ≠ p := (Finset.mem_erase.mp ha).1
  have hca : qLimit a = c := (htriple a).mpr hap
  have hcluster (i : Satellite) (hi : i ≠ p) : theta0 i = theta0 a := by
    by_contra hne
    apply polarUnit_ne_of_angle_ne (theta0 i) (theta0 a) hne (by simpa only [abs_sub_comm] using hbound i a)
    rw [← hunit i, ← hunit a, (htriple i).mpr hi, hca]
  have hne : theta0 p ≠ theta0 a := by
    intro he
    have hpc : qLimit p = c := by rw [hunit p, he, ← hunit a, hca]
    exact (htriple p).mp hpc rfl
  obtain ⟨hend, hgap⟩ := normalized_complete_triple_exterior_gap eps mu x heps hepst hm hx
    r theta hr hpolar horder theta0 htheta p (theta0 a) hcluster hne (hbound p a)
  refine ⟨hend, ?_⟩
  intro i hi
  rwa [hcluster i hi]

end DominantFiveBody
