import DominantFiveBody.CollisionTripleScales

/-! # The actual one-source field on a complete-triple rectangle

Source equation `eq:triple-J`. The epsilon-dependent barycentric term is
retained in the field and in its radial derivative.
-/

noncomputable section
open scoped BigOperators Matrix ContDiff
open Filter Set Topology

namespace DominantFiveBody
open Coorbital
set_option maxHeartbeats 800000

def physicalSourceFullAngularRadialDerivative (eps s angle rho v : ℝ) : ℝ :=
  s * Real.sin (angle - v) *
    ((‖polarPoint rho v - polarPoint s angle‖ ^ 3)⁻¹ - (1 + eps)⁻¹) +
  rho * physicalSourceAngularRadialDerivative s angle rho v

theorem physicalSourceFullAngularField_decomposition (eps s angle rho v : ℝ) :
    physicalSourceFullAngularField eps s angle rho v =
      rho * physicalSourceAngularField s angle rho v +
        rho * (s * Real.sin (angle - v) * ((s ^ 3)⁻¹ - (1 + eps)⁻¹)) := by
  unfold physicalSourceFullAngularField physicalSourceAngularField
  ring

theorem physicalSourceFullAngularField_hasDerivAt_radius (eps s angle rho v : ℝ)
    (hs : 0 < s) (hsep : polarPoint s angle ≠ polarPoint rho v) :
    HasDerivAt (fun r => physicalSourceFullAngularField eps s angle r v)
      (physicalSourceFullAngularRadialDerivative eps s angle rho v) rho := by
  have hd := ((hasDerivAt_id rho).mul
    (physicalSourceAngularField_hasDerivAt_radius s angle rho v hs hsep)).add
      ((hasDerivAt_id rho).mul_const
        (s * Real.sin (angle - v) * ((s ^ 3)⁻¹ - (1 + eps)⁻¹)))
  convert! hd using 1
  · funext r
    exact physicalSourceFullAngularField_decomposition eps s angle r v
  · unfold physicalSourceFullAngularRadialDerivative physicalSourceAngularField
    simp only [id_eq]
    ring

theorem physicalSourceFullAngularRadialDerivative_joint_contDiffAt
    (d : ℝ × ((ℝ × ℝ) × (ℝ × ℝ))) (heps : 1 + d.1 ≠ 0)
    (hsep : polarPoint d.2.1.1 d.2.1.2 ≠ polarPoint d.2.2.1 d.2.2.2) :
    ContDiffAt ℝ ∞ (fun z : ℝ × ((ℝ × ℝ) × (ℝ × ℝ)) =>
      physicalSourceFullAngularRadialDerivative z.1 z.2.1.1 z.2.1.2 z.2.2.1 z.2.2.2) d := by
  have hsource : ContDiff ℝ ∞ (fun z : ℝ × ((ℝ × ℝ) × (ℝ × ℝ)) =>
      polarPoint z.2.1.1 z.2.1.2) := (polarPoint_contDiff ∞).comp (by fun_prop)
  have htarget : ContDiff ℝ ∞ (fun z : ℝ × ((ℝ × ℝ) × (ℝ × ℝ)) =>
      polarPoint z.2.2.1 z.2.2.2) := (polarPoint_contDiff ∞).comp (by fun_prop)
  have hn := (htarget.contDiffAt.sub hsource.contDiffAt).norm ℝ
    (sub_ne_zero.mpr (Ne.symm hsep))
  have hden : ‖polarPoint d.2.2.1 d.2.2.2 - polarPoint d.2.1.1 d.2.1.2‖ ^ 3 ≠ 0 :=
    pow_ne_zero 3 (norm_ne_zero_iff.mpr (sub_ne_zero.mpr (Ne.symm hsep)))
  have he : ContDiffAt ℝ ∞ (fun z : ℝ × ((ℝ × ℝ) × (ℝ × ℝ)) => (1 + z.1)⁻¹) d :=
    (by fun_prop : ContDiffAt ℝ ∞ (fun z : ℝ × ((ℝ × ℝ) × (ℝ × ℝ)) => 1 + z.1) d).inv heps
  have hrad := (physicalSourceAngularRadialDerivative_joint_contDiffAt d.2 hsep).comp d
    (contDiff_snd.contDiffAt : ContDiffAt ℝ ∞ (fun z : ℝ × ((ℝ × ℝ) × (ℝ × ℝ)) => z.2) d)
  unfold physicalSourceFullAngularRadialDerivative
  apply ContDiffAt.add
  · exact (by fun_prop : ContDiffAt ℝ ∞ (fun z : ℝ × ((ℝ × ℝ) × (ℝ × ℝ)) =>
      z.2.1.1 * Real.sin (z.2.1.2 - z.2.2.2)) d).mul (((hn.pow 3).inv hden).sub he)
  · exact (by fun_prop : ContDiffAt ℝ ∞ (fun z : ℝ × ((ℝ × ℝ) × (ℝ × ℝ)) => z.2.2.1) d).mul hrad

theorem physicalSourceFullAngularRadialDerivative_unit (angle psi : ℝ) :
    physicalSourceFullAngularRadialDerivative 0 1 angle 1 psi =
      physicalSourceAngularField 1 angle 1 psi + physicalSourceAngularRadialDerivative 1 angle 1 psi := by
  simp [physicalSourceFullAngularRadialDerivative, physicalSourceAngularField]

theorem physicalSourceFullAngularRadialDerivative_unit_left_neg (angle psi : ℝ)
    (hgap : angle - psi = h) :
    physicalSourceFullAngularRadialDerivative 0 1 angle 1 psi < 0 := by
  have hh : 0 < h := by unfold h; positivity
  have hp : h < Real.pi := by unfold h; linarith [Real.pi_pos]
  have hne : angle ≠ psi := sub_ne_zero.mp (hgap ▸ hh.ne')
  have habs : |angle - psi| < Real.pi := by rw [hgap, abs_of_pos hh]; exact hp
  rw [physicalSourceFullAngularRadialDerivative_unit,
    physicalSourceAngularField_unit_kernel angle psi hne habs, hgap]
  have hz : coorbitalKernel h = 0 := by
    rw [coorbitalKernel_eq_positive_formula h hh.le, kernelF_h]
  rw [hz, zero_add]
  exact physicalSourceAngularRadialDerivative_unit_neg angle psi (by rwa [hgap]) (by rwa [hgap])

theorem physicalSourceFullAngularField_unit_hasDerivAt_angle (angle psi : ℝ)
    (hne : angle ≠ psi) (hpi : |angle - psi| < Real.pi) :
    HasDerivAt (fun v => physicalSourceFullAngularField 0 1 angle 1 v)
      (kappa |psi - angle|) psi := by
  convert! physicalSourceAngularField_unit_hasDerivAt angle psi hne hpi using 1
  funext v
  simp [physicalSourceFullAngularField_decomposition]

/-- The strict negative radial derivative persists when epsilon, source
radius, source angle and target coordinates vary independently. -/
theorem physicalSourceFullAngularRadialDerivative_left_rectangle (angle psi : ℝ)
    (hgap : angle - psi = h) :
    ∃ eta k : ℝ, 0 < eta ∧ 0 < k ∧ ∀ (eps s theta rho v : ℝ),
      |eps| < eta → dist (s, theta) (1, angle) < eta → dist (rho, v) (1, psi) < eta →
      physicalSourceFullAngularRadialDerivative eps s theta rho v ≤ -k := by
  have hh : 0 < h := by unfold h; positivity
  have hp : h < Real.pi := by unfold h; linarith [Real.pi_pos]
  have hne : angle ≠ psi := sub_ne_zero.mp (hgap ▸ hh.ne')
  have hsep := polarUnit_ne_of_angle_ne angle psi hne (by rw [abs_sub_comm, hgap, abs_of_pos hh]; exact hp)
  let k := -physicalSourceFullAngularRadialDerivative 0 1 angle 1 psi / 2
  have hneg := physicalSourceFullAngularRadialDerivative_unit_left_neg angle psi hgap
  have hk : 0 < k := by dsimp [k]; linarith
  have hstrict : physicalSourceFullAngularRadialDerivative 0 1 angle 1 psi < -k := by dsimp [k]; linarith
  have he := (physicalSourceFullAngularRadialDerivative_joint_contDiffAt
    (0, ((1, angle), (1, psi))) (by norm_num) hsep).continuousAt.eventually (Iio_mem_nhds hstrict)
  obtain ⟨eta, heta, hball⟩ := Metric.eventually_nhds_iff.mp he
  refine ⟨eta, k, heta, hk, ?_⟩
  intro eps s theta rho v heps hsource htarget
  exact (hball (y := (eps, ((s, theta), (rho, v)))) (by
    rw [Prod.dist_eq, Prod.dist_eq, Real.dist_eq, sub_zero]
    exact max_lt heps (max_lt hsource htarget))).le

theorem physicalSourceFullAngularField_lipschitz_rectangle (angle psi : ℝ)
    (hsep : polarPoint 1 angle ≠ polarPoint 1 psi) :
    ∃ eta C : ℝ, 0 < eta ∧ 0 < C ∧ ∀ (eps s theta ra va rb vb : ℝ),
      |eps| < eta → dist (s, theta) (1, angle) < eta →
      dist (ra, va) (1, psi) < eta → dist (rb, vb) (1, psi) < eta →
      |physicalSourceFullAngularField eps s theta rb vb - physicalSourceFullAngularField eps s theta ra va| ≤
        C * max |rb - ra| |vb - va| := by
  obtain ⟨K, U, hU, hLip⟩ := ((physicalSourceFullAngularField_joint_contDiffAt
    (0, ((1, angle), (1, psi))) (by norm_num) hsep).of_le
      (by norm_num : (1 : ℕ∞ω) ≤ ∞)).exists_lipschitzOnWith
  obtain ⟨eta, heta, hball⟩ := Metric.mem_nhds_iff.mp hU
  refine ⟨eta, (K : ℝ) + 1, heta, by positivity, ?_⟩
  intro eps s theta ra va rb vb heps hsource ha hb
  have hUa : (eps, ((s, theta), (ra, va))) ∈ U := hball (by
    rw [Metric.mem_ball, Prod.dist_eq, Prod.dist_eq, Real.dist_eq, sub_zero]
    exact max_lt heps (max_lt hsource ha))
  have hUb : (eps, ((s, theta), (rb, vb))) ∈ U := hball (by
    rw [Metric.mem_ball, Prod.dist_eq, Prod.dist_eq, Real.dist_eq, sub_zero]
    exact max_lt heps (max_lt hsource hb))
  have hbound := hLip.dist_le_mul _ hUb _ hUa
  have hd : dist (eps, ((s, theta), (rb, vb))) (eps, ((s, theta), (ra, va))) =
      max |rb - ra| |vb - va| := by
    simp only [Prod.dist_eq, dist_self, Real.dist_eq]
    simp [abs_nonneg]
  rw [hd, Real.dist_eq] at hbound
  exact hbound.trans (mul_le_mul_of_nonneg_right (by linarith : (K : ℝ) ≤ (K : ℝ) + 1)
    (le_max_of_le_left (abs_nonneg _)))

/-- Scalar mean-value control on a whole radial interval. The angular
part varies after the radius part, with the source held at its actual
current parameters. -/
theorem physicalSourceFullAngularField_left_difference_control (angle psi : ℝ)
    (hgap : angle - psi = h) :
    ∃ eta k C : ℝ, 0 < eta ∧ 0 < k ∧ 0 < C ∧
      ∀ (eps s theta ra rb va vb : ℝ), |eps| < eta → dist (s, theta) (1, angle) < eta →
        ra ≤ rb → dist (ra, va) (1, psi) < eta → dist (rb, va) (1, psi) < eta →
        dist (rb, vb) (1, psi) < eta →
        physicalSourceFullAngularField eps s theta rb vb - physicalSourceFullAngularField eps s theta ra va ≤
          -k * (rb - ra) + C * |vb - va| := by
  have hh : 0 < h := by unfold h; positivity
  have hp : h < Real.pi := by unfold h; linarith [Real.pi_pos]
  have hne : angle ≠ psi := sub_ne_zero.mp (hgap ▸ hh.ne')
  have hsep := polarUnit_ne_of_angle_ne angle psi hne (by rw [abs_sub_comm, hgap, abs_of_pos hh]; exact hp)
  obtain ⟨e0, he0, hregular⟩ := physicalSourceAngularField_regular_rectangle angle psi hsep
  obtain ⟨e1, k, he1, hk, hradial⟩ := physicalSourceFullAngularRadialDerivative_left_rectangle angle psi hgap
  obtain ⟨e2, C, he2, hC, hangular⟩ := physicalSourceFullAngularField_lipschitz_rectangle angle psi hsep
  let eta := min e0 (min e1 e2)
  have h0 : eta ≤ e0 := min_le_left _ _
  have h1 : eta ≤ e1 := (min_le_right _ _).trans (min_le_left _ _)
  have h2 : eta ≤ e2 := (min_le_right _ _).trans (min_le_right _ _)
  refine ⟨eta, k, C, lt_min he0 (lt_min he1 he2), hk, hC, ?_⟩
  intro eps s theta ra rb va vb heps hs habr ha hb hc
  have hrect := polar_rectangle_radius_interval ra rb va psi eta ha hb
  have hF (rho : ℝ) (hrho : rho ∈ Icc ra rb) :=
    physicalSourceFullAngularField_hasDerivAt_radius eps s theta rho va
      (hregular s theta rho va (hs.trans_le h0) ((hrect rho hrho).trans_le h0)).1
      (hregular s theta rho va (hs.trans_le h0) ((hrect rho hrho).trans_le h0)).2
  have hcont : ContinuousOn (fun rho => physicalSourceFullAngularField eps s theta rho va) (Icc ra rb) :=
    fun rho hrho => (hF rho hrho).continuousAt.continuousWithinAt
  have hdiff : DifferentiableOn ℝ (fun rho => physicalSourceFullAngularField eps s theta rho va)
      (interior (Icc ra rb)) :=
    fun rho hrho => (hF rho (interior_subset hrho)).differentiableAt.differentiableWithinAt
  have hbound : ∀ rho ∈ interior (Icc ra rb), deriv (fun r => physicalSourceFullAngularField eps s theta r va) rho ≤ -k := by
    intro rho hrho
    rw [(hF rho (interior_subset hrho)).deriv]
    exact hradial eps s theta rho va (heps.trans_le h1) (hs.trans_le h1)
      ((hrect rho (interior_subset hrho)).trans_le h1)
  have hr := (convex_Icc ra rb).image_sub_le_mul_sub_of_deriv_le hcont hdiff hbound
    ra (left_mem_Icc.mpr habr) rb (right_mem_Icc.mpr habr) habr
  have hang := (le_abs_self (physicalSourceFullAngularField eps s theta rb vb - physicalSourceFullAngularField eps s theta rb va)).trans
    (hangular eps s theta rb va rb vb (heps.trans_le h2) (hs.trans_le h2) (hb.trans_le h2) (hc.trans_le h2))
  simp only [sub_self, abs_zero, max_eq_right (abs_nonneg (vb - va))] at hang
  linarith

end DominantFiveBody
