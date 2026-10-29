import DominantFiveBody.CoorbitalProperness
import DominantFiveBody.CoorbitalDowncrossing
import Mathlib.Analysis.Calculus.ImplicitContDiff

/-! # The minimal equal-mass open-semicircle seed

The source's Albouy--Fu counting input is proved for this chamber directly;
the classification of configurations occupying the rest of the circle is
not imported as an axiom. AF uses the opposite sign for its scalar kernel.
-/

noncomputable section
open scoped BigOperators ContDiff
open Filter Set Topology

namespace DominantFiveBody
open Coorbital
set_option maxHeartbeats 800000

def equalMassRatio : Satellite → ℝ := fun _ => 1 / 4

theorem equalMassRatio_positive : PositiveRatio equalMassRatio := by
  constructor
  · intro i; norm_num [equalMassRatio]
  · norm_num [equalMassRatio, Fin.sum_univ_four]

theorem kappa_ge_neg_one {t : ℝ} (ht : 0 < t) (htpi : t < Real.pi) :
    -1 ≤ kappa t := by
  have hs := sin_half_pos ht htpi
  have hnum : 0 ≤ 2 - Real.sin (t / 2) ^ 2 := by nlinarith [Real.sin_sq_le_one (t / 2)]
  have hquot : 0 ≤ (2 - Real.sin (t / 2) ^ 2) / (8 * Real.sin (t / 2) ^ 3) :=
    div_nonneg hnum (by positivity)
  unfold kappa
  linarith [Real.neg_one_le_cos t]

def equalMassPairSum (b a : ℝ) : ℝ := kernelF a + kernelF (a + b)

theorem equalMassPairSum_hasDerivAt {b a : ℝ} (hb : 0 < b) (hbh : b ≤ h)
    (ha : 0 < a) (hah : a < h) :
    HasDerivAt (equalMassPairSum b) (-kappa a - kappa (a + b)) a := by
  have hhpi : 2 * h < Real.pi := by unfold h; linarith [Real.pi_pos]
  have ha' := kernelF_hasDerivAt ha (by linarith)
  have hab' := (kernelF_hasDerivAt (by linarith : 0 < a + b)
    (by linarith : a + b < Real.pi)).comp a ((hasDerivAt_id a).add_const b)
  convert ha'.add hab' using 1 <;> try rfl
  simp only [mul_one, sub_eq_add_neg]

theorem equalMassPairSum_strictAntiOn {b : ℝ} (hb : 0 < b) (hbh : b ≤ h) :
    StrictAntiOn (equalMassPairSum b) (Set.Ioo 0 h) := by
  apply strictAntiOn_of_deriv_neg (convex_Ioo 0 h)
  · intro a ha
    exact (equalMassPairSum_hasDerivAt hb hbh ha.1 ha.2).continuousAt.continuousWithinAt
  · intro a ha
    rw [interior_Ioo] at ha
    rw [(equalMassPairSum_hasDerivAt hb hbh ha.1 ha.2).deriv]
    obtain ⟨ha, hah⟩ := ha
    have hshort := kappa_ge_nine_quarters ha hah.le
    have hglobal := kappa_ge_neg_one (by linarith : 0 < a + b)
      (by unfold h at *; linarith [Real.pi_pos] : a + b < Real.pi)
    linarith

theorem equalMass_root_reversal_symmetry (theta : Satellite → ℝ)
    (htheta : CoorbitalAngleDomain theta)
    (hroot : ∀ i, coorbitalResidual equalMassRatio theta i = 0) :
    theta 1 - theta 0 = theta 3 - theta 2 := by
  have harc := orderedSemicircle_of_coorbitalAngleDomain theta htheta
  have hr : ∀ i, angularEquation equalMassRatio theta i = 0 := by
    intro i; rw [angularEquation_eq_residual]; exact hroot i
  have hgaps := four_root_gaps equalMassRatio theta equalMassRatio_positive.1 harc hr
  have h0 := hr 0
  have h3 := hr 3
  unfold angularEquation at h0 h3
  rw [Fin.sum_univ_four] at h0 h3
  have hz : coorbitalKernel 0 = 0 := by simp [coorbitalKernel, kernelF]
  simp only [equalMassRatio, sub_self, hz, mul_zero, zero_add, add_zero] at h0 h3
  rw [coorbitalKernel_eq_positive_formula _ (harc 0 1 (by decide)).1.le,
    coorbitalKernel_eq_positive_formula _ (harc 0 2 (by decide)).1.le,
    coorbitalKernel_eq_positive_formula _ (harc 0 3 (by decide)).1.le] at h0
  have h30 : theta 0 - theta 3 = -(theta 3 - theta 0) := by ring
  have h31 : theta 1 - theta 3 = -(theta 3 - theta 1) := by ring
  have h32 : theta 2 - theta 3 = -(theta 3 - theta 2) := by ring
  rw [h30, h31, h32, coorbitalKernel_neg, coorbitalKernel_neg, coorbitalKernel_neg,
    coorbitalKernel_eq_positive_formula _ (harc 0 3 (by decide)).1.le,
    coorbitalKernel_eq_positive_formula _ (harc 1 3 (by decide)).1.le,
    coorbitalKernel_eq_positive_formula _ (harc 2 3 (by decide)).1.le] at h3
  have heq : equalMassPairSum (theta 2 - theta 1) (theta 1 - theta 0) =
      equalMassPairSum (theta 2 - theta 1) (theta 3 - theta 2) := by
    unfold equalMassPairSum
    rw [show theta 1 - theta 0 + (theta 2 - theta 1) = theta 2 - theta 0 by ring,
      show theta 3 - theta 2 + (theta 2 - theta 1) = theta 3 - theta 1 by ring]
    linarith
  exact (equalMassPairSum_strictAntiOn (harc 1 2 (by decide)).1 hgaps.2.1.le).injOn
    ⟨(harc 0 1 (by decide)).1, hgaps.1⟩
    ⟨(harc 2 3 (by decide)).1, hgaps.2.2.1⟩ heq

def equalMassMiddleEquation (a b : ℝ) : ℝ :=
  -kernelF a + kernelF b + kernelF (a + b)

theorem kernelF_tendsto_atTop_right : Tendsto kernelF (𝓝[>] (0 : ℝ)) atTop := by
  have h := tendsto_inv_nhdsGT_zero.atTop_mul_atTop₀ kernelF_angle_mul_tendsto_atTop
  apply h.congr'
  filter_upwards [self_mem_nhdsWithin] with t ht
  have hne : t ≠ 0 := ne_of_gt (show 0 < t from ht)
  field_simp [hne]

theorem equalMassMiddleEquation_strictAntiOn {a : ℝ} (ha : 0 < a) (hah : a ≤ h) :
    StrictAntiOn (equalMassMiddleEquation a) (Set.Ioo 0 h) := by
  have hanti := equalMassPairSum_strictAntiOn ha hah
  intro b hb c hc hbc
  have hg := hanti hb hc hbc
  unfold equalMassMiddleEquation equalMassPairSum at *
  rw [add_comm a c, add_comm a b]
  linarith

theorem equalMassMiddleEquation_continuousOn {a l : ℝ}
    (ha : 0 < a) (hah : a ≤ h) (hl : 0 < l) :
    ContinuousOn (equalMassMiddleEquation a) (Set.Icc l h) := by
  intro b hb
  have hhpi : 2 * h < Real.pi := by unfold h; linarith [Real.pi_pos]
  have hbpos : 0 < b := lt_of_lt_of_le hl hb.1
  have habpos : 0 < a + b := add_pos ha hbpos
  have hblt : b < Real.pi := by linarith [hb.2]
  have hablt : a + b < Real.pi := by linarith [hb.2]
  have hc0 : ContinuousAt (fun _ : ℝ => -kernelF a) b := continuousAt_const
  have hcont := hc0.add
    ((kernelF_hasDerivAt hbpos hblt).continuousAt) |>.add
      ((kernelF_hasDerivAt habpos hablt).continuousAt.comp
        (f := fun b : ℝ => a + b) (x := b) (by fun_prop))
  exact hcont.continuousWithinAt

/-- For each outer gap in (0,h], the genuine middle row has exactly one
inner gap in (0,h). This scalar existence uses the actual collision blowup. -/
theorem equalMassMiddleEquation_existsUnique {a : ℝ} (ha : 0 < a) (hah : a ≤ h) :
    ∃! b : ℝ, b ∈ Set.Ioo 0 h ∧ equalMassMiddleEquation a b = 0 := by
  have hh : 0 < h := by unfold h; positivity
  have haPi : a < Real.pi := by unfold h at hah; linarith [Real.pi_pos]
  have hanonneg : 0 ≤ kernelF a := by
    rcases lt_or_eq_of_le hah with hlt | heq
    · exact (kernelF_pos_on_short_arc ha hlt).le
    · rw [heq, kernelF_h]
  have hendpoint : equalMassMiddleEquation a h < 0 := by
    have hneg : kernelF (a + h) < 0 := kernelF_neg_on_long_arc (by linarith)
      (by unfold h at hah ⊢; linarith [Real.pi_pos])
    unfold equalMassMiddleEquation
    rw [kernelF_h]
    linarith
  have hevent := kernelF_tendsto_atTop_right.eventually_gt_atTop (kernelF a + 1)
  obtain ⟨r, hr, hsmall⟩ := mem_nhdsGT_iff_exists_Ioo_subset.mp hevent
  change 0 < r at hr
  let l := min r h / 2
  have hl : 0 < l := by dsimp [l]; positivity
  have hlr : l < r := by dsimp [l]; have := min_le_left r h; linarith
  have hlh : l < h := by dsimp [l]; have := min_le_right r h; linarith
  have hfl := hsmall ⟨hl, hlr⟩
  change kernelF a + 1 < kernelF l at hfl
  have hsum : l + a < Real.pi := by unfold h at hah hlh; linarith [Real.pi_pos]
  have hflower : -1 ≤ kernelF (a + l) := kernelF_ge_neg_one (add_pos ha hl) (by linarith)
  have hlpositive : 0 < equalMassMiddleEquation a l := by
    unfold equalMassMiddleEquation
    linarith
  obtain ⟨b, hb, hroot⟩ := intermediate_value_Icc' hlh.le
    (equalMassMiddleEquation_continuousOn ha hah hl) ⟨hendpoint.le, hlpositive.le⟩
  have hbpos : 0 < b := lt_of_lt_of_le hl hb.1
  have hbh : b < h := by
    rcases lt_or_eq_of_le hb.2 with hlt | heq
    · exact hlt
    · subst b; linarith
  refine ⟨b, ⟨⟨hbpos, hbh⟩, hroot⟩, ?_⟩
  intro c hc
  exact (equalMassMiddleEquation_strictAntiOn ha hah).injOn hc.1 ⟨hbpos, hbh⟩
    (hc.2.trans hroot.symm)

theorem kernelF_contDiffAt (n : ℕ∞ω) {t : ℝ} (ht : 0 < t) (htpi : t < Real.pi) :
    ContDiffAt ℝ n kernelF t := by
  have hden := kernel_denominator_ne_zero ht htpi
  unfold kernelF
  fun_prop (disch := assumption)

theorem equalMassMiddleEquation_joint_contDiffAt (n : ℕ∞ω) {a b : ℝ}
    (ha : 0 < a) (hah : a ≤ h) (hb : 0 < b) (hbh : b < h) :
    ContDiffAt ℝ n (fun z : ℝ × ℝ => equalMassMiddleEquation z.1 z.2) (a, b) := by
  have hhpi : 2 * h < Real.pi := by unfold h; linarith [Real.pi_pos]
  have haPi : a < Real.pi := by linarith
  have hbPi : b < Real.pi := by linarith
  have habPi : a + b < Real.pi := by linarith
  exact (((kernelF_contDiffAt n ha haPi).comp (a, b)
      (f := fun z : ℝ × ℝ => z.1) (by fun_prop)).neg.add
    ((kernelF_contDiffAt n hb hbPi).comp (a, b)
      (f := fun z : ℝ × ℝ => z.2) (by fun_prop))).add
    ((kernelF_contDiffAt n (add_pos ha hb) habPi).comp (a, b)
      (f := fun z : ℝ × ℝ => z.1 + z.2) (by fun_prop))

theorem equalMassMiddleEquation_hasDerivAt {a b : ℝ}
    (ha : 0 < a) (hah : a ≤ h) (hb : 0 < b) (hbh : b < h) :
    HasDerivAt (equalMassMiddleEquation a) (-kappa b - kappa (a + b)) b := by
  have hhpi : 2 * h < Real.pi := by unfold h; linarith [Real.pi_pos]
  have hd := (kernelF_hasDerivAt hb (by linarith)).const_add (-kernelF a) |>.add
    ((kernelF_hasDerivAt (add_pos ha hb) (by linarith)).comp b
      ((hasDerivAt_id b).const_add a))
  convert hd using 1 <;> try rfl
  simp only [mul_one, sub_eq_add_neg]

theorem equalMassMiddleEquation_derivative_neg {a b : ℝ}
    (ha : 0 < a) (hah : a ≤ h) (hb : 0 < b) (hbh : b < h) :
    -kappa b - kappa (a + b) < 0 := by
  have hshort := kappa_ge_nine_quarters hb hbh.le
  have hglobal := kappa_ge_neg_one (add_pos ha hb)
    (by unfold h at hah hbh; linarith [Real.pi_pos] : a + b < Real.pi)
  linarith

theorem scalar_span_isInvertible {c : ℝ} (hc : c ≠ 0) :
    (ContinuousLinearMap.toSpanSingleton ℝ c).IsInvertible := by
  let A : ℝ →L[ℝ] ℝ := ContinuousLinearMap.toSpanSingleton ℝ c
  have hi : Function.Injective A := by
    intro x y heq
    have hmul : c * x = c * y := by simpa only [A, ContinuousLinearMap.toSpanSingleton_apply,
      smul_eq_mul, mul_comm] using heq
    exact mul_left_cancel₀ hc hmul
  have hs : Function.Surjective A.toLinearMap :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank (f := A.toLinearMap) rfl).mp hi
  let e : ℝ ≃ₗ[ℝ] ℝ := LinearEquiv.ofBijective A.toLinearMap ⟨hi, hs⟩
  let e' : ℝ ≃L[ℝ] ℝ :=
    { e with
      continuous_toFun := A.continuous
      continuous_invFun := LinearMap.continuous_of_finiteDimensional
        (𝕜 := ℝ) (E := ℝ) (F' := ℝ) e.symm.toLinearMap }
  exact ⟨e', rfl⟩

theorem equalMassMiddleEquation_partial_isInvertible {a b : ℝ}
    (ha : 0 < a) (hah : a ≤ h) (hb : 0 < b) (hbh : b < h) :
    (fderiv ℝ (fun z : ℝ × ℝ => equalMassMiddleEquation z.1 z.2) (a, b) ∘L
      ContinuousLinearMap.inr ℝ ℝ ℝ).IsInvertible := by
  have hc := equalMassMiddleEquation_joint_contDiffAt 1 ha hah hb hbh
  have hd := (hc.differentiableAt (by norm_num)).hasFDerivAt
  have hinr : HasFDerivAt (fun x : ℝ => (a, x)) (ContinuousLinearMap.inr ℝ ℝ ℝ) b := by
    convert! (ContinuousLinearMap.inr ℝ ℝ ℝ).hasFDerivAt.add_const (a, 0) using 1
    all_goals first | rfl | (funext x; simp)
  have hpartial := hd.comp b hinr
  have hscalar := (equalMassMiddleEquation_hasDerivAt ha hah hb hbh).hasFDerivAt
  rw [hpartial.unique hscalar]
  exact scalar_span_isInvertible (ne_of_lt (equalMassMiddleEquation_derivative_neg ha hah hb hbh))

theorem equalMassMiddleEquation_local_implicitFunction {a b : ℝ}
    (ha : 0 < a) (hah : a ≤ h) (hb : 0 < b) (hbh : b < h)
    (hroot : equalMassMiddleEquation a b = 0) :
    ∃ psi : ℝ → ℝ, psi a = b ∧ ContDiffAt ℝ ∞ psi a ∧
      (∀ᶠ x in 𝓝 a, equalMassMiddleEquation x (psi x) = 0) := by
  let hc := equalMassMiddleEquation_joint_contDiffAt ∞ ha hah hb hbh
  have hpartial := equalMassMiddleEquation_partial_isInvertible ha hah hb hbh
  let psi := hc.implicitFunction (by simp) hpartial
  refine ⟨psi, hc.implicitFunction_apply_self (by simp) hpartial,
    hc.contDiffAt_implicitFunction (by simp) hpartial, ?_⟩
  simpa only [hroot] using hc.eventually_apply_implicitFunction (by simp) hpartial

def equalMassInnerGap (a : ℝ) : ℝ :=
  if ha : a ∈ Set.Ioc 0 h then Classical.choose (equalMassMiddleEquation_existsUnique ha.1 ha.2)
    else 0

theorem equalMassInnerGap_spec {a : ℝ} (ha : a ∈ Set.Ioc 0 h) :
    equalMassInnerGap a ∈ Set.Ioo 0 h ∧ equalMassMiddleEquation a (equalMassInnerGap a) = 0 := by
  unfold equalMassInnerGap
  rw [dif_pos ha]
  exact (Classical.choose_spec (equalMassMiddleEquation_existsUnique ha.1 ha.2)).1

theorem equalMassInnerGap_eq_of_root {a b : ℝ} (ha : a ∈ Set.Ioc 0 h)
    (hb : b ∈ Set.Ioo 0 h) (hr : equalMassMiddleEquation a b = 0) : equalMassInnerGap a = b := by
  exact (equalMassMiddleEquation_strictAntiOn ha.1 ha.2).injOn
    (equalMassInnerGap_spec ha).1 hb ((equalMassInnerGap_spec ha).2.trans hr.symm)

theorem equalMassInnerGap_contDiffWithinAt {a : ℝ} (ha : a ∈ Set.Ioc 0 h) :
    ContDiffWithinAt ℝ ∞ equalMassInnerGap (Set.Ioc 0 h) a := by
  obtain ⟨hb, hr⟩ := equalMassInnerGap_spec ha
  obtain ⟨psi, hbase, hsmooth, hroots⟩ := equalMassMiddleEquation_local_implicitFunction
    ha.1 ha.2 hb.1 hb.2 hr
  have hin : ∀ᶠ x in 𝓝 a, psi x ∈ Set.Ioo 0 h := by
    have hm : psi a ∈ Set.Ioo 0 h := by rwa [hbase]
    exact hsmooth.continuousAt.tendsto.eventually (isOpen_Ioo.mem_nhds hm)
  have heq : equalMassInnerGap =ᶠ[𝓝[Set.Ioc 0 h] a] psi := by
    filter_upwards [hin.filter_mono nhdsWithin_le_nhds,
      hroots.filter_mono nhdsWithin_le_nhds, self_mem_nhdsWithin] with x hx hroot hxmem
    exact equalMassInnerGap_eq_of_root hxmem hx hroot
  exact hsmooth.contDiffWithinAt.congr_of_eventuallyEq_of_mem heq ha

theorem equalMassInnerGap_continuousOn : ContinuousOn equalMassInnerGap (Set.Ioc 0 h) := by
  intro a ha
  exact (equalMassInnerGap_contDiffWithinAt ha).continuousWithinAt

theorem equalMassInnerGap_contDiffAt {a : ℝ} (ha : a ∈ Set.Ioo 0 h) :
    ContDiffAt ℝ ∞ equalMassInnerGap a :=
  (equalMassInnerGap_contDiffWithinAt ⟨ha.1, ha.2.le⟩).contDiffAt (Ioc_mem_nhds ha.1 ha.2)

def equalMassSymmetricAngles (a b : ℝ) : Satellite → ℝ := ![0, a, a + b, 2 * a + b]

theorem equalMassSymmetricAngles_domain {a b : ℝ} (ha : 0 < a) (hah : a ≤ h)
    (hb : 0 < b) (hbh : b < h) : CoorbitalAngleDomain (equalMassSymmetricAngles a b) := by
  constructor
  · rfl
  · constructor
    · intro i j hij
      fin_cases i <;> fin_cases j
      all_goals try { norm_num at hij }
      all_goals dsimp [equalMassSymmetricAngles]
      all_goals linarith
    · change 2 * a + b < Real.pi
      unfold h at hah hbh
      linarith

def equalMassOuterEquation (a : ℝ) : ℝ :=
  kernelF a + kernelF (a + equalMassInnerGap a) + kernelF (2 * a + equalMassInnerGap a)

theorem equalMassSymmetricAngles_rows {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    (angularEquation equalMassRatio (equalMassSymmetricAngles a b) 0 =
      (kernelF a + kernelF (a + b) + kernelF (2 * a + b)) / 4) ∧
    (angularEquation equalMassRatio (equalMassSymmetricAngles a b) 1 =
      equalMassMiddleEquation a b / 4) ∧
    (angularEquation equalMassRatio (equalMassSymmetricAngles a b) 2 =
      -equalMassMiddleEquation a b / 4) ∧
    (angularEquation equalMassRatio (equalMassSymmetricAngles a b) 3 =
      -(kernelF a + kernelF (a + b) + kernelF (2 * a + b)) / 4) := by
  have ha0 : coorbitalKernel a = kernelF a := coorbitalKernel_eq_positive_formula _ ha.le
  have hb0 : coorbitalKernel b = kernelF b := coorbitalKernel_eq_positive_formula _ hb.le
  have hab0 : coorbitalKernel (a + b) = kernelF (a + b) :=
    coorbitalKernel_eq_positive_formula _ (add_pos ha hb).le
  have hl0 : coorbitalKernel (2 * a + b) = kernelF (2 * a + b) :=
    coorbitalKernel_eq_positive_formula _ (by positivity)
  have hnab : -(a + b) + a = -b := by ring
  have hab : a + b - a = b := by ring
  have hla : 2 * a + b - a = a + b := by ring
  have hlab : 2 * a + b - (a + b) = a := by ring
  have hnal : a - (2 * a + b) = -(a + b) := by ring
  have hnabl : a + b - (2 * a + b) = -a := by ring
  have hnba : a - (a + b) = -b := by ring
  have hz : coorbitalKernel 0 = 0 := by simp [coorbitalKernel, kernelF]
  simp only [angularEquation, Fin.sum_univ_four, equalMassRatio]
  dsimp [equalMassSymmetricAngles]
  simp only [sub_zero, zero_sub, sub_self, hz, mul_zero, zero_add, add_zero,
    hab, hla, hlab, hnal, hnabl, hnba, coorbitalKernel_neg, ha0, hb0, hab0, hl0,
    equalMassMiddleEquation]
  constructor
  · ring
  · constructor
    · ring
    · constructor <;> ring

theorem equalMassOuterEquation_continuousOn :
    ContinuousOn equalMassOuterEquation (Set.Ioc 0 h) := by
  intro a ha
  have hb := (equalMassInnerGap_spec ha).1
  have ha0 := ha.1
  have hah := ha.2
  have hhpi : 2 * h < Real.pi := by unfold h; linarith [Real.pi_pos]
  have haPi : a < Real.pi := by linarith
  have habPi : a + equalMassInnerGap a < Real.pi := by linarith [ha.2, hb.2]
  have hlPi : 2 * a + equalMassInnerGap a < Real.pi := by
    unfold h at ha hb
    linarith [ha.2, hb.2]
  have hinner := equalMassInnerGap_continuousOn a ha
  have hsum := (kernelF_hasDerivAt (by linarith [ha.1, hb.1] : 0 < a + equalMassInnerGap a)
    habPi).continuousAt.comp_continuousWithinAt
      (f := fun x : ℝ => x + equalMassInnerGap x) (x := a) (s := Set.Ioc 0 h)
      (continuousWithinAt_id.add hinner)
  have hspan := (kernelF_hasDerivAt (by linarith [ha.1, hb.1] : 0 < 2 * a + equalMassInnerGap a)
    hlPi).continuousAt.comp_continuousWithinAt
      (f := fun x : ℝ => 2 * x + equalMassInnerGap x) (x := a) (s := Set.Ioc 0 h)
      (continuousWithinAt_id.const_mul 2 |>.add hinner)
  exact ((kernelF_hasDerivAt ha.1 haPi).continuousAt.continuousWithinAt.add hsum).add hspan

theorem equalMassOuterEquation_endpoint_neg : equalMassOuterEquation h < 0 := by
  have hh : 0 < h := by unfold h; positivity
  have hb := (equalMassInnerGap_spec ⟨hh, le_rfl⟩).1
  have hf1 := kernelF_neg_on_long_arc (by linarith [hb.1] : h < h + equalMassInnerGap h)
    (by unfold h at hb ⊢; linarith [hb.2, Real.pi_pos] : h + equalMassInnerGap h < Real.pi)
  have hf2 := kernelF_neg_on_long_arc (by linarith [hb.1] : h < 2 * h + equalMassInnerGap h)
    (by unfold h at hb ⊢; linarith [hb.2] : 2 * h + equalMassInnerGap h < Real.pi)
  unfold equalMassOuterEquation
  rw [kernelF_h]
  linarith

theorem equalMassOuterEquation_exists_zero :
    ∃ a ∈ Set.Ioo 0 h, equalMassOuterEquation a = 0 := by
  have hh : 0 < h := by unfold h; positivity
  have hevent := kernelF_tendsto_atTop_right.eventually_gt_atTop (2 : ℝ)
  obtain ⟨r, hr, hsmall⟩ := mem_nhdsGT_iff_exists_Ioo_subset.mp hevent
  change 0 < r at hr
  let l := min r h / 2
  have hl : 0 < l := by dsimp [l]; positivity
  have hlr : l < r := by dsimp [l]; have := min_le_left r h; linarith
  have hlh : l < h := by dsimp [l]; have := min_le_right r h; linarith
  have hfl := hsmall ⟨hl, hlr⟩
  change 2 < kernelF l at hfl
  have hb := (equalMassInnerGap_spec ⟨hl, hlh.le⟩).1
  have hd := equalMassSymmetricAngles_domain hl hlh.le hb.1 hb.2
  have hf1 := kernelF_ge_neg_one (by linarith [hb.1] : 0 < l + equalMassInnerGap l)
    (by unfold h at hlh hb; linarith [hb.2, Real.pi_pos] : l + equalMassInnerGap l < Real.pi)
  have hf2 := kernelF_ge_neg_one (by linarith [hb.1] : 0 < 2 * l + equalMassInnerGap l) hd.2.2
  have hlpositive : 0 < equalMassOuterEquation l := by unfold equalMassOuterEquation; linarith
  have hcont : ContinuousOn equalMassOuterEquation (Set.Icc l h) :=
    equalMassOuterEquation_continuousOn.mono (fun x hx => ⟨lt_of_lt_of_le hl hx.1, hx.2⟩)
  obtain ⟨a, ha, hz⟩ := intermediate_value_Icc' hlh.le hcont
    ⟨equalMassOuterEquation_endpoint_neg.le, hlpositive.le⟩
  refine ⟨a, ⟨lt_of_lt_of_le hl ha.1, ?_⟩, hz⟩
  rcases lt_or_eq_of_le ha.2 with hlt | heq
  · exact hlt
  · subst a; exact False.elim ((ne_of_lt equalMassOuterEquation_endpoint_neg) hz)

theorem equalMassSymmetricAngles_root_of_outer_zero {a : ℝ} (ha : a ∈ Set.Ioo 0 h)
    (hr : equalMassOuterEquation a = 0) :
    ∀ i, coorbitalResidual equalMassRatio
      (equalMassSymmetricAngles a (equalMassInnerGap a)) i = 0 := by
  have hb := equalMassInnerGap_spec ⟨ha.1, ha.2.le⟩
  obtain ⟨h0, h1, h2, h3⟩ := equalMassSymmetricAngles_rows ha.1 hb.1.1
  change angularEquation equalMassRatio (equalMassSymmetricAngles a (equalMassInnerGap a)) 0 =
    equalMassOuterEquation a / 4 at h0
  change angularEquation equalMassRatio (equalMassSymmetricAngles a (equalMassInnerGap a)) 3 =
    -equalMassOuterEquation a / 4 at h3
  intro i
  rw [← angularEquation_eq_residual]
  fin_cases i
  all_goals dsimp only
  · change angularEquation equalMassRatio
      (equalMassSymmetricAngles a (equalMassInnerGap a)) 0 = 0
    rw [h0, hr]; ring
  · change angularEquation equalMassRatio
      (equalMassSymmetricAngles a (equalMassInnerGap a)) 1 = 0
    rw [h1, hb.2]; ring
  · change angularEquation equalMassRatio
      (equalMassSymmetricAngles a (equalMassInnerGap a)) 2 = 0
    rw [h2, hb.2]; ring
  · change angularEquation equalMassRatio
      (equalMassSymmetricAngles a (equalMassInnerGap a)) 3 = 0
    rw [h3, hr]; ring

theorem equalMass_coorbital_exists :
    ∃ theta : Satellite → ℝ, CoorbitalAngleDomain theta ∧
      ∀ i, coorbitalResidual equalMassRatio theta i = 0 := by
  obtain ⟨a, ha, hr⟩ := equalMassOuterEquation_exists_zero
  have hb := (equalMassInnerGap_spec ⟨ha.1, ha.2.le⟩).1
  exact ⟨equalMassSymmetricAngles a (equalMassInnerGap a),
    equalMassSymmetricAngles_domain ha.1 ha.2.le hb.1 hb.2,
    equalMassSymmetricAngles_root_of_outer_zero ha hr⟩

theorem equalMassInnerGap_derivative_relation {a : ℝ} (ha : a ∈ Set.Ioo 0 h) :
    kappa a - kappa (equalMassInnerGap a) * deriv equalMassInnerGap a -
      kappa (a + equalMassInnerGap a) * (1 + deriv equalMassInnerGap a) = 0 := by
  have hb := (equalMassInnerGap_spec ⟨ha.1, ha.2.le⟩).1
  have ha0 := ha.1
  have hah := ha.2
  have hb0 := hb.1
  have hbh := hb.2
  have hhpi : 2 * h < Real.pi := by unfold h; linarith [Real.pi_pos]
  have haPi : a < Real.pi := by linarith
  have hbPi : equalMassInnerGap a < Real.pi := by linarith
  have habPi : a + equalMassInnerGap a < Real.pi := by linarith
  have hdb := (equalMassInnerGap_contDiffAt ha).differentiableAt (by simp) |>.hasDerivAt
  have hd := ((kernelF_hasDerivAt ha0 haPi).neg.add
    ((kernelF_hasDerivAt hb0 hbPi).comp a hdb)).add
    ((kernelF_hasDerivAt (add_pos ha0 hb0) habPi).comp a ((hasDerivAt_id a).add hdb))
  have heq : (fun x : ℝ => -kernelF x + kernelF (equalMassInnerGap x) +
      kernelF (x + equalMassInnerGap x)) =ᶠ[𝓝 a] (fun _ => 0) := by
    filter_upwards [isOpen_Ioo.mem_nhds ha] with x hx
    exact (equalMassInnerGap_spec ⟨hx.1, hx.2.le⟩).2
  have hd0 := (hasDerivAt_const a (0 : ℝ)).congr_of_eventuallyEq heq
  have hvalue := hd.unique hd0
  nlinarith

theorem equalMassInnerGap_derivative_pos {a : ℝ} (ha : a ∈ Set.Ioo 0 h) :
    0 < deriv equalMassInnerGap a := by
  have hb := (equalMassInnerGap_spec ⟨ha.1, ha.2.le⟩).1
  have hhpi : 2 * h < Real.pi := by unfold h; linarith [Real.pi_pos]
  have haPi : a < Real.pi := lt_trans ha.2 (by unfold h; linarith [Real.pi_pos])
  have habPi : a + equalMassInnerGap a < Real.pi := by linarith [ha.2, hb.2]
  have hk := strictAntiOn_kappa ⟨ha.1, haPi⟩ ⟨add_pos ha.1 hb.1, habPi⟩
    (by linarith [hb.1] : a < a + equalMassInnerGap a)
  have hsum := equalMassMiddleEquation_derivative_neg ha.1 ha.2.le hb.1 hb.2
  have hrel := equalMassInnerGap_derivative_relation ha
  by_contra hd
  have hmul : (kappa (equalMassInnerGap a) + kappa (a + equalMassInnerGap a)) *
      deriv equalMassInnerGap a ≤ 0 := mul_nonpos_of_nonneg_of_nonpos (by linarith) (le_of_not_gt hd)
  nlinarith

def equalMassOuterDerivative (a : ℝ) : ℝ :=
  -kappa a - kappa (a + equalMassInnerGap a) * (1 + deriv equalMassInnerGap a) -
    kappa (2 * a + equalMassInnerGap a) * (2 + deriv equalMassInnerGap a)

theorem equalMassOuterEquation_hasDerivAt {a : ℝ} (ha : a ∈ Set.Ioo 0 h) :
    HasDerivAt equalMassOuterEquation (equalMassOuterDerivative a) a := by
  have hb := (equalMassInnerGap_spec ⟨ha.1, ha.2.le⟩).1
  have ha0 := ha.1
  have hah := ha.2
  have hb0 := hb.1
  have hbh := hb.2
  have hhpi : 2 * h < Real.pi := by unfold h; linarith [Real.pi_pos]
  have haPi : a < Real.pi := by linarith
  have habPi : a + equalMassInnerGap a < Real.pi := by linarith
  have hlPi : 2 * a + equalMassInnerGap a < Real.pi := by unfold h at *; linarith
  have hdb := (equalMassInnerGap_contDiffAt ha).differentiableAt (by simp) |>.hasDerivAt
  have hd := ((kernelF_hasDerivAt ha0 haPi).add
    ((kernelF_hasDerivAt (add_pos ha0 hb0) habPi).comp a ((hasDerivAt_id a).add hdb))).add
    ((kernelF_hasDerivAt (by positivity : 0 < 2 * a + equalMassInnerGap a) hlPi).comp a
      (((hasDerivAt_id a).const_mul 2).add hdb))
  convert hd using 1 <;> try rfl
  unfold equalMassOuterDerivative
  ring

def equalMassSymmetricTangent (d : ℝ) : Satellite → ℝ := ![0, 1, 1 + d, 2 + d]

theorem equalMassSymmetric_form (a b d : ℝ) :
    coorbitalKappaForm equalMassRatio (equalMassSymmetricAngles a b)
      (equalMassSymmetricTangent d) =
    (2 * kappa a + 2 * kappa (a + b) * (1 + d) ^ 2 +
      kappa (2 * a + b) * (2 + d) ^ 2 + kappa b * d ^ 2) / 16 := by
  simp only [coorbitalKappaForm, weightedAngleForm, pairForm, Fin.sum_univ_four,
    Fin.reduceLT, if_true, if_false, zero_add, add_zero, equalMassRatio]
  dsimp [equalMassSymmetricAngles, equalMassSymmetricTangent]
  rw [show a + b - a = b by ring,
    show 2 * a + b - a = a + b by ring,
    show 2 * a + b - (a + b) = a by ring]
  simp only [sub_zero]
  ring

/-- The downcrossing sign is deduced from the proved physical Hessian at
an actual four-satellite root, through its explicit two-gap tangent. -/
theorem equalMassOuterDerivative_neg_at_root {a : ℝ} (ha : a ∈ Set.Ioo 0 h)
    (hr : equalMassOuterEquation a = 0) : equalMassOuterDerivative a < 0 := by
  have hb := (equalMassInnerGap_spec ⟨ha.1, ha.2.le⟩).1
  have hd := equalMassInnerGap_derivative_pos ha
  have hdomain := equalMassSymmetricAngles_domain ha.1 ha.2.le hb.1 hb.2
  have hroot := equalMassSymmetricAngles_root_of_outer_zero ha hr
  have hpos := coorbitalKappaForm_pos_at_root (n := 4) (by decide) (by decide)
    equalMassRatio (equalMassSymmetricAngles a (equalMassInnerGap a))
    (equalMassSymmetricTangent (deriv equalMassInnerGap a)) equalMassRatio_positive.1
    (orderedSemicircle_of_coorbitalAngleDomain _ hdomain)
    (fun i => (angularEquation_eq_residual _ _ i).trans (hroot i))
    (by
      intro hconst
      have h := hconst 0 1
      norm_num [equalMassSymmetricTangent] at h)
  have hrel := equalMassInnerGap_derivative_relation ha
  have hformula : coorbitalKappaForm equalMassRatio
      (equalMassSymmetricAngles a (equalMassInnerGap a))
      (equalMassSymmetricTangent (deriv equalMassInnerGap a)) =
      -(2 + deriv equalMassInnerGap a) / 16 * equalMassOuterDerivative a := by
    rw [equalMassSymmetric_form]
    unfold equalMassOuterDerivative
    linear_combination -(deriv equalMassInnerGap a / 16) * hrel
  rw [hformula] at hpos
  by_contra hbad
  have hnonpos : -(2 + deriv equalMassInnerGap a) / 16 * equalMassOuterDerivative a ≤ 0 :=
    mul_nonpos_of_nonpos_of_nonneg (by linarith) (le_of_not_gt hbad)
  linarith

theorem equalMassOuterEquation_zero_unique {a b : ℝ}
    (ha : a ∈ Set.Ioo 0 h) (hb : b ∈ Set.Ioo 0 h)
    (hfa : equalMassOuterEquation a = 0) (hfb : equalMassOuterEquation b = 0) : a = b := by
  exact downcrossing_zero_unique
    (equalMassOuterEquation_continuousOn.mono (fun _ hx => ⟨hx.1, hx.2.le⟩))
    (fun x hx hz => ⟨equalMassOuterDerivative x, equalMassOuterDerivative_neg_at_root hx hz,
      equalMassOuterEquation_hasDerivAt hx⟩) ha hb hfa hfb

/-- Every anchored equal-mass root has the actual symmetric two-gap form,
and its inner gap is the uniquely solved genuine middle angular equation. -/
theorem equalMass_root_normal_form (theta : Satellite → ℝ)
    (htheta : CoorbitalAngleDomain theta)
    (hroot : ∀ i, coorbitalResidual equalMassRatio theta i = 0) :
    ∃ a ∈ Set.Ioo 0 h,
      theta = equalMassSymmetricAngles a (equalMassInnerGap a) ∧
        equalMassOuterEquation a = 0 := by
  have harc := orderedSemicircle_of_coorbitalAngleDomain theta htheta
  have hr : ∀ i, angularEquation equalMassRatio theta i = 0 := by
    intro i; rw [angularEquation_eq_residual]; exact hroot i
  have hgaps := four_root_gaps equalMassRatio theta equalMassRatio_positive.1 harc hr
  have hsym := equalMass_root_reversal_symmetry theta htheta hroot
  let a := theta 1 - theta 0
  let b := theta 2 - theta 1
  have ha : a ∈ Set.Ioo 0 h := ⟨(harc 0 1 (by decide)).1, hgaps.1⟩
  have hb : b ∈ Set.Ioo 0 h := ⟨(harc 1 2 (by decide)).1, hgaps.2.1⟩
  have heq : theta = equalMassSymmetricAngles a b := by
    funext i
    fin_cases i
    all_goals dsimp [equalMassSymmetricAngles, a, b]
    · exact htheta.1
    · linarith [htheta.1]
    · linarith [htheta.1]
    · linarith [htheta.1]
  obtain ⟨h0, h1, _, _⟩ := equalMassSymmetricAngles_rows ha.1 hb.1
  have hmiddle : equalMassMiddleEquation a b = 0 := by
    rw [← heq, hr 1] at h1
    linarith
  have hinner : b = equalMassInnerGap a :=
    (equalMassInnerGap_eq_of_root ⟨ha.1, ha.2.le⟩ hb hmiddle).symm
  refine ⟨a, ha, ?_, ?_⟩
  · rw [← hinner]; exact heq
  · rw [← heq, hr 0] at h0
    unfold equalMassOuterEquation
    rw [← hinner]
    linarith

/-- The minimal equal-mass seed required by the covering argument is fully
proved in the open-semicircle chamber, without assuming the AF classification. -/
theorem equalMass_coorbital_existsUnique :
    ∃! theta : Satellite → ℝ, CoorbitalAngleDomain theta ∧
      ∀ i, coorbitalResidual equalMassRatio theta i = 0 := by
  obtain ⟨theta, htheta, hroot⟩ := equalMass_coorbital_exists
  refine ⟨theta, ⟨htheta, hroot⟩, ?_⟩
  intro phi hphi
  obtain ⟨a, ha, heqa, hza⟩ := equalMass_root_normal_form theta htheta hroot
  obtain ⟨b, hb, heqb, hzb⟩ := equalMass_root_normal_form phi hphi.1 hphi.2
  have hab := equalMassOuterEquation_zero_unique ha hb hza hzb
  rw [heqa, heqb, hab]

end DominantFiveBody
