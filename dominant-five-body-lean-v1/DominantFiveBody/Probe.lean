import DominantFiveBody.CoorbitalModel

/-!
# The two-source probe, manuscript Lemma `lem:probe` (Theorem counter 2.3)

The theorem below uses the actual odd extension `coorbitalKernel`. Its
geometric hypothesis is exactly that `0,h,x` have span less than π; the
two distinctness conditions and zero source masses are retained.
-/

noncomputable section

namespace DominantFiveBody

open Coorbital

def twoSourceSpan (x : ℝ) : ℝ := max h x - min 0 x

theorem probe_separations_lt_pi {x : ℝ} (hspan : twoSourceSpan x < Real.pi) :
    |x| < Real.pi ∧ |x - h| < Real.pi := by
  have hh : 0 < h := by unfold h; positivity
  have hm0 := min_le_left (0 : ℝ) x
  have hmx := min_le_right (0 : ℝ) x
  have hxM := le_max_right h x
  have hhM := le_max_left h x
  unfold twoSourceSpan at hspan
  constructor
  · apply abs_lt.mpr
    constructor <;> linarith
  · apply abs_lt.mpr
    constructor <;> linarith

/-- The only signed kernel zeros at noncollision separations inside an open
semicircle have absolute separation `h`. -/
theorem coorbitalKernel_zero_iff_abs_eq_h {t : ℝ}
    (ht : t ≠ 0) (htpi : |t| < Real.pi) :
    coorbitalKernel t = 0 ↔ |t| = h := by
  rcases lt_or_gt_of_ne ht with hneg | hpos
  · have hnt : 0 < -t := neg_pos.mpr hneg
    have hntpi : -t < Real.pi := by simpa only [abs_of_neg hneg] using htpi
    rw [coorbitalKernel, if_neg (not_le.mpr hneg), abs_of_neg hneg, neg_eq_zero]
    exact kernelF_eq_zero_iff hnt hntpi
  · rw [coorbitalKernel_eq_positive_formula t (le_of_lt hpos), abs_of_pos hpos]
    exact kernelF_eq_zero_iff hpos (by simpa only [abs_of_pos hpos] using htpi)

def twoSourceFunction (p q : ℝ) (x : ℝ) : ℝ :=
  p * kernelF x + q * kernelF (x - h)

theorem twoSourceFunction_hasDerivAt {p q x : ℝ}
    (hhx : h < x) (hxpi : x < Real.pi) :
    HasDerivAt (twoSourceFunction p q)
      (-(p * kappa x + q * kappa (x - h))) x := by
  have hh : 0 < h := by unfold h; positivity
  have hx : 0 < x := lt_trans hh hhx
  have hxh : 0 < x - h := sub_pos.mpr hhx
  have hxhpi : x - h < Real.pi := by linarith
  have hshift := (kernelF_hasDerivAt hxh hxhpi).comp x ((hasDerivAt_id x).sub_const h)
  have hd := ((kernelF_hasDerivAt hx hxpi).const_mul p).add (hshift.const_mul q)
  convert hd using 1 <;> try rfl
  simp only [mul_one]
  ring

/-- The right exterior interval of the probe lemma. The source at `h` has
positive weight; the source at zero is allowed to have weight zero. -/
theorem twoSourceProbe_right {p q x : ℝ}
    (hp : 0 ≤ p) (hq : 0 < q) (hhx : h < x) (hxpi : x < Real.pi)
    (hroot : p * coorbitalKernel x + q * coorbitalKernel (x - h) = 0) :
    0 < p * kappa |x| + q * kappa |x - h| := by
  have hh : 0 < h := by unfold h; positivity
  have hhpi : h < Real.pi := by unfold h; linarith [Real.pi_pos]
  have hx : 0 < x := lt_trans hh hhx
  have hxh : 0 < x - h := sub_pos.mpr hhx
  have hgroot : twoSourceFunction p q x = 0 := by
    simpa only [twoSourceFunction,
      coorbitalKernel_eq_positive_formula x (le_of_lt hx),
      coorbitalKernel_eq_positive_formula (x - h) (le_of_lt hxh)] using hroot
  have hcont : ContinuousOn (twoSourceFunction p q) (Set.Icc x Real.pi) := by
    intro y hy
    have hypos : 0 < y := lt_of_lt_of_le hx hy.1
    have hyh : 0 < y - h := by linarith [hy.1]
    have hyhpi : y - h ≤ Real.pi := by linarith [hy.2]
    have hshift : ContinuousAt (fun z : ℝ => z - h) y := by fun_prop
    have hcomp : ContinuousAt (fun z : ℝ => kernelF (z - h)) y :=
      ContinuousAt.comp (f := fun z : ℝ => z - h) (x := y)
        (kernelF_continuousAt hyh hyhpi) hshift
    exact (((kernelF_continuousAt hypos hy.2).const_mul p).add
      (hcomp.const_mul q)).continuousWithinAt
  obtain ⟨c, hc, hsec⟩ := exists_hasDerivAt_eq_slope (twoSourceFunction p q)
    (fun y => -(p * kappa y + q * kappa (y - h))) hxpi hcont
    (fun y hy => twoSourceFunction_hasDerivAt (lt_trans hhx hy.1) hy.2)
  have hendpoint : twoSourceFunction p q Real.pi < 0 := by
    have hlong : h < Real.pi - h := by unfold h; linarith [Real.pi_pos]
    have hshort : Real.pi - h < Real.pi := by linarith
    unfold twoSourceFunction
    rw [kernelF_pi, mul_zero, zero_add]
    exact mul_neg_of_pos_of_neg hq (kernelF_neg_on_long_arc hlong hshort)
  rw [hgroot, sub_zero] at hsec
  have hsecneg : -(p * kappa c + q * kappa (c - h)) < 0 := by
    rw [hsec]
    exact div_neg_of_neg_of_pos hendpoint (sub_pos.mpr hxpi)
  have hkc : kappa c < kappa x :=
    strictAntiOn_kappa ⟨hx, hxpi⟩ ⟨lt_trans hx hc.1, hc.2⟩ hc.1
  have hkch : kappa (c - h) < kappa (x - h) := by
    apply strictAntiOn_kappa
      ⟨hxh, by linarith⟩ ⟨by linarith [hc.1], by linarith [hc.2]⟩
    linarith [hc.1]
  have hcompare : p * kappa c + q * kappa (c - h) <
      p * kappa x + q * kappa (x - h) :=
    add_lt_add_of_le_of_lt (mul_le_mul_of_nonneg_left (le_of_lt hkc) hp)
      (mul_lt_mul_of_pos_left hkch hq)
  rw [abs_of_pos hx, abs_of_pos hxh]
  linarith

/-- Manuscript Lemma `lem:probe`, including both zero-mass endpoints and the
reflection argument. No additional analytic or spectral hypothesis occurs. -/
theorem twoSourceProbe {p q x : ℝ}
    (hp : 0 ≤ p) (hq : 0 ≤ q) (hpq : p + q = 1)
    (hx0 : x ≠ 0) (hxh : x ≠ h) (hspan : twoSourceSpan x < Real.pi)
    (hroot : p * coorbitalKernel x + q * coorbitalKernel (x - h) = 0) :
    0 < p * kappa |x| + q * kappa |x - h| := by
  have hsep := probe_separations_lt_pi hspan
  by_cases hp0 : p = 0
  · have hq1 : q = 1 := by linarith
    have hzero : coorbitalKernel (x - h) = 0 := by simpa [hp0, hq1] using hroot
    have hdist := (coorbitalKernel_zero_iff_abs_eq_h (sub_ne_zero.mpr hxh) hsep.2).mp hzero
    rw [hp0, hq1, zero_mul, one_mul, zero_add, hdist, kappa_h]
    norm_num
  by_cases hq0 : q = 0
  · have hp1 : p = 1 := by linarith
    have hzero : coorbitalKernel x = 0 := by simpa [hq0, hp1] using hroot
    have hdist := (coorbitalKernel_zero_iff_abs_eq_h hx0 hsep.1).mp hzero
    rw [hq0, hp1, zero_mul, one_mul, add_zero, hdist, kappa_h]
    norm_num
  have hpp : 0 < p := lt_of_le_of_ne hp (Ne.symm hp0)
  have hqp : 0 < q := lt_of_le_of_ne hq (Ne.symm hq0)
  rcases lt_or_gt_of_ne hx0 with hxneg | hxpos
  · let y : ℝ := h - x
    have hhy : h < y := by dsimp [y]; linarith
    have hypi : y < Real.pi := by
      have hxmh : x - h < 0 := by
        have hh : 0 < h := by unfold h; positivity
        linarith
      simpa only [abs_of_neg hxmh, neg_sub] using hsep.2
    have hyroot : q * coorbitalKernel y + p * coorbitalKernel (y - h) = 0 := by
      have hy1 : y = -(x - h) := by dsimp [y]; ring
      have hy2 : y - h = -x := by dsimp [y]; ring
      rw [hy2, hy1, coorbitalKernel_neg, coorbitalKernel_neg]
      linarith
    have hresult := twoSourceProbe_right hq hpp hhy hypi hyroot
    have hy1 : |y| = |x - h| := by rw [show y = -(x - h) by dsimp [y]; ring, abs_neg]
    have hy2 : |y - h| = |x| := by rw [show y - h = -x by dsimp [y]; ring, abs_neg]
    rw [hy1, hy2] at hresult
    simpa only [add_comm] using hresult
  · rcases lt_or_gt_of_ne hxh with hxlt | hxgt
    · have hhx : 0 < h - x := sub_pos.mpr hxlt
      have hxhle : x ≤ h := le_of_lt hxlt
      have hhxle : h - x ≤ h := by linarith
      rw [abs_of_pos hxpos, abs_of_neg (sub_neg.mpr hxlt), neg_sub]
      exact add_pos (mul_pos hpp (kappa_pos_on_short_arc hxpos hxhle))
        (mul_pos hqp (kappa_pos_on_short_arc hhx hhxle))
    · exact twoSourceProbe_right hp hqp hxgt
        (by simpa only [abs_of_pos hxpos] using hsep.1) hroot

end DominantFiveBody
