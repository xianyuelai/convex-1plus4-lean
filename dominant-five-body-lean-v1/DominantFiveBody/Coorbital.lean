import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Tactic

/-!
# Concrete coorbital kernel, manuscript §2

This module uses precisely the scalar formulas in equations `eq:kernel` and
`eq:kappa`. The short arc positivity theorem is not the full angular cycle
lemma: κ becomes negative near π. No angular equilibrium theorem is assumed.
-/

namespace DominantFiveBody.Coorbital

noncomputable section

def h : ℝ := Real.pi / 3

/-- The positive-argument formula in manuscript equation `eq:kernel`.
The manuscript uses its odd extension for signed angle differences. -/
def kernelF (t : ℝ) : ℝ :=
  Real.sin t * ((2 * Real.sin (t / 2))⁻¹ ^ 3 - 1)

def pairPotential (t : ℝ) : ℝ :=
  (2 * Real.sin (t / 2))⁻¹ + 1 - Real.cos t

/-- The explicit formula in manuscript equation `eq:kappa`. -/
def kappa (t : ℝ) : ℝ :=
  (2 - Real.sin (t / 2) ^ 2) / (8 * Real.sin (t / 2) ^ 3) + Real.cos t

theorem sin_half_pos {t : ℝ} (ht : 0 < t) (htpi : t < Real.pi) :
    0 < Real.sin (t / 2) := by
  apply Real.sin_pos_of_pos_of_lt_pi
  · linarith
  · linarith [Real.pi_pos]

/-- In particular, every denominator used below is genuinely nonzero. -/
theorem kernel_denominator_ne_zero {t : ℝ} (ht : 0 < t) (htpi : t < Real.pi) :
    2 * Real.sin (t / 2) ≠ 0 := by
  exact ne_of_gt (mul_pos (by norm_num) (sin_half_pos ht htpi))

theorem cos_half_identity (t : ℝ) :
    Real.cos t = 1 - 2 * Real.sin (t / 2) ^ 2 := by
  have hc := Real.cos_two_mul (t / 2)
  have hs := Real.sin_sq_add_cos_sq (t / 2)
  have ht : 2 * (t / 2) = t := by ring
  rw [ht] at hc
  nlinarith

theorem kappa_h : kappa h = 9 / 4 := by
  have ht : h / 2 = Real.pi / 6 := by unfold h; ring
  unfold kappa
  rw [ht, Real.sin_pi_div_six, cos_half_identity h, ht, Real.sin_pi_div_six]
  norm_num

theorem sin_half_le_half {t : ℝ} (ht : 0 < t) (hth : t ≤ h) :
    Real.sin (t / 2) ≤ 1 / 2 := by
  have hsin := Real.sin_le_sin_of_le_of_le_pi_div_two
    (x := t / 2) (y := Real.pi / 6)
    (by linarith [Real.pi_pos]) (by linarith [Real.pi_pos])
    (by unfold h at hth; linarith)
  simpa only [Real.sin_pi_div_six] using hsin

/-- Quantitative short arc bound used by the proof of manuscript Lemma `lem:cycle`.
This theorem covers exactly `0 < t ≤ π/3`, not all of the open semicircle. -/
theorem kappa_ge_nine_quarters {t : ℝ} (ht : 0 < t) (hth : t ≤ h) :
    9 / 4 ≤ kappa t := by
  have htpi : t < Real.pi := by unfold h at hth; linarith [Real.pi_pos]
  have hs : 0 < Real.sin (t / 2) := sin_half_pos ht htpi
  have hsle := sin_half_le_half ht hth
  have hd : 0 < 8 * Real.sin (t / 2) ^ 3 := by positivity
  have hpoly : 0 ≤ (1 - 2 * Real.sin (t / 2)) *
      (8 * Real.sin (t / 2) ^ 4 + 4 * Real.sin (t / 2) ^ 3 +
        7 * Real.sin (t / 2) ^ 2 + 4 * Real.sin (t / 2) + 2) := by
    apply mul_nonneg
    · linarith
    · positivity
  unfold kappa
  rw [cos_half_identity]
  have hquot : 9 / 4 - (1 - 2 * Real.sin (t / 2) ^ 2) ≤
      (2 - Real.sin (t / 2) ^ 2) / (8 * Real.sin (t / 2) ^ 3) := by
    apply (le_div_iff₀ hd).2
    nlinarith
  linarith

theorem kappa_pos_on_short_arc {t : ℝ} (ht : 0 < t) (hth : t ≤ h) :
    0 < kappa t := by
  have hbound := kappa_ge_nine_quarters ht hth
  linarith

theorem sin_half_double (t : ℝ) :
    Real.sin t = 2 * Real.sin (t / 2) * Real.cos (t / 2) := by
  have ht : 2 * (t / 2) = t := by ring
  simpa only [ht] using Real.sin_two_mul (t / 2)

/-- First derivative identity for the concrete pair potential in `eq:kernel`. -/
theorem pairPotential_hasDerivAt {t : ℝ} (ht : 0 < t) (htpi : t < Real.pi) :
    HasDerivAt pairPotential (-kernelF t) t := by
  have hs := ((hasDerivAt_id t).div_const 2).sin
  have hden := kernel_denominator_ne_zero ht htpi
  have hv := ((((hs.const_mul 2).inv hden).add_const 1).sub (Real.hasDerivAt_cos t))
  convert hv using 1 <;> try rfl
  simp only [id_eq] 
  unfold kernelF
  rw [sin_half_double t]
  have hsne := ne_of_gt (sin_half_pos ht htpi)
  field_simp [hsne]
  ring

/-- Exact identity `κ = -f'` from `eq:kernel` and `eq:kappa`, with
the singular endpoints excluded explicitly. -/
theorem kernelF_hasDerivAt {t : ℝ} (ht : 0 < t) (htpi : t < Real.pi) :
    HasDerivAt kernelF (-kappa t) t := by
  have hs := ((hasDerivAt_id t).div_const 2).sin
  have hden := kernel_denominator_ne_zero ht htpi
  have hf := (Real.hasDerivAt_sin t).mul ((((hs.const_mul 2).inv hden).pow 3).sub_const 1)
  convert hf using 1 <;> try rfl
  simp only [id_eq, Pi.inv_apply, Pi.pow_apply, Nat.reduceSub, Nat.cast_ofNat]
  unfold kappa
  rw [sin_half_double t, cos_half_identity t]
  have htrig := Real.sin_sq_add_cos_sq (t / 2)
  have hsne := ne_of_gt (sin_half_pos ht htpi)
  field_simp [hsne]
  nlinarith [mul_pos (sin_half_pos ht htpi) (sin_half_pos ht htpi)]

theorem deriv_kernelF {t : ℝ} (ht : 0 < t) (htpi : t < Real.pi) :
    deriv kernelF t = -kappa t := (kernelF_hasDerivAt ht htpi).deriv

theorem deriv_pairPotential {t : ℝ} (ht : 0 < t) (htpi : t < Real.pi) :
    deriv pairPotential t = -kernelF t := (pairPotential_hasDerivAt ht htpi).deriv

/-- The concrete expression for `κ'` in manuscript equation `eq:kappa`. -/
def kappaPrime (t : ℝ) : ℝ :=
  -Real.cos (t / 2) / (16 * Real.sin (t / 2) ^ 4) *
    (6 - Real.sin (t / 2) ^ 2 + 32 * Real.sin (t / 2) ^ 5)

theorem kappa_hasDerivAt {t : ℝ} (ht : 0 < t) (htpi : t < Real.pi) :
    HasDerivAt kappa (kappaPrime t) t := by
  have hs := ((hasDerivAt_id t).div_const 2).sin
  have hspos := sin_half_pos ht htpi
  have hd : 8 * Real.sin (t / 2) ^ 3 ≠ 0 := by positivity
  have hk := (((hasDerivAt_const t (2 : ℝ)).sub (hs.pow 2)).div
    ((hs.pow 3).const_mul 8) hd).add (Real.hasDerivAt_cos t)
  convert hk using 1 <;> try rfl
  simp only [id_eq, Pi.pow_apply, Pi.sub_apply, Nat.reduceSub, Nat.cast_ofNat]
  unfold kappaPrime
  rw [sin_half_double t]
  field_simp [ne_of_gt hspos]
  ring

theorem kappaPrime_neg {t : ℝ} (ht : 0 < t) (htpi : t < Real.pi) :
    kappaPrime t < 0 := by
  have hs := sin_half_pos ht htpi
  have hc : 0 < Real.cos (t / 2) := by
    apply Real.cos_pos_of_mem_Ioo
    constructor <;> linarith [Real.pi_pos]
  have hp : 0 < 6 - Real.sin (t / 2) ^ 2 + 32 * Real.sin (t / 2) ^ 5 := by
    have hsq := Real.sin_sq_le_one (t / 2)
    have hpow : 0 ≤ Real.sin (t / 2) ^ 5 := le_of_lt (pow_pos hs _)
    linarith
  unfold kappaPrime
  apply mul_neg_of_neg_of_pos _ hp
  apply div_neg_of_neg_of_pos
  · exact neg_neg_of_pos hc
  · positivity

theorem deriv_kappa_neg {t : ℝ} (ht : 0 < t) (htpi : t < Real.pi) :
    deriv kappa t < 0 := by
  rw [(kappa_hasDerivAt ht htpi).deriv]
  exact kappaPrime_neg ht htpi

theorem strictAntiOn_kappa : StrictAntiOn kappa (Set.Ioo 0 Real.pi) := by
  apply strictAntiOn_of_deriv_neg (convex_Ioo 0 Real.pi)
  · intro t ht
    exact (kappa_hasDerivAt ht.1 ht.2).continuousAt.continuousWithinAt
  · intro t ht
    rw [interior_Ioo] at ht
    exact deriv_kappa_neg ht.1 ht.2

theorem kernelF_h : kernelF h = 0 := by
  have ht : h / 2 = Real.pi / 6 := by unfold h; ring
  unfold kernelF
  rw [ht, Real.sin_pi_div_six]
  norm_num

theorem kernelF_pi : kernelF Real.pi = 0 := by
  simp [kernelF]

/-- Second derivative identity `v'' = κ`, rather than an abstract Hessian
assumption. The equality for `v'` is transported on an open neighborhood. -/
theorem pairPotential_second_hasDerivAt {t : ℝ}
    (ht : 0 < t) (htpi : t < Real.pi) :
    HasDerivAt (deriv pairPotential) (kappa t) t := by
  have hder := (kernelF_hasDerivAt ht htpi).neg
  have heq : deriv pairPotential =ᶠ[nhds t] (fun x => -kernelF x) := by
    filter_upwards [isOpen_Ioo.mem_nhds (show t ∈ Set.Ioo 0 Real.pi from ⟨ht, htpi⟩)]
      with x hx
    exact deriv_pairPotential hx.1 hx.2
  simpa only [neg_neg] using hder.congr_of_eventuallyEq heq

theorem kernelF_continuousAt {t : ℝ} (ht : 0 < t) (htpi : t ≤ Real.pi) :
    ContinuousAt kernelF t := by
  have hs : 0 < Real.sin (t / 2) := by
    apply Real.sin_pos_of_pos_of_lt_pi
    · linarith
    · linarith [Real.pi_pos]
  have hden : 2 * Real.sin (t / 2) ≠ 0 := by positivity
  unfold kernelF
  apply ContinuousAt.mul (by fun_prop)
  apply ContinuousAt.sub _ continuousAt_const
  apply ContinuousAt.pow
  exact ContinuousAt.inv₀ (by fun_prop) hden

/-- Exactly the piecewise coefficient `ℓ` in manuscript Lemma `lem:cycle`.
The value at `h` is set to zero as in the manuscript. -/
def slopeCoefficient (t : ℝ) : ℝ :=
  if t < h then kernelF t / (h - t)
  else if t = h then 0 else kernelF t / (Real.pi - t)

def positiveRemainder (t : ℝ) : ℝ := kappa t - slopeCoefficient t

/-- The full scalar positivity claim `b(t) > 0` in Lemma `lem:cycle`.
The mean value theorem supplies a point `c > t` at which `ℓ(t) = κ(c)`.
This theorem supplies no directed-cycle bound. -/
theorem positiveRemainder_pos {t : ℝ} (ht : 0 < t) (htpi : t < Real.pi) :
    0 < positiveRemainder t := by
  have hhpos : 0 < h := by unfold h; positivity
  have hhpi : h < Real.pi := by unfold h; linarith [Real.pi_pos]
  unfold positiveRemainder slopeCoefficient
  by_cases hth : t < h
  · rw [if_pos hth]
    have hcont : ContinuousOn kernelF (Set.Icc t h) := by
      intro x hx
      exact (kernelF_continuousAt (lt_of_lt_of_le ht hx.1)
        (le_trans hx.2 (le_of_lt hhpi))).continuousWithinAt
    obtain ⟨c, hc, hsec⟩ := exists_hasDerivAt_eq_slope kernelF (fun x => -kappa x)
      hth hcont (fun x hx => kernelF_hasDerivAt (lt_trans ht hx.1) (lt_trans hx.2 hhpi))
    rw [kernelF_h, zero_sub, neg_div] at hsec
    have hcoef : kernelF t / (h - t) = kappa c := by linarith
    rw [hcoef]
    exact sub_pos.mpr (strictAntiOn_kappa ⟨ht, htpi⟩
      ⟨lt_trans ht hc.1, lt_trans hc.2 hhpi⟩ hc.1)
  · rw [if_neg hth]
    by_cases heq : t = h
    · rw [if_pos heq, heq, kappa_h]
      norm_num
    · rw [if_neg heq]
      have hcont : ContinuousOn kernelF (Set.Icc t Real.pi) := by
        intro x hx
        exact (kernelF_continuousAt (lt_of_lt_of_le ht hx.1) hx.2).continuousWithinAt
      obtain ⟨c, hc, hsec⟩ := exists_hasDerivAt_eq_slope kernelF (fun x => -kappa x)
        htpi hcont (fun x hx => kernelF_hasDerivAt (lt_trans ht hx.1) hx.2)
      rw [kernelF_pi, zero_sub, neg_div] at hsec
      have hcoef : kernelF t / (Real.pi - t) = kappa c := by linarith
      rw [hcoef]
      exact sub_pos.mpr (strictAntiOn_kappa ⟨ht, htpi⟩ ⟨lt_trans ht hc.1, hc.2⟩ hc.1)

theorem kernelF_pos_on_short_arc {t : ℝ} (ht : 0 < t) (hth : t < h) :
    0 < kernelF t := by
  have htpi : t < Real.pi := by unfold h at hth; linarith [Real.pi_pos]
  have hs : 0 < Real.sin (t / 2) := sin_half_pos ht htpi
  have hslt : Real.sin (t / 2) < 1 / 2 := by
    have hm := Real.strictMonoOn_sin
      (show t / 2 ∈ Set.Icc (-(Real.pi / 2)) (Real.pi / 2) from
        ⟨by linarith [Real.pi_pos], by linarith⟩)
      (show Real.pi / 6 ∈ Set.Icc (-(Real.pi / 2)) (Real.pi / 2) from
        ⟨by linarith [Real.pi_pos], by linarith [Real.pi_pos]⟩)
      (show t / 2 < Real.pi / 6 from by unfold h at hth; linarith)
    simpa only [Real.sin_pi_div_six] using hm
  have hd : 0 < 2 * Real.sin (t / 2) := by positivity
  have hinv : 1 < (2 * Real.sin (t / 2))⁻¹ := (one_lt_inv₀ hd).2 (by linarith)
  have hpow : 1 < (2 * Real.sin (t / 2))⁻¹ ^ 3 := one_lt_pow₀ hinv (by decide)
  exact mul_pos (Real.sin_pos_of_pos_of_lt_pi ht htpi) (sub_pos.mpr hpow)

theorem kernelF_neg_on_long_arc {t : ℝ} (hht : h < t) (htpi : t < Real.pi) :
    kernelF t < 0 := by
  have ht : 0 < t := by unfold h at hht; linarith [Real.pi_pos]
  have hs : 0 < Real.sin (t / 2) := sin_half_pos ht htpi
  have hsgt : 1 / 2 < Real.sin (t / 2) := by
    have hm := Real.strictMonoOn_sin
      (show Real.pi / 6 ∈ Set.Icc (-(Real.pi / 2)) (Real.pi / 2) from
        ⟨by linarith [Real.pi_pos], by linarith [Real.pi_pos]⟩)
      (show t / 2 ∈ Set.Icc (-(Real.pi / 2)) (Real.pi / 2) from
        ⟨by linarith [Real.pi_pos], by linarith⟩)
      (show Real.pi / 6 < t / 2 from by unfold h at hht; linarith)
    simpa only [Real.sin_pi_div_six] using hm
  have hd : 0 < 2 * Real.sin (t / 2) := by positivity
  have hinv : (2 * Real.sin (t / 2))⁻¹ < 1 := (inv_lt_one₀ hd).2 (by linarith)
  have hinvpos : 0 ≤ (2 * Real.sin (t / 2))⁻¹ := by positivity
  have hpow : (2 * Real.sin (t / 2))⁻¹ ^ 3 < 1 := pow_lt_one₀ hinvpos hinv (by decide)
  exact mul_neg_of_pos_of_neg (Real.sin_pos_of_pos_of_lt_pi ht htpi) (sub_neg.mpr hpow)

theorem kernelF_ge_neg_one {t : ℝ} (ht : 0 < t) (htpi : t < Real.pi) :
    -1 ≤ kernelF t := by
  have hs := Real.sin_pos_of_pos_of_lt_pi ht htpi
  have hsinle := Real.sin_le_one t
  have hhalf := sin_half_pos ht htpi
  have hterm : 0 ≤ Real.sin t * (2 * Real.sin (t / 2))⁻¹ ^ 3 := by positivity
  unfold kernelF
  nlinarith

theorem kernelF_eq_zero_iff {t : ℝ} (ht : 0 < t) (htpi : t < Real.pi) :
    kernelF t = 0 ↔ t = h := by
  constructor
  · intro hf
    rcases lt_trichotomy t h with hlt | heq | hgt
    · exact False.elim ((ne_of_gt (kernelF_pos_on_short_arc ht hlt)) hf)
    · exact heq
    · exact False.elim ((ne_of_lt (kernelF_neg_on_long_arc hgt htpi)) hf)
  · intro heq
    rw [heq, kernelF_h]

end

end DominantFiveBody.Coorbital
