import DominantFiveBody.Coorbital
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-! The integral identities in the original proof of Lemma 2.1.
Continuity includes the endpoint pi; differentiation is used only in
the open integration interval. All integrability hypotheses are proved.
-/

noncomputable section
open Set MeasureTheory
namespace DominantFiveBody.Coorbital

theorem kappa_continuousAt_closed_right {t : ℝ} (ht : 0<t) (htpi : t≤Real.pi) :
    ContinuousAt kappa t := by
  have hs : 0<Real.sin (t/2) := Real.sin_pos_of_pos_of_lt_pi
    (by linarith) (by linarith [Real.pi_pos])
  unfold kappa
  apply ContinuousAt.add _ (by fun_prop)
  exact ContinuousAt.div (by fun_prop) (by fun_prop) (by positivity)

theorem kappa_intervalIntegrable {a b : ℝ} (ha : 0<a) (hab : a≤b) (hb : b≤Real.pi) :
    IntervalIntegrable kappa volume a b := by
  apply ContinuousOn.intervalIntegrable_of_Icc hab
  intro t ht
  exact (kappa_continuousAt_closed_right (ha.trans_le ht.1) (ht.2.trans hb)).continuousWithinAt

theorem integral_kappa_eq_kernelF_sub {a b : ℝ} (ha : 0<a) (hab : a≤b) (hb : b≤Real.pi) :
    (∫ s in a..b,kappa s)=kernelF a-kernelF b := by
  have hc : ContinuousOn (fun t => -kernelF t) (Icc a b) := by
    intro t ht
    exact ((kernelF_continuousAt (ha.trans_le ht.1) (ht.2.trans hb)).neg).continuousWithinAt
  have hd : ∀ t∈Ioo a b,HasDerivAt (fun s => -kernelF s) (kappa t) t := by
    intro t ht
    convert! (kernelF_hasDerivAt (ha.trans ht.1) (ht.2.trans_le hb)).neg using 1
    simp only [neg_neg]
  have hh := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hab hc hd
    (kappa_intervalIntegrable ha hab hb)
  convert! hh using 1
  ring

theorem kernelF_integral_short {t : ℝ} (ht : 0<t) (hth : t<h) :
    kernelF t=(∫ s in t..h,kappa s) ∧
      (∫ s in t..h,kappa s)<(h-t)*kappa t := by
  have hhpi : h<Real.pi := by unfold h; linarith [Real.pi_pos]
  have hi := integral_kappa_eq_kernelF_sub ht hth.le hhpi.le
  rw [kernelF_h,sub_zero] at hi
  refine ⟨hi.symm,?_⟩
  rw [hi]
  have hp := positiveRemainder_pos ht (hth.trans hhpi)
  simp only [positiveRemainder,slopeCoefficient,if_pos hth] at hp
  have hdiv : kernelF t/(h-t)<kappa t := by linarith
  simpa only [mul_comm] using (div_lt_iff₀ (sub_pos.mpr hth)).mp hdiv

theorem kernelF_integral_long {t : ℝ} (hht : h<t) (htpi : t<Real.pi) :
    kernelF t=(∫ s in t..Real.pi,kappa s) ∧
      (∫ s in t..Real.pi,kappa s)<(Real.pi-t)*kappa t := by
  have ht : 0<t := lt_trans (by unfold h; positivity) hht
  have hi := integral_kappa_eq_kernelF_sub ht htpi.le le_rfl
  rw [kernelF_pi,sub_zero] at hi
  refine ⟨hi.symm,?_⟩
  rw [hi]
  have hp := positiveRemainder_pos ht htpi
  simp only [positiveRemainder,slopeCoefficient,if_neg (not_lt_of_ge hht.le),if_neg hht.ne'] at hp
  have hdiv : kernelF t/(Real.pi-t)<kappa t := by linarith
  simpa only [mul_comm] using (div_lt_iff₀ (sub_pos.mpr htpi)).mp hdiv

end DominantFiveBody.Coorbital
