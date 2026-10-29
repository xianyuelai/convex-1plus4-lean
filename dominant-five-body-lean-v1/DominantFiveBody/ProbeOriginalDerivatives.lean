import DominantFiveBody.BoundaryJacobian

/-! The derivative and strict secant assertions in the original proof of
Lemma 2.3. The already proved probe conclusion does not stand in for them. -/
noncomputable section
open Set Filter
namespace DominantFiveBody
open Coorbital

theorem twoSourceFunction_second_hasDerivAt {p q x : ℝ}
    (hhx : h<x) (hxpi : x<Real.pi) :
    HasDerivAt (deriv (twoSourceFunction p q))
      (-(p*kappaPrime x+q*kappaPrime (x-h))) x := by
  have hh : 0<h := by unfold h; positivity
  have heq : deriv (twoSourceFunction p q) =ᶠ[nhds x]
      (fun t => -(p*kappa t+q*kappa (t-h))) := by
    filter_upwards [isOpen_Ioo.mem_nhds (show x∈Ioo h Real.pi from ⟨hhx,hxpi⟩)] with t ht
    exact (twoSourceFunction_hasDerivAt ht.1 ht.2).deriv
  have hd := (((kappa_hasDerivAt (hh.trans hhx) hxpi).const_mul p).add
    (((kappa_hasDerivAt (sub_pos.mpr hhx) (by linarith)).comp x
      ((hasDerivAt_id x).sub_const h)).const_mul q)).neg
  convert! hd.congr_of_eventuallyEq heq using 1
  simp only [mul_one]

theorem twoSourceFunction_second_deriv_pos {p q x : ℝ}
    (hp : 0≤p) (hq : 0<q) (hhx : h<x) (hxpi : x<Real.pi) :
    0<deriv (deriv (twoSourceFunction p q)) x := by
  rw [(twoSourceFunction_second_hasDerivAt hhx hxpi).deriv]
  have hh : 0<h := by unfold h; positivity
  have hx := kappaPrime_neg (hh.trans hhx) hxpi
  have hxh := kappaPrime_neg (sub_pos.mpr hhx) (show x-h<Real.pi by linarith)
  have h1 := mul_nonpos_of_nonneg_of_nonpos hp hx.le
  have h2 := mul_neg_of_pos_of_neg hq hxh
  linarith

theorem twoSourceFunction_endpoint (p q : ℝ) :
    twoSourceFunction p q Real.pi = q*kernelF (Real.pi-h) := by
  simp [twoSourceFunction, kernelF_pi]

theorem twoSourceFunction_root_strict_secant {p q x : ℝ}
    (hp : 0≤p) (hq : 0<q) (hhx : h<x) (hxpi : x<Real.pi)
    (hroot : twoSourceFunction p q x=0) :
    deriv (twoSourceFunction p q) x < twoSourceFunction p q Real.pi/(Real.pi-x) ∧
      twoSourceFunction p q Real.pi/(Real.pi-x)<0 := by
  have hh : 0<h := by unfold h; positivity
  have hx : 0<x := hh.trans hhx
  have hxh : 0<x-h := sub_pos.mpr hhx
  have hc : ContinuousOn (twoSourceFunction p q) (Icc x Real.pi) := by
    intro y hy
    have hshift : ContinuousAt (fun z : ℝ => z-h) y := by fun_prop
    exact (((kernelF_continuousAt (hx.trans_le hy.1) hy.2).const_mul p).add
      ((ContinuousAt.comp (f := fun z : ℝ => z-h) (x := y)
        (kernelF_continuousAt (by linarith [hy.1]) (by linarith [hy.2]))
        hshift).const_mul q)).continuousWithinAt
  obtain ⟨c,hc,hsec⟩ := exists_hasDerivAt_eq_slope (twoSourceFunction p q)
    (fun y => -(p*kappa y+q*kappa (y-h))) hxpi hc
    (fun y hy => twoSourceFunction_hasDerivAt (hhx.trans hy.1) hy.2)
  have h1 := strictAntiOn_kappa ⟨hx,hxpi⟩ ⟨hx.trans hc.1,hc.2⟩ hc.1
  have h2 : kappa (c-h)<kappa (x-h) := by
    apply strictAntiOn_kappa ⟨hxh,by linarith⟩ ⟨by linarith [hc.1],by linarith [hc.2]⟩
    linarith [hc.1]
  have hcomp := add_lt_add_of_le_of_lt (mul_le_mul_of_nonneg_left h1.le hp)
    (mul_lt_mul_of_pos_left h2 hq)
  have hend : twoSourceFunction p q Real.pi<0 := by
    rw [twoSourceFunction_endpoint]
    exact mul_neg_of_pos_of_neg hq (kernelF_neg_on_long_arc
      (by unfold h; linarith [Real.pi_pos]) (by linarith))
  rw [hroot,sub_zero] at hsec
  refine ⟨?_,div_neg_of_neg_of_pos hend (sub_pos.mpr hxpi)⟩
  rw [(twoSourceFunction_hasDerivAt hhx hxpi).deriv,←hsec]
  linarith

theorem signedProbe_hasDerivAt {p q x : ℝ} (hx : x≠0) (hxh : x≠h)
    (hspan : twoSourceSpan x<Real.pi) :
    HasDerivAt (fun t => p*coorbitalKernel t+q*coorbitalKernel (t-h))
      (-(p*kappa |x|+q*kappa |x-h|)) x := by
  have hs := probe_separations_lt_pi hspan
  have hd := ((coorbitalKernel_hasDerivAt hx hs.1).const_mul p).add
    (((coorbitalKernel_hasDerivAt (sub_ne_zero.mpr hxh) hs.2).comp x
      ((hasDerivAt_id x).sub_const h)).const_mul q)
  convert! hd using 1
  simp only [mul_one]
  ring

theorem signedProbe_inner_deriv_neg {p q x : ℝ} (hp : 0≤p) (hq : 0<q)
    (hx : 0<x) (hxh : x<h) :
    deriv (fun t => p*coorbitalKernel t+q*coorbitalKernel (t-h)) x<0 := by
  have hh : 0<h := by unfold h; positivity
  have hs : twoSourceSpan x<Real.pi := by
    simp only [twoSourceSpan,max_eq_left hxh.le,min_eq_left hx.le]
    unfold h
    linarith [Real.pi_pos]
  rw [(signedProbe_hasDerivAt hx.ne' hxh.ne hs).deriv,abs_of_pos hx,
    abs_of_neg (sub_neg.mpr hxh)]
  have h1 := mul_nonneg hp (kappa_pos_on_short_arc hx hxh.le).le
  have h2 : 0<q*kappa (-(x-h)) :=
    mul_pos hq (kappa_pos_on_short_arc (by linarith) (by linarith))
  linarith

theorem signedProbe_reflection (p q x : ℝ) :
    q*coorbitalKernel (h-x)+p*coorbitalKernel ((h-x)-h) =
      -(p*coorbitalKernel x+q*coorbitalKernel (x-h)) := by
  rw [show h-x=-(x-h) by ring,show -(x-h)-h = -x by ring,
    coorbitalKernel_neg,coorbitalKernel_neg]
  ring

end DominantFiveBody
