import DominantFiveBody.PolarCoordinates
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Sinc
import Mathlib.Analysis.Analytic.IsolatedZeros

/-! # Actual single-scale internal interaction regularization

Source: §5 `eq:chi` and `eq:regular-int`. Signed t supplies the analytic
extension; equality with the physical distance is asserted only for t > 0.
The extension has no ε/t coupling and remains defined at zero weights.
-/

noncomputable section
open Filter Set Topology
open scoped BigOperators ContDiff

namespace DominantFiveBody

theorem sinc_mul_argument (x : ℝ) : x*Real.sinc x=Real.sin x := by
  by_cases hx : x=0
  · simp [hx]
  · rw [Real.sinc_of_ne_zero hx]
    field_simp

theorem sinc_analyticAt (x : ℝ) : AnalyticAt ℝ Real.sinc x := by
  by_cases hx : x=0
  · subst x
    rw [Real.sinc_eq_dslope]
    obtain ⟨p,hp⟩ := (Real.analyticAt_sin : AnalyticAt ℝ Real.sin 0)
    exact ⟨p.fslope,hp.has_fpower_series_dslope_fslope⟩
  · have h : AnalyticAt ℝ (fun y : ℝ => Real.sin y/y) x :=
      Real.analyticAt_sin.div analyticAt_id hx
    apply h.congr
    filter_upwards [eventually_ne_nhds hx] with y hy
    exact (Real.sinc_of_ne_zero hy).symm

@[fun_prop] theorem sinc_contDiff (n : ℕ∞ω) : ContDiff ℝ n Real.sinc :=
  contDiff_iff_contDiffAt.mpr fun x => (sinc_analyticAt x).contDiffAt

@[fun_prop] theorem sinc_contDiffAt (n : ℕ∞ω) (x : ℝ) : ContDiffAt ℝ n Real.sinc x :=
  (sinc_analyticAt x).contDiffAt

def singleScaleChi (t b : ℝ) : ℝ := t*b^2/2*Real.sinc (t*b/2)^2

theorem singleScaleChi_identity (t b : ℝ) :
    1-Real.cos (t*b)=t*singleScaleChi t b := by
  have hs := sinc_mul_argument (t*b/2)
  have hc : Real.cos (t*b)=1-2*Real.sin (t*b/2)^2 := by
    have heq : t*b=2*(t*b/2) := by ring
    conv_lhs => rw [heq, Real.cos_two_mul]
    nlinarith [Real.sin_sq_add_cos_sq (t*b/2)]
  rw [hc]
  unfold singleScaleChi
  nlinarith [congrArg (fun a : ℝ => a^2) hs]

theorem singleScaleChi_complete : ∀ t b : ℝ,
    singleScaleChi t b=t*b^2/2*Real.sinc (t*b/2)^2 ∧
      1-Real.cos (t*b)=t*singleScaleChi t b := by
  intro t b
  exact ⟨rfl,singleScaleChi_identity t b⟩

@[fun_prop] theorem singleScaleChi_contDiff (n : ℕ∞ω) :
    ContDiff ℝ n (fun p : ℝ×ℝ => singleScaleChi p.1 p.2) := by
  unfold singleScaleChi
  fun_prop

def singleScaleRadius (R t w : ℝ) : ℝ := R+t*w

def singleScaleAngle (psi t z : ℝ) : ℝ := psi+t*z

def singleScaleWSq (R t wi wj zi zj : ℝ) : ℝ :=
  (wi-wj)^2+singleScaleRadius R t wi*singleScaleRadius R t wj*(zi-zj)^2*
    Real.sinc (t*(zi-zj)/2)^2

def singleScaleW (R t wi wj zi zj : ℝ) : ℝ :=
  Real.sqrt (singleScaleWSq R t wi wj zi zj)

theorem singleScale_distance_sq (R psi t wi wj zi zj : ℝ) :
    ‖polarPoint (singleScaleRadius R t wi) (singleScaleAngle psi t zi)-
      polarPoint (singleScaleRadius R t wj) (singleScaleAngle psi t zj)‖^2 =
        t^2*singleScaleWSq R t wi wj zi zj := by
  rw [polar_distance_sq]
  have heq : (singleScaleAngle psi t zi-singleScaleAngle psi t zj)/2=t*(zi-zj)/2 := by
    unfold singleScaleAngle
    ring
  rw [heq, ← sinc_mul_argument (t*(zi-zj)/2)]
  unfold singleScaleWSq singleScaleRadius
  ring

/-- This is a distance equality in the positive physical scale range. -/
theorem singleScale_distance (R psi t wi wj zi zj : ℝ) (ht : 0<t)
    (hW : 0<singleScaleWSq R t wi wj zi zj) :
    ‖polarPoint (singleScaleRadius R t wi) (singleScaleAngle psi t zi)-
      polarPoint (singleScaleRadius R t wj) (singleScaleAngle psi t zj)‖ =
        t*singleScaleW R t wi wj zi zj := by
  apply (sq_eq_sq₀ (norm_nonneg _) (mul_nonneg ht.le (Real.sqrt_nonneg _))).mp
  rw [singleScale_distance_sq, mul_pow]
  rw [Real.sq_sqrt hW.le]

theorem singleScale_radial_numerator (R t wi wj zi zj : ℝ) :
    singleScaleRadius R t wi-singleScaleRadius R t wj*Real.cos (t*(zi-zj)) =
      t*((wi-wj)+singleScaleRadius R t wj*singleScaleChi t (zi-zj)) := by
  have h := singleScaleChi_identity t (zi-zj)
  unfold singleScaleRadius at *
  nlinarith [congrArg (fun a : ℝ => (R+t*wj)*a) h]

abbrev SingleScaleVariables := Fin 8 → ℝ

/-- The full independent variables are R,t,wi,wj,zi,zj,ε,αj. -/
def singleScaleRadialTerm (p : SingleScaleVariables) : ℝ :=
  -p 6*p 1*p 7*((p 2-p 3)+singleScaleRadius (p 0) (p 1) (p 3)*
    singleScaleChi (p 1) (p 4-p 5))*singleScaleW (p 0) (p 1) (p 2) (p 3) (p 4) (p 5)^(-3 : ℤ)

def singleScaleAngularTerm (p : SingleScaleVariables) : ℝ :=
  -p 1*p 7*singleScaleRadius (p 0) (p 1) (p 2)*singleScaleRadius (p 0) (p 1) (p 3)*
    (p 4-p 5)*Real.sinc (p 1*(p 4-p 5))*
      (singleScaleW (p 0) (p 1) (p 2) (p 3) (p 4) (p 5)^(-3 : ℤ)-p 1^3/(1+p 6))

theorem singleScaleWSq_contDiff (n : ℕ∞ω) :
    ContDiff ℝ n (fun p : SingleScaleVariables =>
      singleScaleWSq (p 0) (p 1) (p 2) (p 3) (p 4) (p 5)) := by
  unfold singleScaleWSq singleScaleRadius
  fun_prop

theorem singleScaleW_contDiffAt (n : ℕ∞ω) (p : SingleScaleVariables)
    (hW : 0<singleScaleWSq (p 0) (p 1) (p 2) (p 3) (p 4) (p 5)) :
    ContDiffAt ℝ n (fun q : SingleScaleVariables =>
      singleScaleW (q 0) (q 1) (q 2) (q 3) (q 4) (q 5)) p := by
  exact (singleScaleWSq_contDiff n).contDiffAt.sqrt (ne_of_gt hW)

theorem singleScaleRadialTerm_contDiffAt (n : ℕ∞ω) (p : SingleScaleVariables)
    (hW : 0<singleScaleWSq (p 0) (p 1) (p 2) (p 3) (p 4) (p 5)) :
    ContDiffAt ℝ n singleScaleRadialTerm p := by
  unfold singleScaleRadialTerm
  have h := singleScaleW_contDiffAt n p hW
  have hn : singleScaleW (p 0) (p 1) (p 2) (p 3) (p 4) (p 5)≠0 :=
    ne_of_gt (Real.sqrt_pos.mpr hW)
  simp only [zpow_neg, zpow_ofNat]
  have hz := (h.pow 3).inv (pow_ne_zero 3 hn)
  have hpre : ContDiff ℝ n (fun q : SingleScaleVariables =>
      -q 6*q 1*q 7*((q 2-q 3)+singleScaleRadius (q 0) (q 1) (q 3)*
        singleScaleChi (q 1) (q 4-q 5))) := by
    unfold singleScaleRadius singleScaleChi
    fun_prop
  exact hpre.contDiffAt.mul hz

theorem singleScaleAngularTerm_contDiffAt (n : ℕ∞ω) (p : SingleScaleVariables)
    (hW : 0<singleScaleWSq (p 0) (p 1) (p 2) (p 3) (p 4) (p 5)) (heps : 1+p 6≠0) :
    ContDiffAt ℝ n singleScaleAngularTerm p := by
  unfold singleScaleAngularTerm
  have h := singleScaleW_contDiffAt n p hW
  have hn : singleScaleW (p 0) (p 1) (p 2) (p 3) (p 4) (p 5)≠0 :=
    ne_of_gt (Real.sqrt_pos.mpr hW)
  simp only [zpow_neg, zpow_ofNat]
  have hz := (h.pow 3).inv (pow_ne_zero 3 hn)
  have hpre : ContDiff ℝ n (fun q : SingleScaleVariables =>
      -q 1*q 7*singleScaleRadius (q 0) (q 1) (q 2)*singleScaleRadius (q 0) (q 1) (q 3)*
        (q 4-q 5)*Real.sinc (q 1*(q 4-q 5))) := by
    unfold singleScaleRadius
    fun_prop
  have hback : ContDiffAt ℝ n (fun q : SingleScaleVariables => q 1^3/(1+q 6)) p := by
    fun_prop
  exact hpre.contDiffAt.mul (hz.sub hback)

/-- Each extended radial summand equals the actual mass-divided Newtonian
summand for μⱼ=t³αⱼ at every positive scale. -/
theorem singleScaleRadialTerm_eq_physical (p : SingleScaleVariables) (psi : ℝ)
    (ht : 0<p 1) (hW : 0<singleScaleWSq (p 0) (p 1) (p 2) (p 3) (p 4) (p 5)) :
    singleScaleRadialTerm p =
      -p 6*(p 1^3*p 7)*
        (singleScaleRadius (p 0) (p 1) (p 2)-singleScaleRadius (p 0) (p 1) (p 3)*
          Real.cos (singleScaleAngle psi (p 1) (p 4)-singleScaleAngle psi (p 1) (p 5)))/
        ‖polarPoint (singleScaleRadius (p 0) (p 1) (p 2)) (singleScaleAngle psi (p 1) (p 4))-
          polarPoint (singleScaleRadius (p 0) (p 1) (p 3)) (singleScaleAngle psi (p 1) (p 5))‖^3 := by
  rw [singleScale_distance (p 0) psi (p 1) (p 2) (p 3) (p 4) (p 5) ht hW]
  have heq : singleScaleAngle psi (p 1) (p 4)-singleScaleAngle psi (p 1) (p 5)=p 1*(p 4-p 5) := by
    unfold singleScaleAngle
    ring
  rw [heq, singleScale_radial_numerator]
  unfold singleScaleRadialTerm
  have hn : singleScaleW (p 0) (p 1) (p 2) (p 3) (p 4) (p 5)≠0 :=
    ne_of_gt (Real.sqrt_pos.mpr hW)
  simp only [zpow_neg, zpow_ofNat]
  field_simp [ne_of_gt ht, hn]

/-- Each extended angular summand equals the real polar residual summand.
No αⱼ or 1−αⱼ is divided out, so endpoints remain included. -/
theorem singleScaleAngularTerm_eq_physical (p : SingleScaleVariables) (psi : ℝ)
    (ht : 0<p 1) (hW : 0<singleScaleWSq (p 0) (p 1) (p 2) (p 3) (p 4) (p 5))
    (heps : 1+p 6≠0) :
    singleScaleAngularTerm p =
      (p 1^3*p 7)*singleScaleRadius (p 0) (p 1) (p 2)*singleScaleRadius (p 0) (p 1) (p 3)*
        Real.sin (singleScaleAngle psi (p 1) (p 5)-singleScaleAngle psi (p 1) (p 4))*
        ((‖polarPoint (singleScaleRadius (p 0) (p 1) (p 2)) (singleScaleAngle psi (p 1) (p 4))-
          polarPoint (singleScaleRadius (p 0) (p 1) (p 3)) (singleScaleAngle psi (p 1) (p 5))‖^3)⁻¹-
          (1+p 6)⁻¹) := by
  rw [singleScale_distance (p 0) psi (p 1) (p 2) (p 3) (p 4) (p 5) ht hW]
  have heq : singleScaleAngle psi (p 1) (p 5)-singleScaleAngle psi (p 1) (p 4)=-(p 1*(p 4-p 5)) := by
    unfold singleScaleAngle
    ring
  rw [heq, Real.sin_neg, ← sinc_mul_argument (p 1*(p 4-p 5))]
  unfold singleScaleAngularTerm
  have hn : singleScaleW (p 0) (p 1) (p 2) (p 3) (p 4) (p 5)≠0 :=
    ne_of_gt (Real.sqrt_pos.mpr hW)
  simp only [zpow_neg, zpow_ofNat]
  field_simp [ne_of_gt ht, hn, heps]

end DominantFiveBody
