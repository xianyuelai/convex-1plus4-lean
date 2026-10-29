import DominantFiveBody.CollisionTripleNestedRectangle

/-! # Proposition 4.3: actual full-field derivatives on the triple rectangle

The epsilon-dependent physical field J, rather than the compensated field
H alone, is differentiated. All source and target parameters may move.
-/

noncomputable section
open scoped BigOperators ContDiff
open Filter Set Topology
namespace DominantFiveBody
open Coorbital
set_option maxHeartbeats 1500000

def physicalSourceFullAngularAngularDerivative (eps s angle rho v : ℝ) : ℝ :=
  rho*physicalSourceAngularAngularDerivative s angle rho v-
    rho*s*Real.cos (angle-v)*((s^3)⁻¹-(1+eps)⁻¹)

theorem physicalSourceFullAngularField_hasDerivAt_angle (eps s angle rho v : ℝ)
    (hs : 0<s) (hsep : polarPoint s angle≠polarPoint rho v) :
    HasDerivAt (fun w => physicalSourceFullAngularField eps s angle rho w)
      (physicalSourceFullAngularAngularDerivative eps s angle rho v) v := by
  have hsin : HasDerivAt (fun w => Real.sin (angle-w)) (-Real.cos (angle-v)) v := by
    simpa only [Pi.sub_apply,Function.const_apply,id_eq,zero_sub,mul_neg,mul_one] using
      ((hasDerivAt_const v angle).sub (hasDerivAt_id v)).sin
  have ht := ((physicalSourceAngularField_hasDerivAt_angle s angle rho v hs hsep).const_mul rho).add
    (hsin.const_mul (rho*s*((s^3)⁻¹-(1+eps)⁻¹)))
  convert! ht using 1
  · funext w
    change physicalSourceFullAngularField eps s angle rho w=
      rho*physicalSourceAngularField s angle rho w+
        rho*s*((s^3)⁻¹-(1+eps)⁻¹)*Real.sin (angle-w)
    rw [physicalSourceFullAngularField_decomposition]
    ring
  · unfold physicalSourceFullAngularAngularDerivative
    ring

theorem physicalSourceFullAngularAngularDerivative_joint_contDiffAt
    (d : ℝ×((ℝ×ℝ)×(ℝ×ℝ))) (heps : 1+d.1≠0) (hs : d.2.1.1≠0)
    (hsep : polarPoint d.2.1.1 d.2.1.2≠polarPoint d.2.2.1 d.2.2.2) :
    ContDiffAt ℝ ∞ (fun z : ℝ×((ℝ×ℝ)×(ℝ×ℝ)) =>
      physicalSourceFullAngularAngularDerivative z.1 z.2.1.1 z.2.1.2 z.2.2.1 z.2.2.2) d := by
  have hV := (physicalSourceAngularAngularDerivative_joint_contDiffAt d.2 hs hsep).comp d
    (contDiff_snd.contDiffAt : ContDiffAt ℝ ∞ (fun z : ℝ×((ℝ×ℝ)×(ℝ×ℝ)) => z.2) d)
  have hiS : ContDiffAt ℝ ∞ (fun z : ℝ×((ℝ×ℝ)×(ℝ×ℝ)) => (z.2.1.1^3)⁻¹) d :=
    (by fun_prop : ContDiffAt ℝ ∞ (fun z : ℝ×((ℝ×ℝ)×(ℝ×ℝ)) => z.2.1.1^3) d).inv (pow_ne_zero 3 hs)
  have hiE : ContDiffAt ℝ ∞ (fun z : ℝ×((ℝ×ℝ)×(ℝ×ℝ)) => (1+z.1)⁻¹) d :=
    (by fun_prop : ContDiffAt ℝ ∞ (fun z : ℝ×((ℝ×ℝ)×(ℝ×ℝ)) => 1+z.1) d).inv heps
  unfold physicalSourceFullAngularAngularDerivative
  apply ContDiffAt.sub
  · exact (by fun_prop : ContDiffAt ℝ ∞ (fun z : ℝ×((ℝ×ℝ)×(ℝ×ℝ)) => z.2.2.1) d).mul hV
  · exact (by fun_prop : ContDiffAt ℝ ∞ (fun z : ℝ×((ℝ×ℝ)×(ℝ×ℝ)) =>
      z.2.2.1*z.2.1.1*Real.cos (z.2.1.2-z.2.2.2)) d).mul (hiS.sub hiE)

theorem physicalSourceFullAngularAngularDerivative_unit_kappa (angle psi : ℝ)
    (hne : angle≠psi) (hpi : |angle-psi|<Real.pi) :
    physicalSourceFullAngularAngularDerivative 0 1 angle 1 psi=kappa |psi-angle| := by
  simp only [physicalSourceFullAngularAngularDerivative,one_pow,inv_one,add_zero,
    sub_self,mul_zero,sub_zero,one_mul]
  exact physicalSourceAngularAngularDerivative_unit_kappa angle psi hne hpi

theorem physicalSourceFullAngularRadialDerivative_unit_h (angle psi : ℝ) (hgap : angle-psi=h) :
    physicalSourceFullAngularRadialDerivative 0 1 angle 1 psi= -3*Real.sqrt 3/4 := by
  have hh : 0<h := by unfold h;positivity
  have hne : angle≠psi := sub_ne_zero.mp (hgap ▸ hh.ne')
  have hpi : |angle-psi|<Real.pi := by rw [hgap,abs_of_pos hh];unfold h;linarith [Real.pi_pos]
  rw [physicalSourceFullAngularRadialDerivative_unit,
    physicalSourceAngularField_unit_kernel angle psi hne hpi,hgap,
    coorbitalKernel_eq_positive_formula h hh.le,kernelF_h,zero_add]
  exact physicalSourceAngularRadialDerivative_unit_h angle psi hgap

theorem physical_full_source_polar_rectangle_derivatives_uniform
    (eps rp vp rlo rhi vlo vhi : ℕ → ℝ) (psi angle0 : ℝ)
    (heps : Tendsto eps atTop (𝓝 0))
    (hrp : Tendsto rp atTop (𝓝 1)) (hvp : Tendsto vp atTop (𝓝 angle0))
    (hrlo : Tendsto rlo atTop (𝓝 1)) (hrhi : Tendsto rhi atTop (𝓝 1))
    (hvlo : Tendsto vlo atTop (𝓝 psi)) (hvhi : Tendsto vhi atTop (𝓝 psi))
    (hgap : angle0-psi=h) :
    ∀ eta : ℝ,0<eta → ∀ᶠ n in atTop,∀ rho∈uIcc (rlo n) (rhi n),∀ v∈uIcc (vlo n) (vhi n),
      |physicalSourceFullAngularRadialDerivative (eps n) (rp n) (vp n) rho v+3*Real.sqrt 3/4|<eta ∧
      |physicalSourceFullAngularAngularDerivative (eps n) (rp n) (vp n) rho v-(9/4 : ℝ)|<eta := by
  have hh : 0<h := by unfold h;positivity
  have hne : angle0≠psi := sub_ne_zero.mp (hgap ▸ hh.ne')
  have hpi : |angle0-psi|<Real.pi := by rw [hgap,abs_of_pos hh];unfold h;linarith [Real.pi_pos]
  have hsep := polarUnit_ne_of_angle_ne angle0 psi hne (by simpa only [abs_sub_comm] using hpi)
  let S : ℕ → Set (ℝ×ℝ) := fun n => uIcc (rlo n) (rhi n) ×ˢ uIcc (vlo n) (vhi n)
  let F : ℕ → (ℝ×ℝ) → ℝ×ℝ := fun n z =>
    (physicalSourceFullAngularRadialDerivative (eps n) (rp n) (vp n) z.1 z.2,
      physicalSourceFullAngularAngularDerivative (eps n) (rp n) (vp n) z.1 z.2)
  have hseq : ∀ z : ℕ → ℝ×ℝ,(∀ n,z n∈S n) → Tendsto (fun n => F n (z n)) atTop
      (𝓝 (-3*Real.sqrt 3/4,(9/4 : ℝ))) := by
    intro z hz
    have hrho := between_tendsto_common_limit rlo rhi (fun n => (z n).1) 1 (fun n => (hz n).1) hrlo hrhi
    have hv := between_tendsto_common_limit vlo vhi (fun n => (z n).2) psi (fun n => (hz n).2) hvlo hvhi
    have hp := heps.prodMk_nhds ((hrp.prodMk_nhds hvp).prodMk_nhds (hrho.prodMk_nhds hv))
    have hR := (physicalSourceFullAngularRadialDerivative_joint_contDiffAt
      (0,((1,angle0),(1,psi))) (by norm_num) hsep).continuousAt.tendsto.comp hp
    have hV := (physicalSourceFullAngularAngularDerivative_joint_contDiffAt
      (0,((1,angle0),(1,psi))) (by norm_num) (by norm_num) hsep).continuousAt.tendsto.comp hp
    have habs : |psi-angle0|=h := by rw [abs_sub_comm,hgap,abs_of_pos hh]
    simpa only [F,Function.comp_def,physicalSourceFullAngularRadialDerivative_unit_h _ _ hgap,
      physicalSourceFullAngularAngularDerivative_unit_kappa _ _ hne hpi,habs,kappa_h] using hR.prodMk_nhds hV
  have hU := limit_on_moving_sets_of_all_selections S (fun n => (rlo n,vlo n))
    (fun _ => ⟨left_mem_uIcc,left_mem_uIcc⟩) F _ hseq
  intro eta heta
  filter_upwards [hU eta heta] with n hn
  intro rho hr v hv
  have ht := hn (rho,v) ⟨hr,hv⟩
  simpa only [F,Prod.dist_eq,Real.dist_eq,max_lt_iff,
    show -3*Real.sqrt 3/4= -(3*Real.sqrt 3/4) by ring,sub_neg_eq_add] using ht

/-- Source eq:triple-J on the entire actual lower-triple rectangle,
including every radius between the minimum and maximum of all three. -/
theorem normalized_complete_lower_triple_full_rectangle_derivatives_uniform
    (eps : ℕ → ℝ) (mu : ℕ → MassRatio) (x : ℕ → Configuration)
    (heps : ∀ n,0<eps n) (hepst : Tendsto eps atTop (𝓝 0))
    (hm : ∀ n,PositiveRatio (mu n))
    (hx : ∀ n,NormalizedCentralConfiguration (masses (eps n) (mu n)) (x n))
    (r theta : ℕ → Satellite → ℝ) (hr : ∀ n i,0<r n i)
    (hpolar : ∀ n,satellitesRelative (x n)=polarSatellites (r n) (theta n))
    (horder : ∀ n,OrderedSemicircle (theta n))
    (muLimit : MassRatio) (hmt : Tendsto mu atTop (𝓝 muLimit))
    (qLimit : SatelliteConfiguration)
    (hqt : Tendsto (fun n => satellitesRelative (x n)) atTop (𝓝 qLimit))
    (theta0 : Satellite → ℝ) (htt : Tendsto theta atTop (𝓝 theta0))
    (center : Plane) (htriple : CompleteLimitingSatelliteTriple qLimit 3 center) :
    ∀ eta : ℝ,0<eta → ∀ᶠ n in atTop,
      ∀ rho∈uIcc (min (r n 0) (min (r n 1) (r n 2))) (max (r n 0) (max (r n 1) (r n 2))),
      ∀ v∈uIcc (theta n 0) (theta n 2),
      |physicalSourceFullAngularRadialDerivative (eps n) (r n 3) (theta n 3) rho v+3*Real.sqrt 3/4|<eta ∧
      |physicalSourceFullAngularAngularDerivative (eps n) (r n 3) (theta n 3) rho v-(9/4 : ℝ)|<eta := by
  obtain ⟨hrt,hunit,hmono,_,hspan⟩ := normalized_ordered_polar_limit_geometry eps mu x heps hepst hm hx
    r theta hr hpolar horder muLimit hmt qLimit hqt theta0 htt
  have hrat (i : Satellite) : Tendsto (fun n => r n i) atTop (𝓝 1) :=
    (continuous_apply i).continuousAt.tendsto.comp hrt
  have htat (i : TripleLabel) : Tendsto (fun n => theta n i.castSucc) atTop (𝓝 (theta0 0)) := by
    have he := complete_lower_triple_angles_equal qLimit theta0 hunit hmono hspan center htriple i 0
    simpa only [Function.comp_def,he,show (0 : TripleLabel).castSucc=(0 : Satellite) from rfl] using
      (continuous_apply i.castSucc).continuousAt.tendsto.comp htt
  have htp : Tendsto (fun n => theta n 3) atTop (𝓝 (theta0 3)) :=
    (continuous_apply (3 : Satellite)).continuousAt.tendsto.comp htt
  have hg := (normalized_complete_triple_limiting_exterior eps mu x heps hepst hm hx r theta hr hpolar horder
    muLimit hmt qLimit hqt theta0 htt 3 center htriple).2 0 (by decide)
  have hgap : theta0 3-theta0 0=h := by
    rw [abs_of_nonneg (sub_nonneg.mpr (hmono (by decide : (0 : Satellite)≤3)))] at hg
    exact hg
  apply physical_full_source_polar_rectangle_derivatives_uniform eps _ _ _ _ _ _ (theta0 0) (theta0 3)
    hepst (hrat 3) htp
  · simpa only [min_self] using (hrat 0).min ((hrat 1).min (hrat 2))
  · simpa only [max_self] using (hrat 0).max ((hrat 1).max (hrat 2))
  · exact htat 0
  · exact htat 2
  · exact hgap

end DominantFiveBody
