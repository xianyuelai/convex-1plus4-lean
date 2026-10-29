import DominantFiveBody.CollisionPairScales
import DominantFiveBody.CollisionClassification

/-! # Actual smaller-pair equations inside a complete triple

The current mass normalized averages are proved from physical angular
rows. No chart root or individual pair-fraction limit is used.
-/

noncomputable section
open scoped BigOperators ContDiff
open Filter Set Topology

namespace DominantFiveBody

def physicalSourceAngularAngularDerivative (s angle rho v : ℝ) : ℝ :=
  s*(-Real.cos (angle-v)*((‖polarPoint rho v-polarPoint s angle‖^3)⁻¹-(s^3)⁻¹)+
    3*rho*s*(Real.sin (angle-v))^2*(‖polarPoint rho v-polarPoint s angle‖^5)⁻¹)

/-- The angle derivative in `eq:nested-field` is the derivative of the
actual physical target field, with the current near source retained. -/
theorem physicalSourceAngularField_hasDerivAt_angle (s angle rho v : ℝ)
    (hs : 0<s) (hsep : polarPoint s angle≠polarPoint rho v) :
    HasDerivAt (fun w : ℝ => physicalSourceAngularField s angle rho w)
      (physicalSourceAngularAngularDerivative s angle rho v) v := by
  have hp := polarPoint_hasDerivAt_angle rho v
  have hF := (newtonTargetField_hasFDerivAt (polarPoint s angle) (polarPoint rho v) hsep).comp_hasDerivAt v hp
  have hJ : HasDerivAt (fun w : ℝ => quarterTurn (polarPoint 1 w))
      (-polarPoint 1 v) v := by
    have h := quarterTurnLinear.toContinuousLinearMap.hasFDerivAt.comp_hasDerivAt v
      (polarPoint_hasDerivAt_angle 1 v)
    convert! h using 1
    ext k
    fin_cases k <;> simp [quarterTurn,point]
  have h := (hF.sub_const ((‖polarPoint s angle‖^3)⁻¹ • polarPoint s angle)).inner ℝ hJ
  convert! h using 1
  · funext w
    exact physicalSourceAngularField_eq_cartesian s angle rho w hs
  · simp only [newtonTargetDerivative_apply,Function.comp_def,newtonTargetField,
      inner_sub_left,real_inner_smul_left,
      inner_neg_right,polarPoint_inner_radial,polarPoint_inner_rotation,
      quarterTurn_inner_quarterTurn,sub_self,Real.sin_zero,Real.cos_zero,
      one_mul,mul_one,mul_zero,sub_zero,polarPoint_norm,abs_of_pos hs]
    unfold physicalSourceAngularAngularDerivative
    rw [norm_sub_rev (polarPoint s angle)]
    simp only [div_eq_mul_inv]
    ring

theorem physicalSourceAngularAngularDerivative_joint_contDiffAt
    (d : (ℝ×ℝ)×(ℝ×ℝ)) (hs : d.1.1≠0)
    (hsep : polarPoint d.1.1 d.1.2≠polarPoint d.2.1 d.2.2) :
    ContDiffAt ℝ ∞ (fun z : (ℝ×ℝ)×(ℝ×ℝ) =>
      physicalSourceAngularAngularDerivative z.1.1 z.1.2 z.2.1 z.2.2) d := by
  have hsource : ContDiff ℝ ∞ (fun z : (ℝ×ℝ)×(ℝ×ℝ) => polarPoint z.1.1 z.1.2) :=
    (polarPoint_contDiff ∞).comp contDiff_fst
  have htarget : ContDiff ℝ ∞ (fun z : (ℝ×ℝ)×(ℝ×ℝ) => polarPoint z.2.1 z.2.2) :=
    (polarPoint_contDiff ∞).comp contDiff_snd
  have hn := (htarget.contDiffAt.sub hsource.contDiffAt).norm ℝ
    (sub_ne_zero.mpr (Ne.symm hsep))
  have hd : ‖polarPoint d.2.1 d.2.2-polarPoint d.1.1 d.1.2‖≠0 :=
    norm_ne_zero_iff.mpr (sub_ne_zero.mpr (Ne.symm hsep))
  have hi3 := (hn.pow 3).inv (pow_ne_zero 3 hd)
  have hi5 := (hn.pow 5).inv (pow_ne_zero 5 hd)
  have his : ContDiffAt ℝ ∞ (fun z : (ℝ×ℝ)×(ℝ×ℝ) => (z.1.1^3)⁻¹) d := by
    exact (by fun_prop : ContDiffAt ℝ ∞ (fun z : (ℝ×ℝ)×(ℝ×ℝ) => z.1.1^3) d).inv
      (pow_ne_zero 3 hs)
  unfold physicalSourceAngularAngularDerivative
  apply ContDiffAt.mul (by fun_prop)
  apply ContDiffAt.add
  · exact (by fun_prop : ContDiffAt ℝ ∞ (fun z : (ℝ×ℝ)×(ℝ×ℝ) =>
      -Real.cos (z.1.2-z.2.2)) d).mul (hi3.sub his)
  · exact (by fun_prop : ContDiffAt ℝ ∞ (fun z : (ℝ×ℝ)×(ℝ×ℝ) =>
      3*z.2.1*z.1.1*(Real.sin (z.1.2-z.2.2))^2) d).mul hi5

theorem physicalPairExteriorAngularField_hasDerivAt_angle
    (mu r theta : Satellite → ℝ) (a b : Satellite) (rho v : ℝ)
    (hr : ∀ i,0<r i)
    (hsep : ∀ j∈pairExteriorLabels a b,polarPoint (r j) (theta j)≠polarPoint rho v) :
    HasDerivAt (fun w => physicalPairExteriorAngularField mu r theta a b rho w)
      (∑ j∈pairExteriorLabels a b,mu j*physicalSourceAngularAngularDerivative (r j) (theta j) rho v) v := by
  have hsum := HasDerivAt.sum (u := pairExteriorLabels a b) (fun j hj =>
    (physicalSourceAngularField_hasDerivAt_angle (r j) (theta j) rho v (hr j) (hsep j hj)).const_mul (mu j))
  have heq : (fun w => physicalPairExteriorAngularField mu r theta a b rho w)=
      (fun w => ∑ j∈pairExteriorLabels a b,mu j*physicalSourceAngularField (r j) (theta j) rho w) :=
    funext (fun w => physicalPairExteriorAngularField_eq_source_sum mu r theta a b rho w)
  rw [heq]
  convert! hsum using 1
  funext w
  simp only [Finset.sum_apply]

/-- Both displayed target derivatives in source `eq:nested-field` are
proved for the actual summed field at every separated physical target. -/
theorem physical_pair_exterior_angular_derivatives
    (mu r theta : Satellite → ℝ) (a b : Satellite) (rho v : ℝ)
    (hr : ∀ i,0<r i)
    (hsep : ∀ j∈pairExteriorLabels a b,polarPoint (r j) (theta j)≠polarPoint rho v) :
    HasDerivAt (fun s => physicalPairExteriorAngularField mu r theta a b s v)
      (∑ j∈pairExteriorLabels a b,mu j*physicalSourceAngularRadialDerivative (r j) (theta j) rho v) rho ∧
    HasDerivAt (fun w => physicalPairExteriorAngularField mu r theta a b rho w)
      (∑ j∈pairExteriorLabels a b,mu j*physicalSourceAngularAngularDerivative (r j) (theta j) rho v) v :=
  ⟨physicalPairExteriorAngularField_hasDerivAt_radius mu r theta a b rho v hr hsep,
    physicalPairExteriorAngularField_hasDerivAt_angle mu r theta a b rho v hr hsep⟩

theorem small_angle_cosine_defect_scaled_limit (gap d : ℕ → ℝ) (omega : ℝ)
    (hg : Tendsto gap atTop (nhds 0)) (hd : ∀ n,0<d n)
    (hgd : Tendsto (fun n => gap n/d n) atTop (nhds omega)) :
    Tendsto (fun n => (1-Real.cos (gap n))/d n) atTop (nhds 0) := by
  let F : ℝ → ℝ := fun x => 1-Real.cos x
  have hc : ContDiffAt ℝ ∞ F 0 := by fun_prop
  have hfd : fderiv ℝ F 0=0 := by
    have hh := (hasDerivAt_const (0 : ℝ) (1 : ℝ)).sub (Real.hasDerivAt_cos 0)
    have hh' : HasDerivAt F 0 0 := by
      convert! hh using 1
      simp
    simpa using hh'.hasFDerivAt.fderiv
  have hv : Tendsto (fun n => (d n)⁻¹ • (gap n-(0 : ℝ))) atTop (nhds omega) := by
    simpa only [smul_eq_mul,sub_zero,div_eq_mul_inv,mul_comm] using hgd
  have ht := strict_fderiv_scaled_difference_limit F (fderiv ℝ F 0) 0
    (hc.hasStrictFDerivAt (by simp)) (fun _ => 0) gap tendsto_const_nhds hg d hd omega hv
  simpa only [F,Real.cos_zero,sub_self,sub_zero,hfd,zero_apply] using ht

/-- The near source has vanishing weighted radial derivative on every
selected first-order triple geometry, including a zero limiting share. -/
theorem physicalSourceAngularRadialDerivative_near_weighted_limit
    (mass s angle rho v d : ℕ → ℝ) (omega L : ℝ)
    (hs : Tendsto s atTop (nhds 1))
    (hd : ∀ n,0<d n)
    (hgap : Tendsto (fun n => angle n-v n) atTop (nhds 0))
    (hgd : Tendsto (fun n => (angle n-v n)/d n) atTop (nhds omega))
    (hrd : Tendsto (fun n => (rho n-s n)/d n) atTop (nhds 0))
    (hsep : ∀ n,polarPoint (s n) (angle n)≠polarPoint (rho n) (v n))
    (hDd : Tendsto (fun n => ‖polarPoint (rho n) (v n)-polarPoint (s n) (angle n)‖/d n)
      atTop (nhds 1))
    (hmd : Tendsto (fun n => mass n/d n^3) atTop (nhds L)) :
    Tendsto (fun n => mass n*physicalSourceAngularRadialDerivative (s n) (angle n) (rho n) (v n))
      atTop (nhds 0) := by
  have hsinc : Tendsto (fun n => Real.sinc (angle n-v n)) atTop (nhds 1) := by
    simpa only [Function.comp_def,Real.sinc_zero] using
      Real.continuous_sinc.continuousAt.tendsto.comp hgap
  have hsin : Tendsto (fun n => Real.sin (angle n-v n)/d n) atTop (nhds omega) := by
    convert hsinc.mul hgd using 1
    · funext n
      rw [← sinc_mul_argument (angle n-v n)]
      ring
    · ring
  have hcos := small_angle_cosine_defect_scaled_limit _ d omega hgap hd hgd
  have hproj : Tendsto (fun n => (rho n-s n*Real.cos (angle n-v n))/d n) atTop (nhds 0) := by
    convert! hrd.add (hs.mul hcos) using 1
    · funext n; ring
    · ring
  have hi5 := (hDd.pow 5).inv₀ (by norm_num : (1 : ℝ)^5≠0)
  have ht := ((((tendsto_const_nhds : Tendsto (fun _ : ℕ => (-3 : ℝ)) atTop (nhds (-3))).mul hmd).mul hs).mul hsin).mul hproj |>.mul hi5
  convert! ht using 1
  · funext n
    have hdn := ne_of_gt (hd n)
    have hDn := norm_ne_zero_iff.mpr (sub_ne_zero.mpr (Ne.symm (hsep n)))
    unfold physicalSourceAngularRadialDerivative
    field_simp [hdn,hDn]
  · ring

/-- For a tangential unit scaled separation, the weighted near-source
angle derivative converges to twice its current cubic mass coefficient.
The limiting share L may vanish; it is never cancelled. -/
theorem physicalSourceAngularAngularDerivative_near_weighted_limit
    (mass s angle rho v d : ℕ → ℝ) (omega L : ℝ)
    (hs : Tendsto s atTop (nhds 1)) (hrho : Tendsto rho atTop (nhds 1))
    (hd : ∀ n,0<d n) (hdt : Tendsto d atTop (nhds 0)) (homega : omega^2=1)
    (hgap : Tendsto (fun n => angle n-v n) atTop (nhds 0))
    (hgd : Tendsto (fun n => (angle n-v n)/d n) atTop (nhds omega))
    (hsep : ∀ n,polarPoint (s n) (angle n)≠polarPoint (rho n) (v n))
    (hDd : Tendsto (fun n => ‖polarPoint (rho n) (v n)-polarPoint (s n) (angle n)‖/d n)
      atTop (nhds 1))
    (hmd : Tendsto (fun n => mass n/d n^3) atTop (nhds L)) :
    Tendsto (fun n => mass n*physicalSourceAngularAngularDerivative (s n) (angle n) (rho n) (v n))
      atTop (nhds (2*L)) := by
  have hsinc : Tendsto (fun n => Real.sinc (angle n-v n)) atTop (nhds 1) := by
    simpa only [Function.comp_def,Real.sinc_zero] using
      Real.continuous_sinc.continuousAt.tendsto.comp hgap
  have hsin : Tendsto (fun n => Real.sin (angle n-v n)/d n) atTop (nhds omega) := by
    convert hsinc.mul hgd using 1
    · funext n
      rw [← sinc_mul_argument (angle n-v n)]
      ring
    · ring
  have hcos : Tendsto (fun n => Real.cos (angle n-v n)) atTop (nhds 1) := by
    simpa only [Function.comp_def,Real.cos_zero] using
      Real.continuous_cos.continuousAt.tendsto.comp hgap
  have hmass : Tendsto mass atTop (nhds 0) := by
    convert! hmd.mul (hdt.pow 3) using 1
    · funext n
      field_simp [ne_of_gt (hd n)]
    · ring
  have hi3 := (hDd.pow 3).inv₀ (by norm_num : (1 : ℝ)^3≠0)
  have hi5 := (hDd.pow 5).inv₀ (by norm_num : (1 : ℝ)^5≠0)
  have hpos := (((((hmd.mul (tendsto_const_nhds : Tendsto (fun _ : ℕ => (3 : ℝ)) atTop (nhds 3))).mul hrho).mul (hs.pow 2)).mul (hsin.pow 2)).mul hi5)
  have hneg := ((hmd.mul hs).mul hcos).mul hi3
  have hsource := (hmass.mul hcos).div (hs.pow 2) (by norm_num : (1 : ℝ)^2≠0)
  have ht : Tendsto (fun n => mass n/d n^3*3*rho n*(s n)^2*(Real.sin (angle n-v n)/d n)^2*
      ((‖polarPoint (rho n) (v n)-polarPoint (s n) (angle n)‖/d n)^5)⁻¹-
      mass n/d n^3*s n*Real.cos (angle n-v n)*
      ((‖polarPoint (rho n) (v n)-polarPoint (s n) (angle n)‖/d n)^3)⁻¹+
      mass n*Real.cos (angle n-v n)/(s n)^2) atTop (nhds (2*L)) := by
    convert! (hpos.sub hneg).add hsource using 1
    simp only [homega]
    ring
  apply ht.congr'
  filter_upwards [hs.eventually_ne (by norm_num : (1 : ℝ)≠0)] with n hsn
  have hdn := ne_of_gt (hd n)
  have hDn := norm_ne_zero_iff.mpr (sub_ne_zero.mpr (Ne.symm (hsep n)))
  unfold physicalSourceAngularAngularDerivative
  field_simp [hdn,hDn,hsn]
  ring

theorem sum_satellite_selected_four (f : Satellite → ℝ) (a b c p : Satellite)
    (hab : a≠b) (hcp : c≠p) (hc : c∈pairExteriorLabels a b) (hp : p∈pairExteriorLabels a b) :
    ∑ i,f i=f a+f b+f c+f p := by
  have hset := pairExteriorLabels_eq_two a b c p hab hc hp hcp
  have hb : b∈Finset.univ.erase a := Finset.mem_erase.mpr ⟨Ne.symm hab,Finset.mem_univ b⟩
  rw [← Finset.sum_erase_add _ _ (Finset.mem_univ a),← Finset.sum_erase_add _ _ hb]
  change (∑ j∈pairExteriorLabels a b,f j)+f b+f a=_
  rw [hset]
  simp only [Finset.sum_pair hcp]
  ring

def nestedPairCurrentKernel (eps : ℝ) (mu r theta : Satellite → ℝ) (a b c : Satellite) : ℝ :=
  (mu a*fullAngularMatrix eps r theta a c+mu b*fullAngularMatrix eps r theta b c)/(mu a+mu b)

def nestedPairCurrentExterior (eps : ℝ) (mu r theta : Satellite → ℝ) (a b p : Satellite) : ℝ :=
  (mu a*fullAngularMatrix eps r theta a p+mu b*fullAngularMatrix eps r theta b p)/(mu a+mu b)

/-- Source eq:nested-macro-average, with the genuine current variational
kernel. Internal pair forces cancel before division by the proved nonzero
current total pair mass. Individual fractions may be arbitrary. -/
theorem physical_nested_macro_average (eps : ℝ) (mu r theta : Satellite → ℝ)
    (a b c p : Satellite) (hab : a≠b) (hcp : c≠p)
    (hc : c∈pairExteriorLabels a b) (hp : p∈pairExteriorLabels a b)
    (hxi : mu a+mu b≠0) (hroot : ∀ i,angularResidual eps mu r theta i=0) :
    (mu a+mu b+mu c)*nestedPairCurrentKernel eps mu r theta a b c+
      mu p*(nestedPairCurrentExterior eps mu r theta a b p-fullAngularMatrix eps r theta c p)=0 := by
  have ha := hroot a
  have hb := hroot b
  have hcc := hroot c
  rw [angularResidual_eq_full_matrix_sum,sum_satellite_selected_four _ a b c p hab hcp hc hp] at ha hb hcc
  simp only [fullAngularMatrix_self,mul_zero,zero_add,add_zero] at ha hb hcc
  rw [fullAngularMatrix_reverse eps r theta a b] at hb
  rw [fullAngularMatrix_reverse eps r theta a c,fullAngularMatrix_reverse eps r theta b c] at hcc
  unfold nestedPairCurrentKernel nestedPairCurrentExterior
  field_simp [hxi]
  linear_combination mu a*ha+mu b*hb-(mu a+mu b)*hcc

theorem nested_exterior_mass_eq (mu : MassRatio) (hm : PositiveRatio mu)
    (a b c p : Satellite) (hab : a≠b) (hcp : c≠p)
    (hc : c∈pairExteriorLabels a b) (hp : p∈pairExteriorLabels a b) :
    mu p=1-(mu a+mu b+mu c) := by
  have hsum := hm.2
  rw [sum_satellite_selected_four _ a b c p hab hcp hc hp] at hsum
  linarith

theorem normalized_nested_macro_average (eps : ℝ) (mu : MassRatio) (x : Configuration)
    (heps : 0<eps) (hm : PositiveRatio mu) (hx : NormalizedCentralConfiguration (masses eps mu) x)
    (r theta : Satellite → ℝ) (hr : ∀ i,0<r i) (hpolar : satellitesRelative x=polarSatellites r theta)
    (a b c p : Satellite) (hab : a≠b) (hcp : c≠p)
    (hc : c∈pairExteriorLabels a b) (hp : p∈pairExteriorLabels a b) :
    (mu a+mu b+mu c)*nestedPairCurrentKernel eps mu r theta a b c+
      (1-(mu a+mu b+mu c))*(nestedPairCurrentExterior eps mu r theta a b p-
        fullAngularMatrix eps r theta c p)=0 := by
  rw [← nested_exterior_mass_eq mu hm a b c p hab hcp hc hp]
  exact physical_nested_macro_average eps mu r theta a b c p hab hcp hc hp
    (ne_of_gt (add_pos (hm.1 a) (hm.1 b)))
    (polarResiduals_zero_of_normalized eps mu x hx hm heps r theta hr hpolar).2

/-- A true near-source variational kernel has the inverse-square scaled
limit. The scale is the actual triple diameter; its ratio to the source
distance and the signed angular separation are explicit geometric data. -/
theorem physicalSourceFullAngularField_near_scaled_limit
    (eps s angle rho v d : ℕ → ℝ) (omega : ℝ)
    (heps : Tendsto eps atTop (nhds 0))
    (hs : Tendsto s atTop (nhds 1)) (hrho : Tendsto rho atTop (nhds 1))
    (hd : ∀ n,0<d n) (hdt : Tendsto d atTop (nhds 0))
    (hgap : Tendsto (fun n => angle n-v n) atTop (nhds 0))
    (hgd : Tendsto (fun n => (angle n-v n)/d n) atTop (nhds omega))
    (hsep : ∀ n,polarPoint (s n) (angle n)≠polarPoint (rho n) (v n))
    (hDd : Tendsto (fun n => ‖polarPoint (rho n) (v n)-polarPoint (s n) (angle n)‖/d n)
      atTop (nhds 1)) :
    Tendsto (fun n => d n^2*physicalSourceFullAngularField (eps n) (s n) (angle n) (rho n) (v n))
      atTop (nhds omega) := by
  have hsinc : Tendsto (fun n => Real.sinc (angle n-v n)) atTop (nhds 1) := by
    simpa only [Function.comp_def,Real.sinc_zero] using
      Real.continuous_sinc.continuousAt.tendsto.comp hgap
  have hsin : Tendsto (fun n => Real.sin (angle n-v n)/d n) atTop (nhds omega) := by
    convert hsinc.mul hgd using 1
    · funext n
      rw [← sinc_mul_argument (angle n-v n)]
      ring
    · ring
  have hinv := ((hDd.pow 3).inv₀ (by norm_num : (1 : ℝ)^3≠0))
  have hc := ((tendsto_const_nhds : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (nhds 1)).add heps).inv₀
    (by norm_num : (1 : ℝ)+0≠0)
  have hsin0 := (Real.continuous_sin.continuousAt.tendsto.comp hgap)
  have hmain := ((hrho.mul hs).mul hsin).mul hinv
  have herror := (((hdt.pow 2).mul (hrho.mul hs)).mul hsin0).mul hc
  convert! hmain.sub herror using 1
  · funext n
    have hdn := ne_of_gt (hd n)
    have hDn := norm_ne_zero_iff.mpr (sub_ne_zero.mpr (Ne.symm (hsep n)))
    unfold physicalSourceFullAngularField
    simp only [Function.comp_def]
    field_simp [hdn,hDn]
  · simp

/-- A separated exterior source is differentiated jointly while source
parameters and both targets move. The signed scaled target angle may be
either orientation, and no rate for the source convergence is assumed. -/
theorem physicalSourceFullAngularField_moving_secant_limit
    (eps s angle ra va rb vb d : ℕ → ℝ) (angle0 psi omega : ℝ)
    (heps : Tendsto eps atTop (nhds 0))
    (hst : Tendsto s atTop (nhds 1)) (hangt : Tendsto angle atTop (nhds angle0))
    (hrat : Tendsto ra atTop (nhds 1)) (hrbt : Tendsto rb atTop (nhds 1))
    (hvat : Tendsto va atTop (nhds psi)) (hvbt : Tendsto vb atTop (nhds psi))
    (hd : ∀ n,0<d n)
    (hrd : Tendsto (fun n => (rb n-ra n)/d n) atTop (nhds 0))
    (hvd : Tendsto (fun n => (vb n-va n)/d n) atTop (nhds omega))
    (hne : angle0≠psi) (hpi : |angle0-psi|<Real.pi) :
    Tendsto (fun n => (physicalSourceFullAngularField (eps n) (s n) (angle n) (rb n) (vb n)-
      physicalSourceFullAngularField (eps n) (s n) (angle n) (ra n) (va n))/d n)
      atTop (nhds (omega*Coorbital.kappa |psi-angle0|)) := by
  let F : ℝ×((ℝ×ℝ)×(ℝ×ℝ)) → ℝ := fun z =>
    physicalSourceFullAngularField z.1 z.2.1.1 z.2.1.2 z.2.2.1 z.2.2.2
  let z0 : ℝ×((ℝ×ℝ)×(ℝ×ℝ)) := (0,((1,angle0),(1,psi)))
  have hc : ContDiffAt ℝ ∞ F z0 := physicalSourceFullAngularField_joint_contDiffAt z0 (by norm_num [z0])
    (polarUnit_ne_of_angle_ne angle0 psi hne (by simpa only [abs_sub_comm] using hpi))
  have hA : Tendsto (fun n => (eps n,((s n,angle n),(ra n,va n)))) atTop (nhds z0) :=
    heps.prodMk_nhds ((hst.prodMk_nhds hangt).prodMk_nhds (hrat.prodMk_nhds hvat))
  have hB : Tendsto (fun n => (eps n,((s n,angle n),(rb n,vb n)))) atTop (nhds z0) :=
    heps.prodMk_nhds ((hst.prodMk_nhds hangt).prodMk_nhds (hrbt.prodMk_nhds hvbt))
  let U : ℝ×((ℝ×ℝ)×(ℝ×ℝ)) := (0,((0,0),(0,1)))
  have hv : Tendsto (fun n => (d n)⁻¹ •
      ((eps n,((s n,angle n),(rb n,vb n)))-(eps n,((s n,angle n),(ra n,va n)))))
      atTop (nhds (omega • U)) := by
    have ht := (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (nhds 0)).prodMk_nhds
      ((tendsto_const_nhds : Tendsto (fun _ : ℕ => ((0,0) : ℝ×ℝ)) atTop (nhds (0,0))).prodMk_nhds
        (hrd.prodMk_nhds hvd))
    simpa only [U,Prod.smul_mk,Prod.mk_sub_mk,Prod.zero_eq_mk,smul_zero,smul_eq_mul,
      sub_self,mul_zero,mul_one,div_eq_mul_inv,mul_comm] using ht
  have hp : HasDerivAt (fun v : ℝ => ((0 : ℝ),(((1 : ℝ),angle0),((1 : ℝ),v)))) U psi := by
    have h0 : HasDerivAt (fun _ : ℝ => ((1 : ℝ),angle0)) ((0,0) : ℝ×ℝ) psi :=
      hasDerivAt_const psi ((1 : ℝ),angle0)
    have h1 : HasDerivAt (fun v : ℝ => ((1 : ℝ),v)) ((0,1) : ℝ×ℝ) psi :=
      (hasDerivAt_const psi (1 : ℝ)).prodMk (hasDerivAt_id psi)
    exact (hasDerivAt_const psi (0 : ℝ)).prodMk (h0.prodMk h1)
  have hpartial : (fderiv ℝ F z0) U=Coorbital.kappa |psi-angle0| := by
    have hp' := (hc.differentiableAt (by simp)).hasFDerivAt.comp_hasDerivAt psi hp
    have heq : (fun v : ℝ => F (0,((1,angle0),(1,v))))=
        (fun v : ℝ => physicalSourceAngularField 1 angle0 1 v) := by
      funext v
      simp [F,physicalSourceFullAngularField,physicalSourceAngularField]
    simp only [Function.comp_def] at hp'
    rw [heq] at hp'
    exact hp'.unique (physicalSourceAngularField_unit_hasDerivAt angle0 psi hne hpi)
  have ht := strict_fderiv_scaled_difference_limit F (fderiv ℝ F z0) z0
    (hc.hasStrictFDerivAt (by simp)) _ _ hA hB d hd (omega • U) hv
  simpa only [F,map_smul,smul_eq_mul,hpartial] using ht

/-- The exact macro identity itself determines the cubic mass scale.
In particular no prior convergence of the total triple mass or bounded
mass-to-diameter ratio is needed in this final algebraic step. -/
theorem nested_macro_cube_tendsto (nu K J d : ℕ → ℝ) (omega D : ℝ)
    (heq : ∀ n,nu n*K n+(1-nu n)*J n=0)
    (hd : ∀ n,0<d n) (hdt : Tendsto d atTop (nhds 0)) (homega : omega≠0)
    (hK : Tendsto (fun n => d n^2*K n) atTop (nhds omega))
    (hJ : Tendsto (fun n => J n/d n) atTop (nhds (-omega*D))) :
    Tendsto (fun n => nu n/d n^3) atTop (nhds D) := by
  have hden : Tendsto (fun n => d n^2*K n-d n^3*(J n/d n)) atTop (nhds omega) := by
    convert! hK.sub ((hdt.pow 3).mul hJ) using 1
    ring
  have hquot := hJ.neg.div hden homega
  have hquot' : Tendsto (fun n => -(J n/d n)/(d n^2*K n-d n^3*(J n/d n)))
      atTop (nhds D) := by
    convert! hquot using 1
    field_simp [homega]
  apply hquot'.congr'
  filter_upwards [hden.eventually_ne homega] with n hn
  have hdn := ne_of_gt (hd n)
  apply (div_eq_iff hn).mpr
  field_simp [hdn]
  nlinarith [heq n]

/-- The real normalized macro equations force the triple cube limit from
the first-order triple geometry. This bridge has no chart-root, mass-share
limit, or mass-to-scale limit premise. -/
theorem normalized_nested_macro_mass_cube_limit_of_first_order_geometry
    (eps : ℕ → ℝ) (mu : ℕ → MassRatio) (x : ℕ → Configuration)
    (heps : ∀ n,0<eps n) (hepst : Tendsto eps atTop (nhds 0))
    (hm : ∀ n,PositiveRatio (mu n))
    (hx : ∀ n,NormalizedCentralConfiguration (masses (eps n) (mu n)) (x n))
    (r theta : ℕ → Satellite → ℝ) (hr : ∀ n i,0<r n i)
    (hpolar : ∀ n,satellitesRelative (x n)=polarSatellites (r n) (theta n))
    (hrt : ∀ i,Tendsto (fun n => r n i) atTop (nhds 1))
    (theta0 : Satellite → ℝ) (hthetat : Tendsto theta atTop (nhds theta0))
    (a b c p : Satellite) (hab : a≠b) (hcp : c≠p)
    (hc : c∈pairExteriorLabels a b) (hp : p∈pairExteriorLabels a b)
    (psi omega : ℝ) (homega : omega≠0)
    (hpa : theta0 a=psi) (hpb : theta0 b=psi) (hpc : theta0 c=psi)
    (hsep : theta0 p≠psi) (hpi : |theta0 p-psi|<Real.pi)
    (d : ℕ → ℝ) (hd : ∀ n,0<d n) (hdt : Tendsto d atTop (nhds 0))
    (hrac : Tendsto (fun n => (r n c-r n a)/d n) atTop (nhds 0))
    (hrbc : Tendsto (fun n => (r n c-r n b)/d n) atTop (nhds 0))
    (hgac : Tendsto (fun n => (theta n c-theta n a)/d n) atTop (nhds omega))
    (hgbc : Tendsto (fun n => (theta n c-theta n b)/d n) atTop (nhds omega))
    (hDac : Tendsto (fun n => satelliteDistance (satellitesRelative (x n)) a c/d n) atTop (nhds 1))
    (hDbc : Tendsto (fun n => satelliteDistance (satellitesRelative (x n)) b c/d n) atTop (nhds 1)) :
    Tendsto (fun n => (mu n a+mu n b+mu n c)/d n^3)
      atTop (nhds (Coorbital.kappa |psi-theta0 p|)) := by
  have htat (i : Satellite) : Tendsto (fun n => theta n i) atTop (nhds (theta0 i)) := by
    simpa only [Function.comp_def] using (continuous_apply i).tendsto theta0 |>.comp hthetat
  have hca : c≠a := (Finset.mem_erase.mp (Finset.mem_erase.mp hc).2).1
  have hcb : c≠b := (Finset.mem_erase.mp hc).1
  have hphysicalsep (i : Satellite) (hi : c≠i) (n : ℕ) :
      polarPoint (r n c) (theta n c)≠polarPoint (r n i) (theta n i) := by
    have hn := (satellitesRelative_collisionFree (x n) (hx n).1).2 c i hi
    rw [hpolar n] at hn
    exact hn
  have hpoint (i : Satellite) (hi : c≠i) (hpii : theta0 i=psi)
      (hgi : Tendsto (fun n => (theta n c-theta n i)/d n) atTop (nhds omega))
      (hDi : Tendsto (fun n => satelliteDistance (satellitesRelative (x n)) i c/d n) atTop (nhds 1)) :
      Tendsto (fun n => d n^2*fullAngularMatrix (eps n) (r n) (theta n) i c) atTop (nhds omega) := by
    have hgap : Tendsto (fun n => theta n c-theta n i) atTop (nhds 0) := by
      simpa only [hpc,hpii,sub_self] using (htat c).sub (htat i)
    apply physicalSourceFullAngularField_near_scaled_limit eps _ _ _ _ d omega hepst (hrt c) (hrt i)
      hd hdt hgap hgi (hphysicalsep i hi)
    simpa only [satelliteDistance,hpolar,polarSatellites] using hDi
  have hKavg := current_positive_weighted_average_tendsto (fun n => mu n a) (fun n => mu n b)
    (fun n => d n^2*fullAngularMatrix (eps n) (r n) (theta n) a c)
    (fun n => d n^2*fullAngularMatrix (eps n) (r n) (theta n) b c)
    omega (fun n => (hm n).1 a) (fun n => (hm n).1 b)
    (hpoint a hca hpa hgac hDac) (hpoint b hcb hpb hgbc hDbc)
  have hK : Tendsto (fun n => d n^2*nestedPairCurrentKernel (eps n) (mu n) (r n) (theta n) a b c)
      atTop (nhds omega) := by
    convert! hKavg using 1
    funext n
    unfold nestedPairCurrentKernel
    ring
  have hdiff (i : Satellite) (hpii : theta0 i=psi)
      (hri : Tendsto (fun n => (r n c-r n i)/d n) atTop (nhds 0))
      (hgi : Tendsto (fun n => (theta n c-theta n i)/d n) atTop (nhds omega)) :
      Tendsto (fun n => (fullAngularMatrix (eps n) (r n) (theta n) i p-
        fullAngularMatrix (eps n) (r n) (theta n) c p)/d n)
        atTop (nhds (-omega*Coorbital.kappa |psi-theta0 p|)) := by
    have hrneg : Tendsto (fun n => (r n i-r n c)/d n) atTop (nhds 0) := by
      convert hri.neg using 1
      · funext n; ring
      · ring
    have hgneg : Tendsto (fun n => (theta n i-theta n c)/d n) atTop (nhds (-omega)) := by
      convert hgi.neg using 1
      funext n; ring
    exact physicalSourceFullAngularField_moving_secant_limit eps _ _ _ _ _ _ d (theta0 p) psi (-omega)
      hepst (hrt p) (htat p) (hrt c) (hrt i)
      (by simpa only [hpc] using htat c) (by simpa only [hpii] using htat i)
      hd hrneg hgneg hsep hpi
  have hJavg := current_positive_weighted_average_tendsto (fun n => mu n a) (fun n => mu n b)
    (fun n => (fullAngularMatrix (eps n) (r n) (theta n) a p-fullAngularMatrix (eps n) (r n) (theta n) c p)/d n)
    (fun n => (fullAngularMatrix (eps n) (r n) (theta n) b p-fullAngularMatrix (eps n) (r n) (theta n) c p)/d n)
    (-omega*Coorbital.kappa |psi-theta0 p|) (fun n => (hm n).1 a) (fun n => (hm n).1 b)
    (hdiff a hpa hrac hgac) (hdiff b hpb hrbc hgbc)
  have hJ : Tendsto (fun n => (nestedPairCurrentExterior (eps n) (mu n) (r n) (theta n) a b p-
      fullAngularMatrix (eps n) (r n) (theta n) c p)/d n)
      atTop (nhds (-omega*Coorbital.kappa |psi-theta0 p|)) := by
    convert! hJavg using 1
    funext n
    have hxi := ne_of_gt (add_pos ((hm n).1 a) ((hm n).1 b))
    unfold nestedPairCurrentExterior
    field_simp [hxi,ne_of_gt (hd n)]
    ring
  exact nested_macro_cube_tendsto _ _ _ d omega (Coorbital.kappa |psi-theta0 p|)
    (fun n => normalized_nested_macro_average (eps n) (mu n) (x n) (heps n) (hm n) (hx n)
      (r n) (theta n) (hr n) (hpolar n) a b c p hab hcp hc hp)
    hd hdt homega hK hJ

end DominantFiveBody
