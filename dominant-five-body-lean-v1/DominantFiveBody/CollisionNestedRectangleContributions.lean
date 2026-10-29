import DominantFiveBody.CollisionNestedRectangleControls

/-! # Original separate near and exterior contributions on a nested rectangle -/
noncomputable section
open scoped BigOperators ContDiff
open Filter Set Topology
namespace DominantFiveBody
open Coorbital
set_option maxHeartbeats 1800000

theorem physical_nested_polar_rectangle_derivatives_individually_uniform
    (massC massP rc vc rp vp ra va rb vb d : ℕ → ℝ) (psi angle0 omega L M : ℝ)
    (hrc : Tendsto rc atTop (nhds 1)) (hrp : Tendsto rp atTop (nhds 1))
    (hra : Tendsto ra atTop (nhds 1)) (hrb : Tendsto rb atTop (nhds 1))
    (hvc : Tendsto vc atTop (nhds psi)) (hvp : Tendsto vp atTop (nhds angle0))
    (hva : Tendsto va atTop (nhds psi)) (hvb : Tendsto vb atTop (nhds psi))
    (hd : ∀ n,0<d n) (hdt : Tendsto d atTop (nhds 0)) (homega : omega^2=1)
    (hrab : Tendsto (fun n => (rb n-ra n)/d n) atTop (nhds 0))
    (hvab : Tendsto (fun n => (vb n-va n)/d n) atTop (nhds 0))
    (hrac : Tendsto (fun n => (rc n-ra n)/d n) atTop (nhds 0))
    (hvac : Tendsto (fun n => (vc n-va n)/d n) atTop (nhds omega))
    (hmc : Tendsto (fun n => massC n/d n^3) atTop (nhds L))
    (hmp : Tendsto massP atTop (nhds M)) (hne : angle0≠psi) (hpi : |angle0-psi|<Real.pi) :
    ∀ eta : ℝ,0<eta → ∀ᶠ n in atTop,∀ rho∈uIcc (ra n) (rb n),∀ v∈uIcc (va n) (vb n),
      |massC n*physicalSourceAngularRadialDerivative (rc n) (vc n) rho v|<eta ∧
      |massC n*physicalSourceAngularAngularDerivative (rc n) (vc n) rho v-2*L|<eta ∧
      |massP n*physicalSourceAngularRadialDerivative (rp n) (vp n) rho v-
        M*physicalSourceAngularRadialDerivative 1 angle0 1 psi|<eta ∧
      |massP n*physicalSourceAngularAngularDerivative (rp n) (vp n) rho v-
        (M*Coorbital.kappa |psi-angle0|)|<eta := by
  let S : ℕ → Set (ℝ×ℝ) := fun n => uIcc (ra n) (rb n) ×ˢ uIcc (va n) (vb n)
  let F : ℕ → (ℝ×ℝ) → ℝ×(ℝ×(ℝ×ℝ)) := fun n z =>
    (massC n*physicalSourceAngularRadialDerivative (rc n) (vc n) z.1 z.2,
      (massC n*physicalSourceAngularAngularDerivative (rc n) (vc n) z.1 z.2,
      (massP n*physicalSourceAngularRadialDerivative (rp n) (vp n) z.1 z.2,
       massP n*physicalSourceAngularAngularDerivative (rp n) (vp n) z.1 z.2)))
  have hseq : ∀ z : ℕ → ℝ×ℝ,(∀ n,z n∈S n) → Tendsto (fun n => F n (z n)) atTop
      (nhds (0,(2*L,(M*physicalSourceAngularRadialDerivative 1 angle0 1 psi,
        M*Coorbital.kappa |psi-angle0|)))) := by
    intro z hz
    have hzR (n : ℕ) := (hz n).1
    have hzV (n : ℕ) := (hz n).2
    have hrho := between_tendsto_common_limit ra rb (fun n => (z n).1) 1 hzR hra hrb
    have hv := between_tendsto_common_limit va vb (fun n => (z n).2) psi hzV hva hvb
    have hrTarget := between_scaled_difference_tendsto_zero ra rb (fun n => (z n).1) d hd hzR hrab
    have hvTarget := between_scaled_difference_tendsto_zero va vb (fun n => (z n).2) d hd hzV hvab
    have hrd : Tendsto (fun n => ((z n).1-rc n)/d n) atTop (nhds 0) := by
      convert! hrTarget.sub hrac using 1
      · funext n; ring
      · ring
    have hgd : Tendsto (fun n => (vc n-(z n).2)/d n) atTop (nhds omega) := by
      convert! hvac.sub hvTarget using 1
      · funext n; ring
      · ring
    have hrdRev : Tendsto (fun n => (rc n-(z n).1)/d n) atTop (nhds 0) := by
      convert! hrd.neg using 1
      · funext n; ring
      · ring
    have hdisplacement := polar_scaled_displacement_tendsto (fun n => (z n).1) (fun n => (z n).2)
      rc vc d psi omega hrho hrc hv hvc hd hrdRev hgd
    have hJnorm : ‖quarterTurn (polarPoint 1 psi)‖=1 := by
      have he : ‖quarterTurn (polarPoint 1 psi)‖^2=1 := by
        rw [← real_inner_self_eq_norm_sq,quarterTurn_inner_quarterTurn,real_inner_self_eq_norm_sq,
          polarPoint_norm,abs_one]
        norm_num
      nlinarith [norm_nonneg (quarterTurn (polarPoint 1 psi))]
    have homegaAbs : |omega|=1 := by nlinarith [sq_abs omega,abs_nonneg omega]
    have hDd : Tendsto (fun n => ‖polarPoint ((z n).1) ((z n).2)-polarPoint (rc n) (vc n)‖/d n)
        atTop (nhds 1) := by
      convert! hdisplacement.norm using 1
      · funext n
        rw [norm_smul,Real.norm_eq_abs,abs_inv,abs_of_pos (hd n),norm_sub_rev]
        ring
      · rw [norm_smul,Real.norm_eq_abs,homegaAbs,hJnorm,mul_one]
    have hnear := physical_near_angular_derivative_limits_of_scaled_geometry massC rc vc (fun n => (z n).1)
      (fun n => (z n).2) d omega L hrc hrho hd hdt homega
      (by simpa only [sub_self] using hvc.sub hv) hgd hrd hDd hmc
    have hsep := polarUnit_ne_of_angle_ne angle0 psi hne (by simpa only [abs_sub_comm] using hpi)
    have hparams := (hrp.prodMk_nhds hvp).prodMk_nhds (hrho.prodMk_nhds hv)
    have hfarR := hmp.mul ((physicalSourceAngularRadialDerivative_joint_contDiffAt ((1,angle0),(1,psi)) hsep).continuousAt.tendsto.comp hparams)
    have hfarV := hmp.mul ((physicalSourceAngularAngularDerivative_joint_contDiffAt ((1,angle0),(1,psi))
      (by norm_num) hsep).continuousAt.tendsto.comp hparams)
    have ht := hnear.1.prodMk_nhds (hnear.2.prodMk_nhds (hfarR.prodMk_nhds hfarV))
    simpa only [Function.comp_def,physicalSourceAngularAngularDerivative_unit_kappa angle0 psi hne hpi] using ht
  have huniform := limit_on_moving_sets_of_all_selections S (fun n => (ra n,va n))
    (fun _ => ⟨left_mem_uIcc,left_mem_uIcc⟩) F _ hseq
  intro eta heta
  filter_upwards [huniform eta heta] with n hn
  intro rho hr v hv
  have ht := hn (rho,v) ⟨hr,hv⟩
  simpa only [F,Prod.dist_eq,Real.dist_eq,max_lt_iff,sub_zero] using ht


theorem normalized_complete_lower_triple_nested_rectangle_individual_limits
    (eps : ℕ → ℝ) (mu : ℕ → MassRatio) (x : ℕ → Configuration)
    (heps : ∀ n,0<eps n) (hepst : Tendsto eps atTop (𝓝 0))
    (hm : ∀ n,PositiveRatio (mu n))
    (hx : ∀ n,NormalizedCentralConfiguration (masses (eps n) (mu n)) (x n))
    (hconv : ∀ n,StrictConvexInOrder standardHullOrder (x n))
    (r theta : ℕ → Satellite → ℝ) (hr : ∀ n i,0<r n i)
    (hpolar : ∀ n,satellitesRelative (x n)=polarSatellites (r n) (theta n))
    (horder : ∀ n,OrderedSemicircle (theta n))
    (muLimit : MassRatio) (hmt : Tendsto mu atTop (𝓝 muLimit))
    (qLimit : SatelliteConfiguration)
    (hqt : Tendsto (fun n => satellitesRelative (x n)) atTop (𝓝 qLimit))
    (theta0 : Satellite → ℝ) (htt : Tendsto theta atTop (𝓝 theta0))
    (center : Plane) (htriple : CompleteLimitingSatelliteTriple qLimit 3 center)
    (a b c : TripleLabel) (hab : a<b) (hca : c≠a) (hcb : c≠b)
    (hpair : Tendsto (fun n => satelliteDistance (satellitesRelative (x n)) a.castSucc b.castSucc/
      tripleLowDiameter (satellitesRelative (x n))) atTop (𝓝 0)) :
    ∀ eta : ℝ,0<eta → ∀ᶠ n in atTop,
      ∀ rho∈uIcc (r n a.castSucc) (r n b.castSucc),∀ v∈uIcc (theta n a.castSucc) (theta n b.castSucc),
      |mu n c.castSucc*physicalSourceAngularRadialDerivative (r n c.castSucc) (theta n c.castSucc) rho v|<eta ∧
      |mu n c.castSucc*physicalSourceAngularAngularDerivative (r n c.castSucc) (theta n c.castSucc) rho v-
        2*mu n c.castSucc/tripleLowDiameter (satellitesRelative (x n))^3|<eta ∧
      |mu n 3*physicalSourceAngularRadialDerivative (r n 3) (theta n 3) rho v+3*Real.sqrt 3/4|<eta ∧
      |mu n 3*physicalSourceAngularAngularDerivative (r n 3) (theta n 3) rho v-(9/4 : ℝ)|<eta := by
  have hfull := normalized_complete_lower_triple_nested_precise_scales eps mu x heps hepst hm hx
    hconv r theta hr hpolar horder muLimit hmt qLimit hqt theta0 htt center htriple a b c hab hca hcb hpair
  have hdir := normalized_complete_lower_triple_nested_directions eps mu x heps hepst hm hx
    hconv r theta hr hpolar horder muLimit hmt qLimit hqt theta0 htt center htriple a b c hab hca hcb hpair
  have hrad := normalized_complete_lower_triple_nested_radial_limits eps mu x heps hepst hm hx
    hconv r theta hr hpolar horder muLimit hmt qLimit hqt theta0 htt center htriple a b c hab.ne hca hcb hpair
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
  have hgapAbs := (normalized_complete_triple_limiting_exterior eps mu x heps hepst hm hx
    r theta hr hpolar horder muLimit hmt qLimit hqt theta0 htt 3 center htriple).2 0 (by decide)
  have hgapEq : theta0 3-theta0 0=h := by
    rw [abs_of_nonneg (sub_nonneg.mpr (hmono (by decide : (0 : Satellite)≤3)))] at hgapAbs
    exact hgapAbs
  have hne : theta0 3≠theta0 0 := by
    intro he
    rw [he,sub_self] at hgapEq
    have hh : 0<h := by unfold h; positivity
    linarith
  have hpi : |theta0 3-theta0 0|<Real.pi := by rw [hgapAbs]; unfold h; linarith [Real.pi_pos]
  have hmp := (normalized_complete_lower_triple_mass_vanishes eps mu x heps hepst hm hx
    hconv r theta hr hpolar horder muLimit hmt qLimit hqt theta0 htt center htriple).2
  have hq0 : qLimit 0=center := (htriple 0).mpr (by decide)
  have hdt := tripleLowDiameter_tendsto_zero _ qLimit hqt
    (((htriple 1).mpr (by decide)).trans hq0.symm)
    (((htriple 2).mpr (by decide)).trans hq0.symm)
  have homega : (lowNestedOrientation a c)^2=1 := by
    unfold lowNestedOrientation
    split_ifs <;> norm_num
  have ht := physical_nested_polar_rectangle_derivatives_individually_uniform
    (fun n => mu n c.castSucc) (fun n => mu n 3)
    (fun n => r n c.castSucc) (fun n => theta n c.castSucc) (fun n => r n 3) (fun n => theta n 3)
    (fun n => r n a.castSucc) (fun n => theta n a.castSucc) (fun n => r n b.castSucc) (fun n => theta n b.castSucc)
    (fun n => tripleLowDiameter (satellitesRelative (x n))) (theta0 0) (theta0 3) (lowNestedOrientation a c)
    (9/4) 1 (hrat c.castSucc) (hrat 3) (hrat a.castSucc) (hrat b.castSucc) (htat c) htp (htat a) (htat b)
    (fun n => tripleLowDiameter_pos _ (satellitesRelative_collisionFree _ (hx n).1)) hdt homega
    (hrad a b) hdir.2.1 (hrad a c) (hdir.2.2.1 a (by simp)) hfull.2.2.2.2.2.1 hmp hne hpi
  have habs : |theta0 0-theta0 3|=h := by rw [abs_sub_comm]; exact hgapAbs
  have hU : ∀ eta : ℝ,0<eta → ∀ᶠ n in atTop,
      ∀ rho∈uIcc (r n a.castSucc) (r n b.castSucc),∀ v∈uIcc (theta n a.castSucc) (theta n b.castSucc),
      |mu n c.castSucc*physicalSourceAngularRadialDerivative (r n c.castSucc) (theta n c.castSucc) rho v|<eta ∧
      |mu n c.castSucc*physicalSourceAngularAngularDerivative (r n c.castSucc) (theta n c.castSucc) rho v-(9/2 : ℝ)|<eta ∧
      |mu n 3*physicalSourceAngularRadialDerivative (r n 3) (theta n 3) rho v+3*Real.sqrt 3/4|<eta ∧
      |mu n 3*physicalSourceAngularAngularDerivative (r n 3) (theta n 3) rho v-(9/4 : ℝ)|<eta := by
    simpa only [physicalSourceAngularRadialDerivative_unit_h _ _ hgapEq,habs,kappa_h,one_mul,
      show -3*Real.sqrt 3/4= -(3*Real.sqrt 3/4) by ring,sub_neg_eq_add,
      show (2 : ℝ)*(9/4)=9/2 by norm_num] using ht
  have hcenter : Tendsto (fun n => 2*mu n c.castSucc/
      tripleLowDiameter (satellitesRelative (x n))^3) atTop (nhds (9/2 : ℝ)) := by
    convert! hfull.2.2.2.2.2.1.const_mul 2 using 1
    · funext n;ring
    · norm_num
  intro eta heta
  filter_upwards [hU (eta/2) (by positivity),
    hcenter.eventually (Metric.ball_mem_nhds (9/2 : ℝ) (by positivity : 0<eta/2))] with n hn hc
  intro rho hrho v hv
  have hb := hn rho hrho v hv
  have hc' : |(9/2 : ℝ)-2*mu n c.castSucc/tripleLowDiameter (satellitesRelative (x n))^3|<eta/2 := by
    simpa only [Real.dist_eq,abs_sub_comm] using hc
  refine ⟨by linarith [hb.1],?_,by linarith [hb.2.2.1],by linarith [hb.2.2.2]⟩
  have htri := abs_add_le
    (mu n c.castSucc*physicalSourceAngularAngularDerivative (r n c.castSucc) (theta n c.castSucc) rho v-9/2)
    (9/2-2*mu n c.castSucc/tripleLowDiameter (satellitesRelative (x n))^3)
  rw [show mu n c.castSucc*physicalSourceAngularAngularDerivative (r n c.castSucc) (theta n c.castSucc) rho v-9/2+
      (9/2-2*mu n c.castSucc/tripleLowDiameter (satellitesRelative (x n))^3)=
      mu n c.castSucc*physicalSourceAngularAngularDerivative (r n c.castSucc) (theta n c.castSucc) rho v-
        2*mu n c.castSucc/tripleLowDiameter (satellitesRelative (x n))^3 by ring] at htri
  linarith [hb.2.1]

end DominantFiveBody
