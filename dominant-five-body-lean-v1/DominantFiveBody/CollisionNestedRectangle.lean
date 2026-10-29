import DominantFiveBody.CollisionTripleNestedComplete

/-! # Uniform physical angular derivatives on the moving smaller-pair polar rectangle -/

noncomputable section
open scoped BigOperators ContDiff
open Filter Set Topology
namespace DominantFiveBody
set_option maxHeartbeats 1800000

theorem limit_on_moving_sets_of_all_selections
    {E F : Type*} [PseudoMetricSpace F] (S : ℕ → Set E) (x : ℕ → E)
    (hx : ∀ n,x n∈S n) (F0 : ℕ → E → F) (y : F)
    (hseq : ∀ z : ℕ → E,(∀ n,z n∈S n) → Tendsto (fun n => F0 n (z n)) atTop (nhds y)) :
    ∀ eta : ℝ,0<eta → ∀ᶠ n in atTop,∀ z∈S n,dist (F0 n z) y<eta := by
  classical
  intro eta heta
  have hz : ∀ n,∃ z,z∈S n ∧
      ((∃ w∈S n,eta≤dist (F0 n w) y) → eta≤dist (F0 n z) y) := by
    intro n
    by_cases hbad : ∃ w∈S n,eta≤dist (F0 n w) y
    · obtain ⟨z,hz,hfail⟩ := hbad
      exact ⟨z,hz,fun _ => hfail⟩
    · exact ⟨x n,hx n,fun h => (hbad h).elim⟩
  choose z hz using hz
  have ht := hseq z (fun n => (hz n).1)
  filter_upwards [ht.eventually (Metric.ball_mem_nhds y heta)] with n hn
  intro w hw
  by_contra hfail
  have hbad : eta≤dist (F0 n (z n)) y := (hz n).2 ⟨w,hw,le_of_not_gt hfail⟩
  exact (not_lt_of_ge hbad) hn

theorem between_scaled_difference_tendsto_zero (A B Z d : ℕ → ℝ)
    (hd : ∀ n,0<d n) (hZ : ∀ n,Z n∈uIcc (A n) (B n))
    (hAB : Tendsto (fun n => (B n-A n)/d n) atTop (nhds 0)) :
    Tendsto (fun n => (Z n-A n)/d n) atTop (nhds 0) := by
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  have hABnorm : Tendsto (fun n => ‖(B n-A n)/d n‖) atTop (nhds 0) := by
    simpa only [norm_zero] using hAB.norm
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hABnorm
  · exact Eventually.of_forall (fun n => norm_nonneg _)
  · exact Eventually.of_forall (fun n => by
      simp only [Real.norm_eq_abs,abs_div,abs_of_pos (hd n)]
      exact (div_le_div_iff_of_pos_right (hd n)).mpr (abs_sub_left_of_mem_uIcc (hZ n)))

theorem between_tendsto_common_limit (A B Z : ℕ → ℝ) (L : ℝ)
    (hZ : ∀ n,Z n∈uIcc (A n) (B n)) (hA : Tendsto A atTop (nhds L)) (hB : Tendsto B atTop (nhds L)) :
    Tendsto Z atTop (nhds L) := by
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le'
    (by simpa only [min_self] using hA.min hB) (by simpa only [max_self] using hA.max hB)
  · exact Eventually.of_forall (fun n => (hZ n).1)
  · exact Eventually.of_forall (fun n => (hZ n).2)

theorem physical_near_angular_derivative_limits_of_scaled_geometry
    (mass rc angle rho v d : ℕ → ℝ) (omega L : ℝ)
    (hrc : Tendsto rc atTop (nhds 1)) (hrho : Tendsto rho atTop (nhds 1))
    (hd : ∀ n,0<d n) (hdt : Tendsto d atTop (nhds 0)) (homega : omega^2=1)
    (hgap : Tendsto (fun n => angle n-v n) atTop (nhds 0))
    (hgd : Tendsto (fun n => (angle n-v n)/d n) atTop (nhds omega))
    (hrd : Tendsto (fun n => (rho n-rc n)/d n) atTop (nhds 0))
    (hDd : Tendsto (fun n => ‖polarPoint (rho n) (v n)-polarPoint (rc n) (angle n)‖/d n)
      atTop (nhds 1))
    (hmd : Tendsto (fun n => mass n/d n^3) atTop (nhds L)) :
    Tendsto (fun n => mass n*physicalSourceAngularRadialDerivative (rc n) (angle n) (rho n) (v n))
      atTop (nhds 0) ∧
    Tendsto (fun n => mass n*physicalSourceAngularAngularDerivative (rc n) (angle n) (rho n) (v n))
      atTop (nhds (2*L)) := by
  have hsep : ∀ᶠ n in atTop,polarPoint (rc n) (angle n)≠polarPoint (rho n) (v n) := by
    filter_upwards [hDd.eventually (Ioi_mem_nhds (by norm_num : (1/2 : ℝ)<1))] with n hn
    have hp : 0<‖polarPoint (rho n) (v n)-polarPoint (rc n) (angle n)‖ :=
      (div_pos_iff_of_pos_right (hd n)).mp (lt_trans (by norm_num) hn)
    exact (sub_ne_zero.mp (norm_pos_iff.mp hp)).symm
  obtain ⟨N,hN⟩ := eventually_atTop.mp hsep
  have hshift := tendsto_add_atTop_nat N
  have hsepN (n : ℕ) : polarPoint (rc (n+N)) (angle (n+N))≠polarPoint (rho (n+N)) (v (n+N)) :=
    hN (n+N) (by omega)
  constructor
  · apply (tendsto_add_atTop_iff_nat N).mp
    exact physicalSourceAngularRadialDerivative_near_weighted_limit
      (fun n => mass (n+N)) (fun n => rc (n+N)) (fun n => angle (n+N))
      (fun n => rho (n+N)) (fun n => v (n+N)) (fun n => d (n+N)) omega L
      (hrc.comp hshift) (fun n => hd (n+N)) (hgap.comp hshift) (hgd.comp hshift)
      (hrd.comp hshift) hsepN (hDd.comp hshift) (hmd.comp hshift)
  · apply (tendsto_add_atTop_iff_nat N).mp
    exact physicalSourceAngularAngularDerivative_near_weighted_limit
      (fun n => mass (n+N)) (fun n => rc (n+N)) (fun n => angle (n+N))
      (fun n => rho (n+N)) (fun n => v (n+N)) (fun n => d (n+N)) omega L
      (hrc.comp hshift) (hrho.comp hshift) (fun n => hd (n+N)) (hdt.comp hshift) homega
      (hgap.comp hshift) (hgd.comp hshift) hsepN (hDd.comp hshift) (hmd.comp hshift)

theorem physicalSourceAngularAngularDerivative_unit_kappa (angle psi : ℝ)
    (hne : angle≠psi) (hpi : |angle-psi|<Real.pi) :
    physicalSourceAngularAngularDerivative 1 angle 1 psi=Coorbital.kappa |psi-angle| := by
  exact (physicalSourceAngularField_hasDerivAt_angle 1 angle 1 psi (by norm_num)
    (polarUnit_ne_of_angle_ne angle psi hne (by simpa only [abs_sub_comm] using hpi))).unique
      (physicalSourceAngularField_unit_hasDerivAt angle psi hne hpi)

theorem physical_nested_polar_rectangle_derivatives_uniform
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
      |massC n*physicalSourceAngularRadialDerivative (rc n) (vc n) rho v+
        massP n*physicalSourceAngularRadialDerivative (rp n) (vp n) rho v-
        M*physicalSourceAngularRadialDerivative 1 angle0 1 psi|<eta ∧
      |massC n*physicalSourceAngularAngularDerivative (rc n) (vc n) rho v+
        massP n*physicalSourceAngularAngularDerivative (rp n) (vp n) rho v-
        (2*L+M*Coorbital.kappa |psi-angle0|)|<eta := by
  let S : ℕ → Set (ℝ×ℝ) := fun n => uIcc (ra n) (rb n) ×ˢ uIcc (va n) (vb n)
  let F : ℕ → (ℝ×ℝ) → ℝ×ℝ := fun n z =>
    (massC n*physicalSourceAngularRadialDerivative (rc n) (vc n) z.1 z.2+
      massP n*physicalSourceAngularRadialDerivative (rp n) (vp n) z.1 z.2,
      massC n*physicalSourceAngularAngularDerivative (rc n) (vc n) z.1 z.2+
      massP n*physicalSourceAngularAngularDerivative (rp n) (vp n) z.1 z.2)
  have hseq : ∀ z : ℕ → ℝ×ℝ,(∀ n,z n∈S n) → Tendsto (fun n => F n (z n)) atTop
      (nhds (M*physicalSourceAngularRadialDerivative 1 angle0 1 psi,2*L+M*Coorbital.kappa |psi-angle0|)) := by
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
    have ht := (hnear.1.add hfarR).prodMk_nhds (hnear.2.add hfarV)
    simpa only [Function.comp_def,zero_add,physicalSourceAngularAngularDerivative_unit_kappa angle0 psi hne hpi] using ht
  have huniform := limit_on_moving_sets_of_all_selections S (fun n => (ra n,va n))
    (fun _ => ⟨left_mem_uIcc,left_mem_uIcc⟩) F _ hseq
  intro eta heta
  filter_upwards [huniform eta heta] with n hn
  intro rho hr v hv
  have ht := hn (rho,v) ⟨hr,hv⟩
  simpa only [F,Prod.dist_eq,Real.dist_eq,max_lt_iff] using ht

end DominantFiveBody
