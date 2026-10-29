import DominantFiveBody.CollisionNestedGeometry

/-! # Physical translation and positive scale transport for Newton secants -/

noncomputable section
open scoped BigOperators ContDiff
open Filter Set Topology
namespace DominantFiveBody

theorem strict_fderiv_scaled_vector_difference_limit
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (f : E → F) (L : E →L[ℝ] F) (z : E) (hf : HasStrictFDerivAt f L z)
    (A B : ℕ → E) (hA : Tendsto A atTop (nhds z)) (hB : Tendsto B atTop (nhds z))
    (d : ℕ → ℝ) (hd : ∀ n,0<d n) (v : E)
    (hv : Tendsto (fun n => (d n)⁻¹ • (B n-A n)) atTop (nhds v)) :
    Tendsto (fun n => (d n)⁻¹ • (f (B n)-f (A n))) atTop (nhds (L v)) := by
  have hbound : Asymptotics.IsBigO atTop (fun n => B n-A n) d := by
    apply Asymptotics.IsBigO.of_bound (‖v‖+1)
    filter_upwards [hv.norm.eventually (Iio_mem_nhds (by linarith : ‖v‖<‖v‖+1))] with n hn
    have he : B n-A n=d n • ((d n)⁻¹ • (B n-A n)) := by
      rw [smul_smul,mul_inv_cancel₀ (ne_of_gt (hd n)),one_smul]
    calc
      ‖B n-A n‖=d n*‖(d n)⁻¹ • (B n-A n)‖ := by
        conv_lhs => rw [he]
        rw [norm_smul,Real.norm_eq_abs,abs_of_pos (hd n)]
      _≤(‖v‖+1)*‖d n‖ := by
        rw [Real.norm_eq_abs,abs_of_pos (hd n)]
        exact (mul_le_mul_of_nonneg_left hn.le (hd n).le).trans_eq (mul_comm _ _)
  have hrem : Tendsto (fun n => (d n)⁻¹ • (f (B n)-f (A n)-L (B n-A n))) atTop (nhds 0) := by
    have ho := hf.isLittleO.comp_tendsto (hB.prodMk_nhds hA)
    simpa only [Function.comp_def] using (ho.trans_isBigO hbound).tendsto_inv_smul_nhds_zero
  have hlin : Tendsto (fun n => (d n)⁻¹ • L (B n-A n)) atTop (nhds (L v)) := by
    simpa only [Function.comp_def,map_smul] using L.continuous.continuousAt.tendsto.comp hv
  convert! hrem.add hlin using 1
  · funext n
    module
  · rw [zero_add]

theorem polar_scaled_displacement_tendsto (ra va rb vb d : ℕ → ℝ) (psi omega : ℝ)
    (hrat : Tendsto ra atTop (nhds 1)) (hrbt : Tendsto rb atTop (nhds 1))
    (hvat : Tendsto va atTop (nhds psi)) (hvbt : Tendsto vb atTop (nhds psi))
    (hd : ∀ n,0<d n)
    (hrd : Tendsto (fun n => (rb n-ra n)/d n) atTop (nhds 0))
    (hvd : Tendsto (fun n => (vb n-va n)/d n) atTop (nhds omega)) :
    Tendsto (fun n => (d n)⁻¹ • (polarPoint (rb n) (vb n)-polarPoint (ra n) (va n)))
      atTop (nhds (omega • quarterTurn (polarPoint 1 psi))) := by
  have hc : ContDiffAt ℝ ∞ (fun z : ℝ×ℝ => polarPoint z.1 z.2) (1,psi) :=
    (polarPoint_contDiff ∞).contDiffAt
  have hstrict : HasStrictFDerivAt (fun z : ℝ×ℝ => polarPoint z.1 z.2)
      (polarPointDerivative (1,psi)) (1,psi) := by
    rw [← (polarPoint_hasFDerivAt (1,psi)).fderiv]
    exact hc.hasStrictFDerivAt (by simp)
  have hv : Tendsto (fun n => (d n)⁻¹ • ((rb n,vb n)-(ra n,va n)))
      atTop (nhds ((0,omega) : ℝ×ℝ)) := by
    simpa only [Prod.smul_mk,Prod.mk_sub_mk,smul_eq_mul,div_eq_mul_inv,mul_comm] using
      hrd.prodMk_nhds hvd
  have ht := strict_fderiv_scaled_vector_difference_limit _ (polarPointDerivative (1,psi)) (1,psi)
    hstrict _ _ (hrat.prodMk_nhds hvat) (hrbt.prodMk_nhds hvbt) d hd (0,omega) hv
  simpa only [polarPointDerivative_apply,zero_smul,zero_add] using ht

theorem quarterTurn_polarPoint_hasDerivAt_angle (rho v : ℝ) :
    HasDerivAt (fun w : ℝ => quarterTurn (polarPoint rho w)) (-polarPoint rho v) v := by
  have h := quarterTurnLinear.toContinuousLinearMap.hasFDerivAt.comp_hasDerivAt v
    (polarPoint_hasDerivAt_angle rho v)
  convert! h using 1
  ext k
  fin_cases k <;> simp [quarterTurn,point]

theorem polar_unit_tangent_scaled_difference_tendsto (va vb s : ℕ → ℝ) (psi omega : ℝ)
    (hva : Tendsto va atTop (nhds psi)) (hvb : Tendsto vb atTop (nhds psi))
    (hs : ∀ n,0<s n)
    (hgap : Tendsto (fun n => (vb n-va n)/s n) atTop (nhds omega)) :
    Tendsto (fun n => (s n)⁻¹ • (quarterTurn (polarPoint 1 (vb n))-quarterTurn (polarPoint 1 (va n))))
      atTop (nhds (omega • (-polarPoint 1 psi))) := by
  let F : ℝ → Plane := fun w => quarterTurn (polarPoint 1 w)
  have hc : ContDiff ℝ ∞ F :=
    quarterTurnLinear.toContinuousLinearMap.contDiff.comp
      ((polarPoint_contDiff ∞).comp (contDiff_const.prodMk contDiff_id))
  have hd := quarterTurn_polarPoint_hasDerivAt_angle 1 psi
  have hstrict : HasStrictFDerivAt F (ContinuousLinearMap.toSpanSingleton ℝ (-polarPoint 1 psi)) psi := by
    rw [← hd.hasFDerivAt.fderiv]
    exact hc.contDiffAt.hasStrictFDerivAt (by simp)
  have hv : Tendsto (fun n => (s n)⁻¹ • (vb n-va n)) atTop (nhds omega) := by
    simpa only [smul_eq_mul,div_eq_mul_inv,mul_comm] using hgap
  exact strict_fderiv_scaled_vector_difference_limit F _ psi hstrict va vb hva hvb s hs omega hv

theorem newtonTargetField_translate_scale (source target base : Plane) (d : ℝ) (hd : 0<d) :
    newtonTargetField (d⁻¹ • (source-base)) (d⁻¹ • (target-base))=
      d^2 • newtonTargetField source target := by
  have hgap : d⁻¹ • (source-base)-d⁻¹ • (target-base)=d⁻¹ • (source-target) := by module
  unfold newtonTargetField
  rw [hgap,norm_smul,Real.norm_eq_abs,abs_inv,abs_of_pos hd,smul_smul,smul_smul]
  congr 1
  field_simp [ne_of_gt hd]

theorem dividedNewtonTargetField_translate_scale
    (source qa qb direction : Plane) (d t : ℝ) (hd : 0<d) (ht : t≠0)
    (hsa : source≠qa) (hsb : source≠qb) (hgap : qb-qa=t • direction) :
    dividedNewtonTargetField (d⁻¹ • (source-qa)) 0 (d⁻¹ • (qb-qa)) direction=
      d^3 • dividedNewtonTargetField source qa qb direction := by
  have hscaledgap : d⁻¹ • (qb-qa)-(0 : Plane)=(t/d) • direction := by
    rw [hgap,sub_zero,smul_smul]
    congr 1
    ring
  have hscaledsa : d⁻¹ • (source-qa)≠(0 : Plane) :=
    smul_ne_zero (inv_ne_zero (ne_of_gt hd)) (sub_ne_zero.mpr hsa)
  have hscaledsb : d⁻¹ • (source-qa)≠d⁻¹ • (qb-qa) := by
    intro heq
    apply hsb
    have hsub := (smul_right_injective _ (inv_ne_zero (ne_of_gt hd))) heq
    exact sub_left_inj.mp hsub
  rw [dividedNewtonTargetField_eq _ _ _ direction (t/d) (div_ne_zero ht (ne_of_gt hd))
    hscaledsa hscaledsb hscaledgap,
    dividedNewtonTargetField_eq source qa qb direction t ht hsa hsb hgap]
  have hNqb := newtonTargetField_translate_scale source qb qa d hd
  have hNqa := newtonTargetField_translate_scale source qa qa d hd
  simp only [sub_self,smul_zero] at hNqa
  rw [hNqb,hNqa,← smul_sub,smul_smul,smul_smul]
  congr 1
  field_simp [ht,ne_of_gt hd]

end DominantFiveBody
