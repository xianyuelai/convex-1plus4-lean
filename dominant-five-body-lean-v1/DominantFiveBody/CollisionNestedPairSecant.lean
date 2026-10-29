import DominantFiveBody.NewtonScaleTransport

/-! # Real smaller-pair secants with a nearby third source -/

noncomputable section
open scoped BigOperators ContDiff
open Filter Set Topology
namespace DominantFiveBody

theorem physical_pair_direction_alternative_of_exterior_vanishes
    (eps : ℕ → ℝ) (mu : ℕ → MassRatio) (q : ℕ → SatelliteConfiguration)
    (a b : Satellite) (hab : a≠b) (hcf : ∀ n,RelativeCollisionFree (q n))
    (hroot : ∀ n i,vectorResidual (eps n) (mu n) (q n) i=0)
    (c v : Plane) (hc : ‖c‖=1)
    (hqa : Tendsto (fun n => q n a) atTop (nhds c))
    (hqb : Tendsto (fun n => q n b) atTop (nhds c))
    (hv : Tendsto (fun n => physicalPairDirection (q n) a b) atTop (nhds v))
    (hP : Tendsto (fun n => eps n • pairSecantExteriorField (mu n) (q n) a b
      (physicalPairDirection (q n) a b)) atTop (nhds 0)) :
    (Tendsto (fun n => eps n*(mu n a+mu n b)/satelliteDistance (q n) a b^3)
        atTop (nhds 0) ∧ inner ℝ v c=0) ∨
      (Tendsto (fun n => eps n*(mu n a+mu n b)/satelliteDistance (q n) a b^3)
        atTop (nhds 3) ∧ (v=c ∨ v= -c)) := by
  let u : ℕ → Plane := fun n => physicalPairDirection (q n) a b
  let lambda : ℕ → ℝ := fun n => eps n*(mu n a+mu n b)/satelliteDistance (q n) a b^3
  have hv' : Tendsto u atTop (nhds v) := hv
  have hc0 : c≠0 := by intro heq; simp [heq] at hc
  have hnv (n : ℕ) : ‖u n‖=1 := physicalPairDirection_norm (q n) a b ((hcf n).2 a b hab)
  have hDt : Tendsto (fun n => dividedNewtonTargetField 0 (q n a) (q n b) (u n)) atTop
      (nhds (dividedNewtonTargetField 0 c c v)) := by
    have hd := (dividedNewtonTargetField_joint_contDiffAt ∞ ((0,c),(c,v)) hc0.symm hc0.symm).continuousAt.tendsto
    simpa only [Function.comp_def] using hd.comp
      ((tendsto_const_nhds.prodMk_nhds hqa).prodMk_nhds (hqb.prodMk_nhds hv))
  let lhs : ℕ → Plane := fun n => u n+dividedNewtonTargetField 0 (q n a) (q n b) (u n)+
    eps n • pairSecantExteriorField (mu n) (q n) a b (u n)
  have hrow (n : ℕ) : lhs n=lambda n • u n :=
    physical_pair_direction_equation (eps n) (mu n) (q n) a b (hcf n) hab (hroot n)
  have hlt : Tendsto lhs atTop (nhds ((3*inner ℝ v c) • c)) := by
    simpa only [lhs,add_zero,dividedNewtonTargetField_unit_diagonal c v hc] using
      (hv.add hDt).add hP
  have hli (n : ℕ) : inner ℝ (lhs n) (u n)=lambda n := by
    rw [hrow,real_inner_smul_left,real_inner_self_eq_norm_sq,hnv]
    ring
  have hlat : Tendsto lambda atTop (nhds (3*(inner ℝ v c)^2)) := by
    simpa only [hli,real_inner_smul_left,real_inner_comm c v,pow_two,mul_assoc] using
      hlt.inner (𝕜 := ℝ) hv'
  have heigen : (3*inner ℝ v c) • c=(3*(inner ℝ v c)^2) • v := by
    have heq : lhs=(fun n => lambda n • u n) := funext hrow
    exact tendsto_nhds_unique hlt (by rw [heq]; exact hlat.smul hv')
  by_cases hvc : inner ℝ v c=0
  · exact Or.inl ⟨by simpa only [hvc,pow_two,mul_zero] using hlat,hvc⟩
  · have hi := congrArg (fun z : Plane => inner ℝ z c) heigen
    simp only [real_inner_smul_left,real_inner_self_eq_norm_sq,hc,one_pow,mul_one] at hi
    have hprod : (3*(inner ℝ v c)^2-3)*inner ℝ v c=0 := by nlinarith [hi]
    have hl : 3*(inner ℝ v c)^2=3 := by
      have hz := (mul_eq_zero.mp hprod).resolve_right hvc
      linarith
    have hvdir : v=(inner ℝ v c) • c := by
      rw [hl] at heigen
      have hi' := congrArg (fun z : Plane => (1/3 : ℝ) • z) heigen
      simpa [smul_smul,← mul_assoc] using hi'.symm
    have hsign : inner ℝ v c=1 ∨ inner ℝ v c= -1 := by
      have hs : (inner ℝ v c-1)*(inner ℝ v c+1)=0 := by nlinarith [hl]
      rcases mul_eq_zero.mp hs with hs|hs
      · exact Or.inl (by linarith)
      · exact Or.inr (by linarith)
    refine Or.inr ⟨by simpa only [hl] using hlat,?_⟩
    rcases hsign with hs|hs
    · exact Or.inl (by simpa only [hs,one_smul] using hvdir)
    · exact Or.inr (by simpa only [hs,neg_one_smul] using hvdir)

theorem physical_pair_weighted_near_secant_limit
    (mass d : ℕ → ℝ) (q : ℕ → SatelliteConfiguration) (a b c : Satellite)
    (hab : a≠b) (hca : c≠a) (hcb : c≠b) (hcf : ∀ n,RelativeCollisionFree (q n))
    (hd : ∀ n,0<d n) (U v : Plane) (hU : ‖U‖=1) (L : ℝ)
    (hsource : Tendsto (fun n => (d n)⁻¹ • (q n c-q n a)) atTop (nhds U))
    (hsmall : Tendsto (fun n => satelliteDistance (q n) a b/d n) atTop (nhds 0))
    (hv : Tendsto (fun n => physicalPairDirection (q n) a b) atTop (nhds v))
    (hmd : Tendsto (fun n => mass n/d n^3) atTop (nhds L)) :
    Tendsto (fun n => mass n • dividedNewtonTargetField (q n c) (q n a) (q n b)
      (physicalPairDirection (q n) a b)) atTop (nhds (L • dividedNewtonTargetField U 0 0 v)) := by
  have hU0 : U≠0 := by intro heq; simp [heq] at hU
  have hqb : Tendsto (fun n => (d n)⁻¹ • (q n b-q n a)) atTop (nhds 0) := by
    convert! hsmall.smul hv using 1
    · funext n
      rw [physicalPairDirection_gap (q n) a b ((hcf n).2 a b hab)]
      simp only [smul_smul,div_eq_mul_inv,mul_comm]
    · rw [zero_smul]
  have hc := (dividedNewtonTargetField_joint_contDiffAt ∞ ((U,0),(0,v)) hU0 hU0).continuousAt.tendsto
  have hscaled := hc.comp ((hsource.prodMk_nhds tendsto_const_nhds).prodMk_nhds (hqb.prodMk_nhds hv))
  have ht := hmd.smul hscaled
  convert! ht using 1
  funext n
  simp only [Function.comp_def]
  rw [dividedNewtonTargetField_translate_scale (q n c) (q n a) (q n b) _ (d n)
    (satelliteDistance (q n) a b) (hd n)
    (norm_ne_zero_iff.mpr (sub_ne_zero.mpr ((hcf n).2 a b hab)))
    ((hcf n).2 c a hca) ((hcf n).2 c b hcb)
    (physicalPairDirection_gap (q n) a b ((hcf n).2 a b hab)),smul_smul]
  congr 1
  field_simp [ne_of_gt (hd n)]

theorem physical_pair_weighted_near_field_tendsto_zero
    (mass d : ℕ → ℝ) (q : ℕ → SatelliteConfiguration) (a c : Satellite)
    (hd : ∀ n,0<d n) (hdt : Tendsto d atTop (nhds 0)) (U : Plane) (hU : ‖U‖=1) (L : ℝ)
    (hsource : Tendsto (fun n => (d n)⁻¹ • (q n c-q n a)) atTop (nhds U))
    (hmd : Tendsto (fun n => mass n/d n^3) atTop (nhds L)) :
    Tendsto (fun n => mass n • newtonTargetField (q n c) (q n a)) atTop (nhds 0) := by
  have hU0 : U≠0 := by intro heq; simp [heq] at hU
  have hc := (physicalNewtonTargetField_joint_contDiffAt U 0 hU0).continuousAt.tendsto
  have hN := hc.comp (hsource.prodMk_nhds tendsto_const_nhds)
  have hmass := hmd.mul hdt
  have ht := hmass.smul hN
  convert! ht using 1
  · funext n
    simp only [Function.comp_def]
    have hscale := newtonTargetField_translate_scale (q n c) (q n a) (q n a) (d n) (hd n)
    simp only [sub_self,smul_zero] at hscale
    rw [hscale,smul_smul]
    congr 1
    field_simp [ne_of_gt (hd n)]
  · simp

/-- The true Cartesian near-source H secant, projected on moving polar
tangent bases, has its scaled Newton derivative limit. The extra change
of tangent basis is multiplied by a physical weighted field tending to
zero, so no unproved remainder or source convergence rate is inserted. -/
theorem physical_pair_near_cartesian_angular_secant_limit
    (mass d : ℕ → ℝ) (q : ℕ → SatelliteConfiguration) (a b c : Satellite)
    (hab : a≠b) (hca : c≠a) (hcb : c≠b) (hcf : ∀ n,RelativeCollisionFree (q n))
    (hd : ∀ n,0<d n) (hdt : Tendsto d atTop (nhds 0)) (U v c0 : Plane)
    (hU : ‖U‖=1) (hc0 : ‖c0‖=1) (L : ℝ)
    (hqc : Tendsto (fun n => q n c) atTop (nhds c0))
    (hsource : Tendsto (fun n => (d n)⁻¹ • (q n c-q n a)) atTop (nhds U))
    (hsmall : Tendsto (fun n => satelliteDistance (q n) a b/d n) atTop (nhds 0))
    (hv : Tendsto (fun n => physicalPairDirection (q n) a b) atTop (nhds v))
    (hmd : Tendsto (fun n => mass n/d n^3) atTop (nhds L))
    (Ja Jb : ℕ → Plane) (J W : Plane)
    (hJb : Tendsto Jb atTop (nhds J))
    (hJdiff : Tendsto (fun n => (satelliteDistance (q n) a b)⁻¹ • (Jb n-Ja n)) atTop (nhds W)) :
    Tendsto (fun n => mass n*(
      inner ℝ (newtonTargetField (q n c) (q n b)-newtonTargetField (q n c) 0) (Jb n)-
      inner ℝ (newtonTargetField (q n c) (q n a)-newtonTargetField (q n c) 0) (Ja n))/
      satelliteDistance (q n) a b) atTop
      (nhds (inner ℝ (L • dividedNewtonTargetField U 0 0 v) J)) := by
  have hc00 : c0≠0 := by intro heq; simp [heq] at hc0
  have hnear := physical_pair_weighted_near_secant_limit mass d q a b c hab hca hcb hcf hd U v hU L
    hsource hsmall hv hmd
  have hfield := physical_pair_weighted_near_field_tendsto_zero mass d q a c hd hdt U hU L hsource hmd
  have hmass0 : Tendsto mass atTop (nhds 0) := by
    convert! hmd.mul (hdt.pow 3) using 1
    · funext n
      field_simp [ne_of_gt (hd n)]
    · ring
  have hsourcefield := ((physicalNewtonTargetField_joint_contDiffAt c0 0 hc00).continuousAt.tendsto).comp
    (hqc.prodMk_nhds tendsto_const_nhds)
  have hsourcezero : Tendsto (fun n => mass n • newtonTargetField (q n c) 0) atTop (nhds 0) := by
    simpa only [Function.comp_def,zero_smul] using hmass0.smul hsourcefield
  have hFN : Tendsto (fun n => mass n • (newtonTargetField (q n c) (q n a)-newtonTargetField (q n c) 0))
      atTop (nhds 0) := by
    simpa only [smul_sub,sub_self] using hfield.sub hsourcezero
  have ht := (hnear.inner (𝕜 := ℝ) hJb).add (hFN.inner (𝕜 := ℝ) hJdiff)
  convert! ht using 1
  · funext n
    have hsn := norm_ne_zero_iff.mpr (sub_ne_zero.mpr ((hcf n).2 a b hab))
    rw [dividedNewtonTargetField_eq (q n c) (q n a) (q n b) _ (satelliteDistance (q n) a b)
      hsn ((hcf n).2 c a hca) ((hcf n).2 c b hcb)
      (physicalPairDirection_gap (q n) a b ((hcf n).2 a b hab))]
    simp only [inner_sub_left,inner_sub_right,real_inner_smul_left,real_inner_smul_right]
    field_simp [hsn]
    ring
  · simp

theorem tangential_unit_source_angular_newton_eigenvalue (U v : Plane) (psi : ℝ)
    (hU : ‖U‖=1) (hUr : inner ℝ U (polarPoint 1 psi)=0) :
    inner ℝ (dividedNewtonTargetField U 0 0 v) (quarterTurn (polarPoint 1 psi))=
      2*inner ℝ v (quarterTurn (polarPoint 1 psi)) := by
  let J : Plane := quarterTurn (polarPoint 1 psi)
  have hJ : inner ℝ J J=1 := by
    rw [quarterTurn_inner_quarterTurn,polarPoint_inner_radial]
    simp
  have hdecomp := polarOrthonormal_decomposition psi U
  rw [hUr,zero_smul,zero_add] at hdecomp
  change U=inner ℝ U J • J at hdecomp
  have hUI : inner ℝ U U=1 := by rw [real_inner_self_eq_norm_sq,hU]; norm_num
  have hcoef : (inner ℝ U J)^2=1 := by
    have hh := congrArg (fun z : Plane => inner ℝ z z) hdecomp
    rw [hUI,real_inner_smul_left,real_inner_smul_right,hJ,mul_one] at hh
    nlinarith
  have hU0 : U≠0 := by intro heq; simp [heq] at hU
  rw [dividedNewtonTargetField_diagonal U 0 v hU0,
    (newtonTargetField_hasFDerivAt U 0 hU0).fderiv,newtonTargetDerivative_apply]
  change inner ℝ ((3/‖U-0‖^5*inner ℝ (U-0) v) • (U-0)-(‖U-0‖^3)⁻¹ • v) J=2*inner ℝ v J
  simp only [sub_zero,hU,one_pow,div_one,inv_one,one_smul,inner_sub_left,real_inner_smul_left]
  have huv : inner ℝ U v=inner ℝ U J*inner ℝ v J := by
    conv_lhs => rw [hdecomp]
    rw [real_inner_smul_left,real_inner_comm J v]
  rw [huv]
  rw [show 3*(inner ℝ U J*inner ℝ v J)*inner ℝ U J-inner ℝ v J=
    (3*(inner ℝ U J)^2-1)*inner ℝ v J by ring,hcoef]
  ring

theorem physical_pair_near_angular_secant_limit
    (mass d : ℕ → ℝ) (r theta : ℕ → Satellite → ℝ) (a b c : Satellite)
    (hab : a≠b) (hca : c≠a) (hcb : c≠b)
    (hcf : ∀ n,RelativeCollisionFree (polarSatellites (r n) (theta n)))
    (hrc : ∀ n,0<r n c) (hrb : ∀ n,0<r n b)
    (hrct : Tendsto (fun n => r n c) atTop (nhds 1))
    (hrbt : Tendsto (fun n => r n b) atTop (nhds 1))
    (psi : ℝ) (htha : Tendsto (fun n => theta n a) atTop (nhds psi))
    (hthb : Tendsto (fun n => theta n b) atTop (nhds psi))
    (hthc : Tendsto (fun n => theta n c) atTop (nhds psi))
    (hd : ∀ n,0<d n) (hdt : Tendsto d atTop (nhds 0)) (U v : Plane)
    (hU : ‖U‖=1) (hUr : inner ℝ U (polarPoint 1 psi)=0) (L : ℝ)
    (hsource : Tendsto (fun n => (d n)⁻¹ •
      (polarPoint (r n c) (theta n c)-polarPoint (r n a) (theta n a))) atTop (nhds U))
    (hsmall : Tendsto (fun n => satelliteDistance (polarSatellites (r n) (theta n)) a b/d n) atTop (nhds 0))
    (hv : Tendsto (fun n => physicalPairDirection (polarSatellites (r n) (theta n)) a b) atTop (nhds v))
    (hmd : Tendsto (fun n => mass n/d n^3) atTop (nhds L)) :
    Tendsto (fun n => mass n*(physicalSourceAngularField (r n c) (theta n c) (r n b) (theta n b)-
      physicalSourceAngularField (r n c) (theta n c) (r n a) (theta n a))/
      satelliteDistance (polarSatellites (r n) (theta n)) a b) atTop
      (nhds (2*L*inner ℝ v (quarterTurn (polarPoint 1 psi)))) := by
  let q : ℕ → SatelliteConfiguration := fun n => polarSatellites (r n) (theta n)
  have hs (n : ℕ) : 0<satelliteDistance (q n) a b :=
    norm_pos_iff.mpr (sub_ne_zero.mpr ((hcf n).2 a b hab))
  have hqc : Tendsto (fun n => q n c) atTop (nhds (polarPoint 1 psi)) :=
    ((polarPoint_contDiff ∞).continuous.tendsto (1,psi)).comp (hrct.prodMk_nhds hthc)
  have hgap := (physical_pair_direction_polar_ratio_limits r theta a b psi hrb hs hrbt htha hthb v hv).1
  have hJdiff := polar_unit_tangent_scaled_difference_tendsto _ _ (fun n => satelliteDistance (q n) a b)
    psi (inner ℝ v (quarterTurn (polarPoint 1 psi))) htha hthb hs hgap
  have hpolarB : Tendsto (fun n => polarPoint 1 (theta n b)) atTop (nhds (polarPoint 1 psi)) :=
    ((polarPoint_contDiff ∞).continuous.tendsto (1,psi)).comp (tendsto_const_nhds.prodMk_nhds hthb)
  have hJb : Tendsto (fun n => quarterTurn (polarPoint 1 (theta n b))) atTop
      (nhds (quarterTurn (polarPoint 1 psi))) :=
    quarterTurnLinear.toContinuousLinearMap.continuous.tendsto _ |>.comp hpolarB
  have ht := physical_pair_near_cartesian_angular_secant_limit mass d q a b c hab hca hcb hcf hd hdt U v
    (polarPoint 1 psi) hU (by simp only [polarPoint_norm,abs_one]) L hqc hsource hsmall hv hmd
    (fun n => quarterTurn (polarPoint 1 (theta n a))) (fun n => quarterTurn (polarPoint 1 (theta n b)))
    (quarterTurn (polarPoint 1 psi)) (inner ℝ v (quarterTurn (polarPoint 1 psi)) • (-polarPoint 1 psi)) hJb hJdiff
  convert! ht using 1
  · funext n
    rw [physicalSourceAngularField_eq_cartesian _ _ _ _ (hrc n),
      physicalSourceAngularField_eq_cartesian _ _ _ _ (hrc n)]
    simp only [q,polarSatellites,newtonTargetField,sub_zero]
  · rw [real_inner_smul_left,tangential_unit_source_angular_newton_eigenvalue U v psi hU hUr]
    ring

/-- The far source is differentiated along the true radial smaller-pair
direction, retaining the moving source parameters. -/
theorem physicalSourceAngularField_moving_radial_secant_limit
    (s angle ra va rb vb d : ℕ → ℝ) (angle0 psi omega : ℝ)
    (hst : Tendsto s atTop (nhds 1)) (hangt : Tendsto angle atTop (nhds angle0))
    (hrat : Tendsto ra atTop (nhds 1)) (hrbt : Tendsto rb atTop (nhds 1))
    (hvat : Tendsto va atTop (nhds psi)) (hvbt : Tendsto vb atTop (nhds psi))
    (hd : ∀ n,0<d n)
    (hrd : Tendsto (fun n => (rb n-ra n)/d n) atTop (nhds omega))
    (hvd : Tendsto (fun n => (vb n-va n)/d n) atTop (nhds 0))
    (hne : angle0≠psi) (hpi : |angle0-psi|<Real.pi) :
    Tendsto (fun n => (physicalSourceAngularField (s n) (angle n) (rb n) (vb n)-
      physicalSourceAngularField (s n) (angle n) (ra n) (va n))/d n)
      atTop (nhds (omega*physicalSourceAngularRadialDerivative 1 angle0 1 psi)) := by
  let F : (ℝ×ℝ)×(ℝ×ℝ) → ℝ := fun z => physicalSourceAngularField z.1.1 z.1.2 z.2.1 z.2.2
  let z0 : (ℝ×ℝ)×(ℝ×ℝ) := ((1,angle0),(1,psi))
  let U : (ℝ×ℝ)×(ℝ×ℝ) := ((0,0),(1,0))
  have hsep := polarUnit_ne_of_angle_ne angle0 psi hne (by simpa only [abs_sub_comm] using hpi)
  have hc : ContDiffAt ℝ ∞ F z0 := physicalSourceAngularField_joint_contDiffAt z0 (by norm_num [z0]) hsep
  have hA : Tendsto (fun n => ((s n,angle n),(ra n,va n))) atTop (nhds z0) :=
    (hst.prodMk_nhds hangt).prodMk_nhds (hrat.prodMk_nhds hvat)
  have hB : Tendsto (fun n => ((s n,angle n),(rb n,vb n))) atTop (nhds z0) :=
    (hst.prodMk_nhds hangt).prodMk_nhds (hrbt.prodMk_nhds hvbt)
  have hv : Tendsto (fun n => (d n)⁻¹ •
      (((s n,angle n),(rb n,vb n))-((s n,angle n),(ra n,va n))))
      atTop (nhds (omega • U)) := by
    have ht := (tendsto_const_nhds : Tendsto (fun _ : ℕ => ((0,0) : ℝ×ℝ)) atTop (nhds (0,0))).prodMk_nhds
      (hrd.prodMk_nhds hvd)
    simpa only [U,Prod.smul_mk,Prod.mk_sub_mk,Prod.zero_eq_mk,smul_zero,smul_eq_mul,sub_self,
      mul_zero,mul_one,div_eq_mul_inv,mul_comm] using ht
  have hp : HasDerivAt (fun r : ℝ => (((1 : ℝ),angle0),(r,psi))) U 1 := by
    exact (hasDerivAt_const (1 : ℝ) ((1 : ℝ),angle0)).prodMk
      ((hasDerivAt_id (1 : ℝ)).prodMk (hasDerivAt_const (1 : ℝ) psi))
  have hpartial : (fderiv ℝ F z0) U=physicalSourceAngularRadialDerivative 1 angle0 1 psi := by
    have hp' := (hc.differentiableAt (by simp)).hasFDerivAt.comp_hasDerivAt 1 hp
    exact hp'.unique (physicalSourceAngularField_hasDerivAt_radius 1 angle0 1 psi (by norm_num) hsep)
  have ht := strict_fderiv_scaled_difference_limit F (fderiv ℝ F z0) z0
    (hc.hasStrictFDerivAt (by simp)) _ _ hA hB d hd (omega • U) hv
  simpa only [F,map_smul,smul_eq_mul,hpartial] using ht

/-- Positivity of the exact pair Q difference uses only the real ordered
collision-free sequence; a complete-pair limiting partition is unnecessary. -/
theorem physical_pair_tangential_difference_eventually_positive
    (mu r theta : ℕ → Satellite → ℝ) (a b : Satellite) (hab : a≠b)
    (hm : ∀ n i,0<mu n i) (hr : ∀ n i,0<r n i)
    (hQ : ∀ n i,tangentialResidual (mu n) (r n) (theta n) i=0)
    (hs : ∀ n,0<satelliteDistance (polarSatellites (r n) (theta n)) a b)
    (hst : Tendsto (fun n => satelliteDistance (polarSatellites (r n) (theta n)) a b) atTop (nhds 0))
    (hrat : Tendsto (fun n => r n a) atTop (nhds 1))
    (hrbt : Tendsto (fun n => r n b) atTop (nhds 1))
    (horder : ∀ n,0<theta n b-theta n a ∧ theta n b-theta n a<Real.pi) :
    ∀ᶠ n in atTop,0<physicalPairExteriorAngularField (mu n) (r n) (theta n) a b (r n b) (theta n b)-
      physicalPairExteriorAngularField (mu n) (r n) (theta n) a b (r n a) (theta n a) := by
  filter_upwards [hrat.eventually (Ioi_mem_nhds (by norm_num : (1/2 : ℝ)<1)),
    hrbt.eventually (Ioi_mem_nhds (by norm_num : (1/2 : ℝ)<1)),
    hst.eventually (Iio_mem_nhds (by norm_num : (0 : ℝ)<1/2))] with n hna hnb hns
  rw [physical_pair_tangential_difference (mu n) (r n) (theta n) a b hab (hr n) (hQ n)]
  exact mul_pos (Real.sin_pos_of_pos_of_lt_pi (horder n).1 (horder n).2)
    (pairTangentialCoefficient_pos (mu n) (r n) (theta n) a b (hm n) (hr n) (hs n)
      (by linarith) (by linarith))

theorem physical_nested_pair_exterior_secant_limit
    (mu : ℕ → MassRatio) (d : ℕ → ℝ) (q : ℕ → SatelliteConfiguration)
    (a b c p : Satellite) (hab : a≠b) (hcp : c≠p)
    (hc : c∈pairExteriorLabels a b) (hp : p∈pairExteriorLabels a b)
    (hcf : ∀ n,RelativeCollisionFree (q n)) (hd : ∀ n,0<d n)
    (U v e z : Plane) (hU : ‖U‖=1) (L M : ℝ) (hze : z≠e)
    (hsource : Tendsto (fun n => (d n)⁻¹ • (q n c-q n a)) atTop (nhds U))
    (hsmall : Tendsto (fun n => satelliteDistance (q n) a b/d n) atTop (nhds 0))
    (hv : Tendsto (fun n => physicalPairDirection (q n) a b) atTop (nhds v))
    (hmd : Tendsto (fun n => mu n c/d n^3) atTop (nhds L))
    (hmp : Tendsto (fun n => mu n p) atTop (nhds M))
    (hqa : Tendsto (fun n => q n a) atTop (nhds e))
    (hqb : Tendsto (fun n => q n b) atTop (nhds e))
    (hqp : Tendsto (fun n => q n p) atTop (nhds z)) :
    Tendsto (fun n => pairSecantExteriorField (mu n) (q n) a b (physicalPairDirection (q n) a b))
      atTop (nhds (L • dividedNewtonTargetField U 0 0 v+M • dividedNewtonTargetField z e e v)) := by
  have hca := (Finset.mem_erase.mp (Finset.mem_erase.mp hc).2).1
  have hcb := (Finset.mem_erase.mp hc).1
  have hnear := physical_pair_weighted_near_secant_limit (fun n => mu n c) d q a b c hab hca hcb
    hcf hd U v hU L hsource hsmall hv hmd
  have hfar := (dividedNewtonTargetField_joint_contDiffAt ∞ ((z,e),(e,v)) hze hze).continuousAt.tendsto.comp
    ((hqp.prodMk_nhds hqa).prodMk_nhds (hqb.prodMk_nhds hv))
  have ht := hnear.add (hmp.smul hfar)
  convert! ht using 1
  funext n
  rw [pairSecantExteriorField,pairExteriorLabels_eq_two a b c p hab hc hp hcp,Finset.sum_pair hcp]
  rfl

theorem physicalPairExteriorAngularField_eq_selected_sources
    (mu r theta : Satellite → ℝ) (a b c p : Satellite) (hab : a≠b) (hcp : c≠p)
    (hc : c∈pairExteriorLabels a b) (hp : p∈pairExteriorLabels a b) (rho v : ℝ) :
    physicalPairExteriorAngularField mu r theta a b rho v=
      mu c*physicalSourceAngularField (r c) (theta c) rho v+
      mu p*physicalSourceAngularField (r p) (theta p) rho v := by
  rw [physicalPairExteriorAngularField_eq_source_sum,
    pairExteriorLabels_eq_two a b c p hab hc hp hcp,Finset.sum_pair hcp]

/-- For a lower triple the positive radial micro direction contradicts
the exact positive Q difference. The nearby source contributes zero in
this radial direction; the separated source contributes a negative limit. -/
theorem physical_nested_pair_left_outward_radial_impossible
    (mu r theta : ℕ → Satellite → ℝ) (d : ℕ → ℝ) (a b c p : Satellite)
    (hab : a≠b) (hcp : c≠p) (hc : c∈pairExteriorLabels a b) (hp : p∈pairExteriorLabels a b)
    (hcf : ∀ n,RelativeCollisionFree (polarSatellites (r n) (theta n)))
    (hr : ∀ n i,0<r n i) (hrt : ∀ i,Tendsto (fun n => r n i) atTop (nhds 1))
    (psi angle0 : ℝ) (htha : Tendsto (fun n => theta n a) atTop (nhds psi))
    (hthb : Tendsto (fun n => theta n b) atTop (nhds psi))
    (hthc : Tendsto (fun n => theta n c) atTop (nhds psi))
    (hthp : Tendsto (fun n => theta n p) atTop (nhds angle0))
    (hside : 0<angle0-psi ∧ angle0-psi<Real.pi)
    (hd : ∀ n,0<d n) (hdt : Tendsto d atTop (nhds 0)) (U : Plane)
    (hU : ‖U‖=1) (hUr : inner ℝ U (polarPoint 1 psi)=0) (L : ℝ)
    (hsource : Tendsto (fun n => (d n)⁻¹ •
      (polarPoint (r n c) (theta n c)-polarPoint (r n a) (theta n a))) atTop (nhds U))
    (hsmall : Tendsto (fun n => satelliteDistance (polarSatellites (r n) (theta n)) a b/d n) atTop (nhds 0))
    (hv : Tendsto (fun n => physicalPairDirection (polarSatellites (r n) (theta n)) a b)
      atTop (nhds (polarPoint 1 psi)))
    (hmd : Tendsto (fun n => mu n c/d n^3) atTop (nhds L))
    (hmp : Tendsto (fun n => mu n p) atTop (nhds 1))
    (hQpos : ∀ᶠ n in atTop,0<physicalPairExteriorAngularField (mu n) (r n) (theta n) a b (r n b) (theta n b)-
      physicalPairExteriorAngularField (mu n) (r n) (theta n) a b (r n a) (theta n a)) : False := by
  let q : ℕ → SatelliteConfiguration := fun n => polarSatellites (r n) (theta n)
  let s : ℕ → ℝ := fun n => satelliteDistance (q n) a b
  have hs (n : ℕ) : 0<s n := norm_pos_iff.mpr (sub_ne_zero.mpr ((hcf n).2 a b hab))
  have hca := (Finset.mem_erase.mp (Finset.mem_erase.mp hc).2).1
  have hcb := (Finset.mem_erase.mp hc).1
  have hnear0 := physical_pair_near_angular_secant_limit (fun n => mu n c) d r theta a b c hab hca hcb
    hcf (fun n => hr n c) (fun n => hr n b) (hrt c) (hrt b) psi htha hthb hthc hd hdt U
    (polarPoint 1 psi) hU hUr L hsource hsmall hv hmd
  have hnear : Tendsto (fun n => mu n c*(physicalSourceAngularField (r n c) (theta n c) (r n b) (theta n b)-
      physicalSourceAngularField (r n c) (theta n c) (r n a) (theta n a))/s n) atTop (nhds 0) := by
    simpa only [polarPoint_inner_rotation,sub_self,Real.sin_zero,mul_zero] using hnear0
  have hratios := physical_pair_direction_polar_ratio_limits r theta a b psi (fun n => hr n b) hs
    (hrt b) htha hthb (polarPoint 1 psi) hv
  have hrad : Tendsto (fun n => (r n b-r n a)/s n) atTop (nhds 1) := by
    simpa only [polarPoint_inner_radial,sub_self,Real.cos_zero,mul_one] using hratios.2
  have hangle : Tendsto (fun n => (theta n b-theta n a)/s n) atTop (nhds 0) := by
    simpa only [polarPoint_inner_rotation,sub_self,Real.sin_zero,mul_zero] using hratios.1
  have hfar0 := physicalSourceAngularField_moving_radial_secant_limit _ _ _ _ _ _ s angle0 psi 1
    (hrt p) hthp (hrt a) (hrt b) htha hthb hs hrad hangle
    (by intro he; rw [he,sub_self] at hside; linarith [hside.1])
    (by rw [abs_of_pos hside.1]; exact hside.2)
  have hfar := hmp.mul hfar0
  have ht : Tendsto (fun n => (physicalPairExteriorAngularField (mu n) (r n) (theta n) a b (r n b) (theta n b)-
      physicalPairExteriorAngularField (mu n) (r n) (theta n) a b (r n a) (theta n a))/s n)
      atTop (nhds (physicalSourceAngularRadialDerivative 1 angle0 1 psi)) := by
    convert! hnear.add hfar using 1
    · funext n
      rw [physicalPairExteriorAngularField_eq_selected_sources _ _ _ a b c p hab hcp hc hp,
        physicalPairExteriorAngularField_eq_selected_sources _ _ _ a b c p hab hcp hc hp]
      ring
    · ring
  have hnonneg := ge_of_tendsto ht (by
    filter_upwards [hQpos] with n hn
    exact (div_pos hn (hs n)).le)
  exact (not_le_of_gt (physicalSourceAngularRadialDerivative_unit_neg angle0 psi hside.1 hside.2)) hnonneg

/-- A selected real smaller-pair direction is the positive unit tangent.
The third mass-to-macro-scale limit is extracted only for this intermediate
step; no convergence of the current internal mass share is used. -/
theorem physical_nested_pair_selected_tangential
    (eps : ℕ → ℝ) (mu : ℕ → MassRatio) (r theta : ℕ → Satellite → ℝ) (d : ℕ → ℝ)
    (a b c p : Satellite) (hab : a≠b) (hcp : c≠p)
    (hc : c∈pairExteriorLabels a b) (hp : p∈pairExteriorLabels a b)
    (hcf : ∀ n,RelativeCollisionFree (polarSatellites (r n) (theta n)))
    (hroot : ∀ n i,vectorResidual (eps n) (mu n) (polarSatellites (r n) (theta n)) i=0)
    (heps : Tendsto eps atTop (nhds 0)) (hr : ∀ n i,0<r n i)
    (hrt : ∀ i,Tendsto (fun n => r n i) atTop (nhds 1))
    (psi angle0 : ℝ) (htha : Tendsto (fun n => theta n a) atTop (nhds psi))
    (hthb : Tendsto (fun n => theta n b) atTop (nhds psi))
    (hthc : Tendsto (fun n => theta n c) atTop (nhds psi))
    (hthp : Tendsto (fun n => theta n p) atTop (nhds angle0))
    (hside : 0<angle0-psi ∧ angle0-psi<Real.pi)
    (hd : ∀ n,0<d n) (hdt : Tendsto d atTop (nhds 0)) (U v : Plane)
    (hU : ‖U‖=1) (hUr : inner ℝ U (polarPoint 1 psi)=0) (L : ℝ)
    (hsource : Tendsto (fun n => (d n)⁻¹ •
      (polarPoint (r n c) (theta n c)-polarPoint (r n a) (theta n a))) atTop (nhds U))
    (hsmall : Tendsto (fun n => satelliteDistance (polarSatellites (r n) (theta n)) a b/d n) atTop (nhds 0))
    (hv : Tendsto (fun n => physicalPairDirection (polarSatellites (r n) (theta n)) a b) atTop (nhds v))
    (hmd : Tendsto (fun n => mu n c/d n^3) atTop (nhds L))
    (hmp : Tendsto (fun n => mu n p) atTop (nhds 1))
    (horder : ∀ n,0<theta n b-theta n a ∧ theta n b-theta n a<Real.pi)
    (hQpos : ∀ᶠ n in atTop,0<physicalPairExteriorAngularField (mu n) (r n) (theta n) a b (r n b) (theta n b)-
      physicalPairExteriorAngularField (mu n) (r n) (theta n) a b (r n a) (theta n a))
    (hsupport : ∀ᶠ n in atTop,0<det2
      (polarPoint (r n b) (theta n b)-polarPoint (r n a) (theta n a))
      (polarPoint (r n p) (theta n p)-polarPoint (r n a) (theta n a))) :
    v=quarterTurn (polarPoint 1 psi) ∧
      Tendsto (fun n => eps n*(mu n a+mu n b)/
        satelliteDistance (polarSatellites (r n) (theta n)) a b^3) atTop (nhds 0) ∧
      Tendsto (fun n => (theta n b-theta n a)/
        satelliteDistance (polarSatellites (r n) (theta n)) a b) atTop (nhds 1) ∧
      Tendsto (fun n => (r n b-r n a)/
        satelliteDistance (polarSatellites (r n) (theta n)) a b) atTop (nhds 0) := by
  let q : ℕ → SatelliteConfiguration := fun n => polarSatellites (r n) (theta n)
  let s : ℕ → ℝ := fun n => satelliteDistance (q n) a b
  let e : Plane := polarPoint 1 psi
  let z : Plane := polarPoint 1 angle0
  have hs (n : ℕ) : 0<s n := norm_pos_iff.mpr (sub_ne_zero.mpr ((hcf n).2 a b hab))
  have hqa : Tendsto (fun n => q n a) atTop (nhds e) :=
    ((polarPoint_contDiff ∞).continuous.tendsto (1,psi)).comp ((hrt a).prodMk_nhds htha)
  have hqb : Tendsto (fun n => q n b) atTop (nhds e) :=
    ((polarPoint_contDiff ∞).continuous.tendsto (1,psi)).comp ((hrt b).prodMk_nhds hthb)
  have hqp : Tendsto (fun n => q n p) atTop (nhds z) :=
    ((polarPoint_contDiff ∞).continuous.tendsto (1,angle0)).comp ((hrt p).prodMk_nhds hthp)
  have hze : z≠e := polarUnit_ne_of_angle_ne angle0 psi
    (by intro he; rw [he,sub_self] at hside; linarith [hside.1])
    (by rw [abs_of_neg (show psi-angle0<0 by linarith [hside.1])]; linarith [hside.2])
  have hsec := physical_nested_pair_exterior_secant_limit mu d q a b c p hab hcp hc hp hcf hd U v e z hU L 1
    hze hsource hsmall hv hmd hmp hqa hqb hqp
  have hP : Tendsto (fun n => eps n • pairSecantExteriorField (mu n) (q n) a b
      (physicalPairDirection (q n) a b)) atTop (nhds 0) := by
    simpa only [zero_smul] using heps.smul hsec
  have halt := physical_pair_direction_alternative_of_exterior_vanishes eps mu q a b hab hcf hroot e v
    (by simp only [e,polarPoint_norm,abs_one]) hqa hqb hv hP
  have hsup : 0≤det2 v (z-e) := by
    have ht := pairDet2_continuous.continuousAt.tendsto.comp (hv.prodMk_nhds (hqp.sub hqa))
    apply ge_of_tendsto ht
    filter_upwards [hsupport] with n hn
    change 0<det2 (q n b-q n a) (q n p-q n a) at hn
    have he : det2 (q n b-q n a) (q n p-q n a)=
        s n*det2 (physicalPairDirection (q n) a b) (q n p-q n a) := by
      rw [physicalPairDirection_gap (q n) a b ((hcf n).2 a b hab)]
      simp only [det2,PiLp.smul_apply,smul_eq_mul]
      ring
    rw [he] at hn
    exact ((mul_pos_iff_of_pos_left (hs n)).mp hn).le
  have htangent : Tendsto (fun n => eps n*(mu n a+mu n b)/s n^3) atTop (nhds 0) ∧ inner ℝ v e=0 := by
    rcases halt with ht|⟨_,he|he⟩
    · exact ht
    · exact (physical_nested_pair_left_outward_radial_impossible mu r theta d a b c p hab hcp hc hp
        hcf hr hrt psi angle0 htha hthb hthc hthp hside hd hdt U hU hUr L hsource hsmall
        (by simpa only [he] using hv) hmd hmp hQpos).elim
    · rw [he,pairDet2_neg_left,pairDet2_unit_sub] at hsup
      have hsin := Real.sin_pos_of_pos_of_lt_pi hside.1 hside.2
      linarith
  obtain ⟨hg,hrad⟩ := physical_pair_direction_polar_ratio_limits r theta a b psi (fun n => hr n b)
    hs (hrt b) htha hthb v hv
  have hcoef : 0 ≤ inner ℝ v (quarterTurn (polarPoint 1 psi)) := ge_of_tendsto hg
    (Eventually.of_forall (fun n => (div_pos (horder n).1 (hs n)).le))
  have hnv : ‖v‖=1 := by
    apply tendsto_nhds_unique hv.norm
    convert! (tendsto_const_nhds : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (nhds 1)) using 1
    funext n
    exact physicalPairDirection_norm (q n) a b ((hcf n).2 a b hab)
  have hdecomp := polarOrthonormal_decomposition psi v
  rw [htangent.2,zero_smul,zero_add] at hdecomp
  have hJ : inner ℝ (quarterTurn (polarPoint 1 psi)) (quarterTurn (polarPoint 1 psi))=1 := by
    rw [quarterTurn_inner_quarterTurn,polarPoint_inner_radial]
    simp
  have hvi : inner ℝ v v=1 := by rw [real_inner_self_eq_norm_sq,hnv]; norm_num
  have hi := congrArg (fun w : Plane => inner ℝ w w) hdecomp
  rw [hvi,real_inner_smul_left,real_inner_smul_right,hJ,mul_one] at hi
  have hone : inner ℝ v (quarterTurn (polarPoint 1 psi))=1 := by nlinarith
  have hvr : inner ℝ v (polarPoint 1 psi)=0 := htangent.2
  refine ⟨by simpa only [hone,one_smul] using hdecomp,htangent.1,?_,?_⟩
  · simpa only [hone] using hg
  · simpa only [hvr] using hrad

end DominantFiveBody
