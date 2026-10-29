import DominantFiveBody.CollisionNestedPreciseScales

/-! # Removing all intermediate smaller-pair selections -/

noncomputable section
open scoped BigOperators ContDiff
open Filter Set Topology
namespace DominantFiveBody
set_option maxHeartbeats 1500000

theorem tendsto_of_compact_selected_limit
    {E F : Type*} [TopologicalSpace E] [FirstCountableTopology E] [PseudoMetricSpace F]
    (A : ℕ → E) (f : ℕ → F) (K : Set E) (hK : IsCompact K)
    (hAK : ∀ᶠ n in atTop,A n∈K) (y : F)
    (hselected : ∀ (phi : ℕ → ℕ),StrictMono phi → ∀ v∈K,
      Tendsto (A ∘ phi) atTop (nhds v) → Tendsto (f ∘ phi) atTop (nhds y)) :
    Tendsto f atTop (nhds y) := by
  apply Metric.tendsto_atTop.mpr
  intro eta heta
  by_contra hbad
  push Not at hbad
  obtain ⟨phi,hphi,hfail⟩ := Nat.exists_strictMono_subsequence (P := fun n => eta≤dist (f n) y) (by
    intro N
    obtain ⟨n,hn,hbadn⟩ := hbad (N+1)
    exact ⟨n,by omega,hbadn⟩)
  obtain ⟨v,hv,psi,hpsi,hvt⟩ := hK.tendsto_subseq' (hphi.tendsto_atTop.eventually hAK).frequently
  have ht := hselected (phi ∘ psi) (hphi.comp hpsi) v hv hvt
  obtain ⟨n,hn⟩ := (ht.eventually (Metric.ball_mem_nhds y heta)).exists
  have hf := hfail (psi n)
  exact (not_lt_of_ge hf) hn

/-- The physical nested micro direction and cubic scale hold along the
original sequence. Compactness selects only a unit direction and a bounded
third-mass ratio inside the proof, and both selections are removed. -/
theorem physical_nested_pair_unselected_precise_scales
    (eps : ℕ → ℝ) (mu : ℕ → MassRatio) (r theta : ℕ → Satellite → ℝ) (d : ℕ → ℝ)
    (a b c p : Satellite) (hab : a≠b) (hcp : c≠p)
    (hc : c∈pairExteriorLabels a b) (hp : p∈pairExteriorLabels a b)
    (hcf : ∀ n,RelativeCollisionFree (polarSatellites (r n) (theta n)))
    (hroot : ∀ n i,vectorResidual (eps n) (mu n) (polarSatellites (r n) (theta n)) i=0)
    (hQ : ∀ n i,tangentialResidual (mu n) (r n) (theta n) i=0)
    (heps : Tendsto eps atTop (nhds 0)) (hm : ∀ n i,0<mu n i) (hr : ∀ n i,0<r n i)
    (hrt : ∀ i,Tendsto (fun n => r n i) atTop (nhds 1))
    (hmat : Tendsto (fun n => mu n a) atTop (nhds 0))
    (hmbt : Tendsto (fun n => mu n b) atTop (nhds 0))
    (psi angle0 : ℝ) (htha : Tendsto (fun n => theta n a) atTop (nhds psi))
    (hthb : Tendsto (fun n => theta n b) atTop (nhds psi))
    (hthc : Tendsto (fun n => theta n c) atTop (nhds psi))
    (hthp : Tendsto (fun n => theta n p) atTop (nhds angle0))
    (hside : 0<angle0-psi ∧ angle0-psi<Real.pi)
    (hd : ∀ n,0<d n) (hdt : Tendsto d atTop (nhds 0)) (U : Plane)
    (hU : ‖U‖=1) (hUr : inner ℝ U (polarPoint 1 psi)=0)
    (hsource : Tendsto (fun n => (d n)⁻¹ •
      (polarPoint (r n c) (theta n c)-polarPoint (r n a) (theta n a))) atTop (nhds U))
    (hsmall : Tendsto (fun n => satelliteDistance (polarSatellites (r n) (theta n)) a b/d n) atTop (nhds 0))
    (hmp : Tendsto (fun n => mu n p) atTop (nhds 1))
    (horder : ∀ n,0<theta n b-theta n a ∧ theta n b-theta n a<Real.pi)
    (hQpos : ∀ᶠ n in atTop,0<physicalPairExteriorAngularField (mu n) (r n) (theta n) a b (r n b) (theta n b)-
      physicalPairExteriorAngularField (mu n) (r n) (theta n) a b (r n a) (theta n a))
    (hsupport : ∀ᶠ n in atTop,0<det2
      (polarPoint (r n b) (theta n b)-polarPoint (r n a) (theta n a))
      (polarPoint (r n p) (theta n p)-polarPoint (r n a) (theta n a)))
    (hmacro : Tendsto (fun n => (mu n a+mu n b+mu n c)/d n^3)
      atTop (nhds (Coorbital.kappa |psi-angle0|))) :
    Tendsto (fun n => physicalPairDirection (polarSatellites (r n) (theta n)) a b)
      atTop (nhds (quarterTurn (polarPoint 1 psi))) ∧
    Tendsto (fun n => eps n*(mu n a+mu n b)/
      satelliteDistance (polarSatellites (r n) (theta n)) a b^3) atTop (nhds 0) ∧
    Tendsto (fun n => (theta n b-theta n a)/
      satelliteDistance (polarSatellites (r n) (theta n)) a b) atTop (nhds 1) ∧
    Tendsto (fun n => (r n b-r n a)/
      satelliteDistance (polarSatellites (r n) (theta n)) a b) atTop (nhds 0) ∧
    Tendsto (fun n => (mu n a+mu n b)/
      satelliteDistance (polarSatellites (r n) (theta n)) a b^3)
      atTop (nhds (3*Coorbital.kappa |psi-angle0|)) ∧
    Tendsto (fun n => mu n c/d n^3) atTop (nhds (Coorbital.kappa |psi-angle0|)) ∧
    Tendsto (fun n => (mu n a+mu n b)/d n^3) atTop (nhds 0) := by
  let q : ℕ → SatelliteConfiguration := fun n => polarSatellites (r n) (theta n)
  let s : ℕ → ℝ := fun n => satelliteDistance (q n) a b
  let D : ℝ := Coorbital.kappa |psi-angle0|
  let J : Plane := quarterTurn (polarPoint 1 psi)
  let A : ℕ → Plane×ℝ := fun n => (physicalPairDirection (q n) a b,mu n c/d n^3)
  let f : ℕ → Plane×(ℝ×(ℝ×(ℝ×ℝ))) := fun n =>
    (physicalPairDirection (q n) a b,(eps n*(mu n a+mu n b)/s n^3,
      ((theta n b-theta n a)/s n,((r n b-r n a)/s n,(mu n a+mu n b)/s n^3))))
  let K : Set (Plane×ℝ) := Metric.closedBall 0 1 ×ˢ Icc (0 : ℝ) (|D|+1)
  have hK : IsCompact K := (isCompact_closedBall (0 : Plane) 1).prod isCompact_Icc
  have hs (n : ℕ) : 0<s n := norm_pos_iff.mpr (sub_ne_zero.mpr ((hcf n).2 a b hab))
  have hAK : ∀ᶠ n in atTop,A n∈K := by
    filter_upwards [hmacro.eventually (Iio_mem_nhds (lt_of_le_of_lt (le_abs_self D) (lt_add_one _)))] with n hn
    refine ⟨?_,?_,?_⟩
    · simpa only [Metric.mem_closedBall,dist_zero_right,A,physicalPairDirection_norm (q n) a b
        ((hcf n).2 a b hab)] using (le_refl (1 : ℝ))
    · exact (div_pos (hm n c) (pow_pos (hd n) 3)).le
    · have hnu : mu n c/d n^3≤(mu n a+mu n b+mu n c)/d n^3 :=
        (div_le_div_iff_of_pos_right (pow_pos (hd n) 3)).mpr (by linarith [hm n a,hm n b])
      exact hnu.trans hn.le
  have ht : Tendsto f atTop (nhds (J,((0 : ℝ),(1,((0 : ℝ),3*D))))) := by
    apply tendsto_of_compact_selected_limit A f K hK hAK
    intro phi hphi v _ hvt
    have htop := hphi.tendsto_atTop
    have hv : Tendsto (fun n => physicalPairDirection (q (phi n)) a b) atTop (nhds v.1) := by
      simpa only [A,Function.comp_def] using (continuous_fst.tendsto v).comp hvt
    have hmc : Tendsto (fun n => mu (phi n) c/d (phi n)^3) atTop (nhds v.2) := by
      simpa only [A,Function.comp_def] using (continuous_snd.tendsto v).comp hvt
    have hdir := physical_nested_pair_selected_tangential (eps ∘ phi) (mu ∘ phi) (r ∘ phi) (theta ∘ phi)
      (d ∘ phi) a b c p hab hcp hc hp (fun n => hcf (phi n)) (fun n => hroot (phi n))
      (heps.comp htop) (fun n => hr (phi n)) (fun i => (hrt i).comp htop) psi angle0
      (htha.comp htop) (hthb.comp htop) (hthc.comp htop) (hthp.comp htop) hside
      (fun n => hd (phi n)) (hdt.comp htop) U v.1 hU hUr v.2 (hsource.comp htop)
      (hsmall.comp htop) hv hmc (hmp.comp htop) (fun n => horder (phi n))
      (htop.eventually hQpos) (htop.eventually hsupport)
    have hvJ : Tendsto (fun n => physicalPairDirection (q (phi n)) a b) atTop (nhds J) := by
      simpa only [hdir.1] using hv
    have hinner := physical_nested_pair_mass_cube_limit_of_tangential (mu ∘ phi) (r ∘ phi) (theta ∘ phi)
      (d ∘ phi) a b c p hab hcp hc hp (fun n => hcf (phi n)) (fun n => hm (phi n))
      (fun n => hr (phi n)) (fun n => hQ (phi n)) (fun i => (hrt i).comp htop)
      (hmat.comp htop) (hmbt.comp htop) psi angle0 (htha.comp htop) (hthb.comp htop)
      (hthc.comp htop) (hthp.comp htop)
      (by intro he; rw [he,sub_self] at hside; linarith [hside.1])
      (by rw [abs_of_pos hside.1]; exact hside.2)
      (fun n => hd (phi n)) (hdt.comp htop) U hU hUr v.2 (hsource.comp htop)
      (hsmall.comp htop) hvJ hmc (hmp.comp htop) (fun n => horder (phi n)) hdir.2.2.1 hdir.2.2.2
    have hprecise := nested_precise_two_cube_limits_of_selected
      (fun n => mu (phi n) a+mu (phi n) b) (fun n => mu (phi n) c) (s ∘ phi) (d ∘ phi)
      D v.2 (fun n => hs (phi n)) (fun n => hd (phi n)) (hsmall.comp htop)
      (hmacro.comp htop) hinner hmc
    exact hvJ.prodMk_nhds (hdir.2.1.prodMk_nhds (hdir.2.2.1.prodMk_nhds
      (hdir.2.2.2.prodMk_nhds hprecise.2.2.2)))
  have hv := (continuous_fst.tendsto _).comp ht
  have hrest := (continuous_snd.tendsto _).comp ht
  have hlambda := (continuous_fst.tendsto _).comp hrest
  have hrest' := (continuous_snd.tendsto _).comp hrest
  have hgap := (continuous_fst.tendsto _).comp hrest'
  have hrest'' := (continuous_snd.tendsto _).comp hrest'
  have hrad := (continuous_fst.tendsto _).comp hrest''
  have hinner := (continuous_snd.tendsto _).comp hrest''
  have hx : Tendsto (fun n => (mu n a+mu n b)/d n^3) atTop (nhds 0) := by
    convert! hinner.mul (hsmall.pow 3) using 1
    · funext n
      simp only [f,Function.comp_def]
      have hsn : satelliteDistance (polarSatellites (r n) (theta n)) a b≠0 := ne_of_gt (hs n)
      dsimp only [s,q]
      field_simp [hsn,ne_of_gt (hd n)]
    · ring
  have hmc : Tendsto (fun n => mu n c/d n^3) atTop (nhds D) := by
    convert! hmacro.sub hx using 1
    · funext n; ring
    · simp only [D,sub_zero]
  exact ⟨hv,hlambda,hgap,hrad,hinner,hmc,hx⟩

end DominantFiveBody
