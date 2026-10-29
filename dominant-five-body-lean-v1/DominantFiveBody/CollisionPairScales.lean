import DominantFiveBody.CollisionScales
import DominantFiveBody.PairDirections
import DominantFiveBody.DividedNewtonField
import DominantFiveBody.NewtonTargetDerivative
import DominantFiveBody.PolarPointDerivative
import DominantFiveBody.PairUnitBoundary
import Mathlib.Algebra.Order.Field.Pi

/-! # Actual complete-pair equations and collision-scale analysis

Source: Proposition 4.2. These identities are proved directly from the
physical mass-divided equations, before any chart capture. The exterior
field retains the current source positions and masses as joint variables.
-/

noncomputable section
open scoped BigOperators ContDiff
open Filter Topology

namespace DominantFiveBody

def primaryRadialField (q : Plane) : Plane := q-(‖q‖^3)⁻¹ • q

def pairExteriorLabels (a b : Satellite) : Finset Satellite :=
  (Finset.univ.erase a).erase b

def pairExteriorField (mu : MassRatio) (q : SatelliteConfiguration)
    (a b : Satellite) (p : Plane) : Plane :=
  ∑ j ∈ pairExteriorLabels a b,(mu j/‖p-q j‖^3) • (q j-p)

theorem pairExteriorLabels_comm (a b : Satellite) :
    pairExteriorLabels a b=pairExteriorLabels b a := Finset.erase_right_comm

theorem satelliteInteraction_split_pair (mu : MassRatio) (q : SatelliteConfiguration)
    (a b : Satellite) (hab : a≠b) :
    satelliteInteraction mu q a=
      (mu b/satelliteDistance q a b^3) • (q b-q a)+pairExteriorField mu q a b (q a) := by
  unfold satelliteInteraction pairExteriorField pairExteriorLabels
  have hb : b∈Finset.univ.erase a := Finset.mem_erase.mpr ⟨Ne.symm hab,Finset.mem_univ b⟩
  rw [← Finset.sum_erase_add _ _ hb]
  simp only [satelliteDistance]
  abel

/-- Exact `eq:pair-vdiff` at every actual pair of distinct satellite labels.
The mutual coefficient contains the current pair mass, without dividing by
either individual fraction. No positivity or scale limit is used here. -/
theorem physical_pair_vector_difference (eps : ℝ) (mu : MassRatio)
    (q : SatelliteConfiguration) (a b : Satellite) (hab : a≠b)
    (hroot : ∀ i,vectorResidual eps mu q i=0) :
    primaryRadialField (q b)-primaryRadialField (q a)+
      eps • (pairExteriorField mu q a b (q b)-pairExteriorField mu q a b (q a))=
        (eps*(mu a+mu b)/satelliteDistance q a b^3) • (q b-q a) := by
  have ha := hroot a
  have hb := hroot b
  change primaryRadialField (q a)+eps • satelliteInteraction mu q a-
    eps • relativeField mu q=0 at ha
  change primaryRadialField (q b)+eps • satelliteInteraction mu q b-
    eps • relativeField mu q=0 at hb
  rw [satelliteInteraction_split_pair mu q a b hab] at ha
  rw [satelliteInteraction_split_pair mu q b a (Ne.symm hab)] at hb
  have hdist : satelliteDistance q b a=satelliteDistance q a b := norm_sub_rev _ _
  rw [hdist,pairExteriorField,pairExteriorLabels_comm b a] at hb
  change primaryRadialField (q b)+eps •
    ((mu a/satelliteDistance q a b^3) • (q a-q b)+pairExteriorField mu q a b (q b))-
    eps • relativeField mu q=0 at hb
  simp only [smul_add,smul_smul] at ha hb
  have hscalar : eps*(mu a+mu b)/satelliteDistance q a b^3=
      eps*(mu a/satelliteDistance q a b^3)+eps*(mu b/satelliteDistance q a b^3) := by ring
  rw [hscalar]
  linear_combination (norm := module) hb-ha

/-- The vector difference above is a consequence of the original centered
normalized five-body equation, in actual primary-relative coordinates. -/
theorem normalized_pair_vector_difference (eps : ℝ) (mu : MassRatio)
    (x : Configuration) (hx : NormalizedCentralConfiguration (masses eps mu) x)
    (a b : Satellite) (hab : a≠b) :
    primaryRadialField (satellitesRelative x b)-primaryRadialField (satellitesRelative x a)+
      eps • (pairExteriorField mu (satellitesRelative x) a b (satellitesRelative x b)-
        pairExteriorField mu (satellitesRelative x) a b (satellitesRelative x a))=
      (eps*(mu a+mu b)/satelliteDistance (satellitesRelative x) a b^3) •
        (satellitesRelative x b-satellitesRelative x a) :=
  physical_pair_vector_difference eps mu _ a b hab
    (vectorResidual_zero_of_normalized eps mu x hx)

/-- The true pair exterior Newton field is jointly C-infinity near a
target separated from every exterior source. Current masses can tend to
zero; the sole analytic condition is the actual positive source distance. -/
theorem pairExteriorField_joint_contDiffAt (a b : Satellite)
    (d : (MassRatio×SatelliteConfiguration)×Plane)
    (hsep : ∀ j∈pairExteriorLabels a b,d.2≠d.1.2 j) :
    ContDiffAt ℝ ∞ (fun z : (MassRatio×SatelliteConfiguration)×Plane =>
      pairExteriorField z.1.1 z.1.2 a b z.2) d := by
  unfold pairExteriorField
  apply ContDiffAt.sum
  intro j hj
  have hm : ContDiffAt ℝ ∞ (fun z : (MassRatio×SatelliteConfiguration)×Plane => z.1.1 j) d := by
    fun_prop
  have hq : ContDiffAt ℝ ∞ (fun z : (MassRatio×SatelliteConfiguration)×Plane => z.2-z.1.2 j) d := by
    fun_prop
  have hn : ContDiffAt ℝ ∞ (fun z : (MassRatio×SatelliteConfiguration)×Plane =>
      ‖z.2-z.1.2 j‖) d := hq.norm ℝ (sub_ne_zero.mpr (hsep j hj))
  have hden : ‖d.2-d.1.2 j‖^3≠0 := pow_ne_zero 3 (norm_ne_zero_iff.mpr (sub_ne_zero.mpr (hsep j hj)))
  exact (hm.div (hn.pow 3) hden).smul (by fun_prop)

def physicalPairExteriorAngularField (mu r theta : Satellite → ℝ)
    (a b : Satellite) (rho v : ℝ) : ℝ :=
  ∑ j∈pairExteriorLabels a b,mu j*r j*Real.sin (theta j-v)*
    ((‖polarPoint rho v-polarPoint (r j) (theta j)‖^3)⁻¹-(r j^3)⁻¹)

theorem tangentialResidual_split_pair (mu r theta : Satellite → ℝ)
    (a b : Satellite) (hab : a≠b) :
    tangentialResidual mu r theta a=
      mu b*r b*Real.sin (theta b-theta a)*
        ((satelliteDistance (polarSatellites r theta) a b^3)⁻¹-(r b^3)⁻¹)+
      physicalPairExteriorAngularField mu r theta a b (r a) (theta a) := by
  unfold tangentialResidual physicalPairExteriorAngularField pairExteriorLabels
  have hb : b∈Finset.univ.erase a := Finset.mem_erase.mpr ⟨Ne.symm hab,Finset.mem_univ b⟩
  rw [← Finset.sum_erase_add _ _ hb]
  simp only [satelliteDistance,polarSatellites]
  ring

/-- Exact `eq:pair-qdiff`, obtained from both retained physical Q rows.
The individual masses are never divided out, so the algebra remains valid
even at zero pair fractions. Positive radii justify the displayed inverses. -/
theorem physical_pair_tangential_difference (mu r theta : Satellite → ℝ)
    (a b : Satellite) (hab : a≠b) (hr : ∀ i,0<r i)
    (hQ : ∀ i,tangentialResidual mu r theta i=0) :
    physicalPairExteriorAngularField mu r theta a b (r b) (theta b)-
      physicalPairExteriorAngularField mu r theta a b (r a) (theta a)=
    Real.sin (theta b-theta a)*
      ((mu a*r a+mu b*r b)/satelliteDistance (polarSatellites r theta) a b^3-
        mu a/(r a)^2-mu b/(r b)^2) := by
  have ha := hQ a
  have hb := hQ b
  rw [tangentialResidual_split_pair mu r theta a b hab] at ha
  rw [tangentialResidual_split_pair mu r theta b a (Ne.symm hab)] at hb
  have hdist : satelliteDistance (polarSatellites r theta) b a=
      satelliteDistance (polarSatellites r theta) a b := norm_sub_rev _ _
  rw [hdist,show theta a-theta b= -(theta b-theta a) by ring,Real.sin_neg,
    physicalPairExteriorAngularField,pairExteriorLabels_comm b a] at hb
  change mu a*r a*(-Real.sin (theta b-theta a))*
      ((satelliteDistance (polarSatellites r theta) a b^3)⁻¹-(r a^3)⁻¹)+
    physicalPairExteriorAngularField mu r theta a b (r b) (theta b)=0 at hb
  have hia : r a*(r a^3)⁻¹=(r a^2)⁻¹ := by
    field_simp [ne_of_gt (hr a)]
  have hib : r b*(r b^3)⁻¹=(r b^2)⁻¹ := by
    field_simp [ne_of_gt (hr b)]
  simp only [div_eq_mul_inv]
  linear_combination hb-ha-mu a*Real.sin (theta b-theta a)*hia-
    mu b*Real.sin (theta b-theta a)*hib

/-- Exact physical normalized-solution version of the pair Q difference.
This precedes and is independent of any regularized collision chart. -/
theorem normalized_pair_tangential_difference (eps : ℝ) (mu : MassRatio)
    (x : Configuration) (hx : NormalizedCentralConfiguration (masses eps mu) x)
    (heps : eps≠0) (r theta : Satellite → ℝ) (hr : ∀ i,0<r i)
    (hpolar : satellitesRelative x=polarSatellites r theta)
    (a b : Satellite) (hab : a≠b) :
    physicalPairExteriorAngularField mu r theta a b (r b) (theta b)-
      physicalPairExteriorAngularField mu r theta a b (r a) (theta a)=
    Real.sin (theta b-theta a)*
      ((mu a*r a+mu b*r b)/satelliteDistance (polarSatellites r theta) a b^3-
        mu a/(r a)^2-mu b/(r b)^2) :=
  physical_pair_tangential_difference mu r theta a b hab hr
    (tangentialResidual_zero_of_normalized eps mu x hx heps r theta hr hpolar)

def physicalPairDirection (q : SatelliteConfiguration) (a b : Satellite) : Plane :=
  (satelliteDistance q a b)⁻¹ • (q b-q a)

theorem physicalPairDirection_gap (q : SatelliteConfiguration) (a b : Satellite)
    (hab : q a≠q b) :
    q b-q a=satelliteDistance q a b • physicalPairDirection q a b := by
  have hd : satelliteDistance q a b≠0 := norm_ne_zero_iff.mpr (sub_ne_zero.mpr hab)
  rw [physicalPairDirection,smul_smul,mul_inv_cancel₀ hd,one_smul]

theorem physicalPairDirection_norm (q : SatelliteConfiguration) (a b : Satellite)
    (hab : q a≠q b) : ‖physicalPairDirection q a b‖=1 := by
  have hd : 0<satelliteDistance q a b := norm_pos_iff.mpr (sub_ne_zero.mpr hab)
  rw [physicalPairDirection,norm_smul,Real.norm_eq_abs,abs_of_pos (inv_pos.mpr hd),
    norm_sub_rev (q b) (q a),← satelliteDistance,inv_mul_cancel₀ (ne_of_gt hd)]

def pairSecantExteriorField (mu : MassRatio) (q : SatelliteConfiguration)
    (a b : Satellite) (v : Plane) : Plane :=
  ∑ j∈pairExteriorLabels a b,mu j • dividedNewtonTargetField (q j) (q a) (q b) v

theorem pairExteriorField_eq_newton_sum (mu : MassRatio) (q : SatelliteConfiguration)
    (a b : Satellite) (p : Plane) :
    pairExteriorField mu q a b p=
      ∑ j∈pairExteriorLabels a b,mu j • newtonTargetField (q j) p := by
  unfold pairExteriorField newtonTargetField
  simp only [smul_smul,div_eq_mul_inv,norm_sub_rev p]

theorem physical_pair_exterior_secant (mu : MassRatio) (q : SatelliteConfiguration)
    (a b : Satellite) (hq : RelativeCollisionFree q) (hab : a≠b) :
    (satelliteDistance q a b)⁻¹ •
      (pairExteriorField mu q a b (q b)-pairExteriorField mu q a b (q a))=
      pairSecantExteriorField mu q a b (physicalPairDirection q a b) := by
  have hd : satelliteDistance q a b≠0 := norm_ne_zero_iff.mpr (sub_ne_zero.mpr (hq.2 a b hab))
  simp only [pairExteriorField_eq_newton_sum,← Finset.sum_sub_distrib,Finset.smul_sum,
    pairSecantExteriorField]
  apply Finset.sum_congr rfl
  intro j hj
  have hjb : j≠b := (Finset.mem_erase.mp hj).1
  have hja : j≠a := (Finset.mem_erase.mp (Finset.mem_erase.mp hj).2).1
  rw [dividedNewtonTargetField_eq (q j) (q a) (q b) (physicalPairDirection q a b)
    (satelliteDistance q a b) hd (hq.2 j a hja) (hq.2 j b hjb)
    (physicalPairDirection_gap q a b (hq.2 a b hab))]
  module

theorem primaryRadialField_eq_newton (q : Plane) :
    primaryRadialField q=q+newtonTargetField 0 q := by
  unfold primaryRadialField newtonTargetField
  rw [zero_sub,norm_neg,smul_neg]
  abel

theorem physical_pair_primary_secant (q : SatelliteConfiguration)
    (a b : Satellite) (hq : RelativeCollisionFree q) (hab : a≠b) :
    (satelliteDistance q a b)⁻¹ • (primaryRadialField (q b)-primaryRadialField (q a))=
      physicalPairDirection q a b+
        dividedNewtonTargetField 0 (q a) (q b) (physicalPairDirection q a b) := by
  have hd : satelliteDistance q a b≠0 := norm_ne_zero_iff.mpr (sub_ne_zero.mpr (hq.2 a b hab))
  rw [dividedNewtonTargetField_eq 0 (q a) (q b) (physicalPairDirection q a b)
    (satelliteDistance q a b) hd (Ne.symm (hq.1 a)) (Ne.symm (hq.1 b))
    (physicalPairDirection_gap q a b (hq.2 a b hab)),primaryRadialField_eq_newton,
    primaryRadialField_eq_newton]
  unfold physicalPairDirection
  module

/-- The actual normalized pair-difference equation divided by its positive
physical distance. This is a regular secant identity, not a chart equation. -/
theorem physical_pair_direction_equation (eps : ℝ) (mu : MassRatio)
    (q : SatelliteConfiguration) (a b : Satellite) (hq : RelativeCollisionFree q)
    (hab : a≠b) (hroot : ∀ i,vectorResidual eps mu q i=0) :
    physicalPairDirection q a b+
      dividedNewtonTargetField 0 (q a) (q b) (physicalPairDirection q a b)+
      eps • pairSecantExteriorField mu q a b (physicalPairDirection q a b)=
      (eps*(mu a+mu b)/satelliteDistance q a b^3) • physicalPairDirection q a b := by
  have h := congrArg (fun z : Plane => (satelliteDistance q a b)⁻¹ • z)
    (physical_pair_vector_difference eps mu q a b hab hroot)
  rw [smul_add,physical_pair_primary_secant q a b hq hab] at h
  have hext : (satelliteDistance q a b)⁻¹ • eps •
      (pairExteriorField mu q a b (q b)-pairExteriorField mu q a b (q a))=
      eps • pairSecantExteriorField mu q a b (physicalPairDirection q a b) := by
    rw [smul_comm,physical_pair_exterior_secant mu q a b hq hab]
  rw [hext,smul_comm] at h
  exact h

theorem dividedNewtonTargetField_unit_diagonal (c v : Plane) (hc : ‖c‖=1) :
    v+dividedNewtonTargetField 0 c c v=(3*inner ℝ v c) • c := by
  simp only [dividedNewtonTargetField,dividedInverseCube,zero_sub,norm_neg,hc,
    smul_zero,sub_zero]
  norm_num
  rw [inner_add_right]
  module

theorem satellitesRelative_collisionFree (x : Configuration) (hx : CollisionFree x) :
    RelativeCollisionFree (satellitesRelative x) := by
  constructor
  · intro i
    exact sub_ne_zero.mpr (hx i.succ 0 (by simp))
  · intro i j hij
    change x i.succ-x 0≠x j.succ-x 0
    exact fun heq => hx i.succ j.succ (fun h => hij (Fin.succ_inj.mp h))
      (sub_left_inj.mp heq)

/-- Actual all-ratio unit-radius convergence along every normalized root
sequence. The proof invokes the already proved uniform radius threshold. -/
theorem dominant_satellite_radius_tendsto (eps : ℕ → ℝ) (mu : ℕ → MassRatio)
    (x : ℕ → Configuration) (heps : ∀ n,0<eps n)
    (hepst : Tendsto eps atTop (nhds 0)) (hm : ∀ n,PositiveRatio (mu n))
    (hx : ∀ n,NormalizedCentralConfiguration (masses (eps n) (mu n)) (x n))
    (i : Satellite) :
    Tendsto (fun n => ‖satellitesRelative (x n) i‖) atTop (nhds 1) := by
  apply Metric.tendsto_nhds.mpr
  intro eta heta
  obtain ⟨delta,hdelta,hbound⟩ := dominant_primary_relative_radii_uniform eta heta
  have hsmall := hepst.eventually (Iio_mem_nhds hdelta)
  filter_upwards [hsmall] with n hn
  rw [Real.dist_eq]
  exact hbound (eps n) (mu n) (x n) (heps n) hn (hm n) (hx n) i

def CompleteLimitingSatellitePair (q : SatelliteConfiguration) (a b : Satellite) (c : Plane) : Prop :=
  ∀ j,q j=c ↔ j=a ∨ j=b

theorem pairSecantExteriorField_joint_contDiffAt (a b : Satellite)
    (d : (MassRatio×SatelliteConfiguration)×Plane)
    (ha : ∀ j∈pairExteriorLabels a b,d.1.2 j≠d.1.2 a)
    (hb : ∀ j∈pairExteriorLabels a b,d.1.2 j≠d.1.2 b) :
    ContDiffAt ℝ ∞ (fun z : (MassRatio×SatelliteConfiguration)×Plane =>
      pairSecantExteriorField z.1.1 z.1.2 a b z.2) d := by
  unfold pairSecantExteriorField
  apply ContDiffAt.sum
  intro j hj
  have hargs : ContDiff ℝ ∞ (fun z : (MassRatio×SatelliteConfiguration)×Plane =>
      ((z.1.2 j,z.1.2 a),(z.1.2 b,z.2))) := by fun_prop
  have hD := (dividedNewtonTargetField_joint_contDiffAt ∞
    ((d.1.2 j,d.1.2 a),(d.1.2 b,d.2)) (ha j hj) (hb j hj)).comp d hargs.contDiffAt
  exact (by fun_prop : ContDiffAt ℝ ∞
    (fun z : (MassRatio×SatelliteConfiguration)×Plane => z.1.1 j) d).smul hD

/-- Every selected unit pair-direction limit of actual normalized roots is
radial with lambda tending to 3, or tangential with lambda tending to zero.
Here lambda=epsilon*(current pair mass)/d³. Its limit is DERIVED from the
actual equations; no boundedness or limiting value is assumed beforehand.
The limiting mass vector is allowed to have any number of zero entries. -/
theorem normalized_complete_pair_direction_alternative
    (eps : ℕ → ℝ) (mu : ℕ → MassRatio) (x : ℕ → Configuration)
    (heps : ∀ n,0<eps n) (hepst : Tendsto eps atTop (nhds 0))
    (hm : ∀ n,PositiveRatio (mu n))
    (hx : ∀ n,NormalizedCentralConfiguration (masses (eps n) (mu n)) (x n))
    (muLimit : MassRatio) (hmt : Tendsto mu atTop (nhds muLimit))
    (qLimit : SatelliteConfiguration)
    (hqt : Tendsto (fun n => satellitesRelative (x n)) atTop (nhds qLimit))
    (a b : Satellite) (hab : a≠b) (c : Plane)
    (hpair : CompleteLimitingSatellitePair qLimit a b c)
    (v : Plane)
    (hvt : Tendsto (fun n => physicalPairDirection (satellitesRelative (x n)) a b)
      atTop (nhds v)) :
    (Tendsto (fun n => eps n*(mu n a+mu n b)/satelliteDistance (satellitesRelative (x n)) a b^3)
      atTop (nhds 0) ∧ inner ℝ v c=0) ∨
    (Tendsto (fun n => eps n*(mu n a+mu n b)/satelliteDistance (satellitesRelative (x n)) a b^3)
      atTop (nhds 3) ∧ (v=c ∨ v= -c)) := by
  let q : ℕ → SatelliteConfiguration := fun n => satellitesRelative (x n)
  let vn : ℕ → Plane := fun n => physicalPairDirection (q n) a b
  let lambda : ℕ → ℝ := fun n => eps n*(mu n a+mu n b)/satelliteDistance (q n) a b^3
  have hqn (n : ℕ) : RelativeCollisionFree (q n) := satellitesRelative_collisionFree (x n) (hx n).1
  have hqa : qLimit a=c := (hpair a).mpr (Or.inl rfl)
  have hqb : qLimit b=c := (hpair b).mpr (Or.inr rfl)
  have hqat : Tendsto (fun n => q n a) atTop (nhds c) := by
    simpa only [q,hqa,Function.comp_def] using (continuous_apply a).tendsto qLimit |>.comp hqt
  have hqbt : Tendsto (fun n => q n b) atTop (nhds c) := by
    simpa only [q,hqb,Function.comp_def] using (continuous_apply b).tendsto qLimit |>.comp hqt
  have hc : ‖c‖=1 := tendsto_nhds_unique hqat.norm
    (dominant_satellite_radius_tendsto eps mu x heps hepst hm hx a)
  have hc0 : c≠0 := by intro heq; simp [heq] at hc
  have hnv (n : ℕ) : ‖vn n‖=1 := physicalPairDirection_norm (q n) a b ((hqn n).2 a b hab)
  have hvt' : Tendsto vn atTop (nhds v) := hvt
  have hsep (j : Satellite) (hj : j∈pairExteriorLabels a b) : qLimit j≠c := by
    have hja : j≠a := (Finset.mem_erase.mp (Finset.mem_erase.mp hj).2).1
    have hjb : j≠b := (Finset.mem_erase.mp hj).1
    exact fun h => ((hpair j).mp h).elim hja hjb
  have hDt : Tendsto (fun n => dividedNewtonTargetField 0 (q n a) (q n b) (vn n)) atTop
      (nhds (dividedNewtonTargetField 0 c c v)) := by
    have hd := (dividedNewtonTargetField_joint_contDiffAt ∞ ((0,c),(c,v))
      (Ne.symm hc0) (Ne.symm hc0)).continuousAt.tendsto
    simpa only [Function.comp_def] using hd.comp
      ((tendsto_const_nhds.prodMk_nhds hqat).prodMk_nhds (hqbt.prodMk_nhds hvt'))
  have hPt : Tendsto (fun n => pairSecantExteriorField (mu n) (q n) a b (vn n)) atTop
      (nhds (pairSecantExteriorField muLimit qLimit a b v)) := by
    have hp := (pairSecantExteriorField_joint_contDiffAt a b ((muLimit,qLimit),v)
      (by intro j hj; simpa only [hqa] using hsep j hj)
      (by intro j hj; simpa only [hqb] using hsep j hj)).continuousAt.tendsto
    simpa only [Function.comp_def,q] using hp.comp ((hmt.prodMk_nhds hqt).prodMk_nhds hvt')
  let lhs : ℕ → Plane := fun n => vn n+dividedNewtonTargetField 0 (q n a) (q n b) (vn n)+
    eps n • pairSecantExteriorField (mu n) (q n) a b (vn n)
  have hrow (n : ℕ) : lhs n=lambda n • vn n := physical_pair_direction_equation (eps n)
    (mu n) (q n) a b (hqn n) hab (vectorResidual_zero_of_normalized (eps n) (mu n) (x n) (hx n))
  have hlt : Tendsto lhs atTop (nhds ((3*inner ℝ v c) • c)) := by
    simpa only [lhs,zero_smul,add_zero,dividedNewtonTargetField_unit_diagonal c v hc]
      using (hvt'.add hDt).add (hepst.smul hPt)
  have hli (n : ℕ) : inner ℝ (lhs n) (vn n)=lambda n := by
    rw [hrow,real_inner_smul_left,real_inner_self_eq_norm_sq,hnv]
    ring
  have hlat : Tendsto lambda atTop (nhds (3*(inner ℝ v c)^2)) := by
    have ht := hlt.inner (𝕜 := ℝ) hvt'
    simpa only [hli,real_inner_smul_left,real_inner_comm c v,pow_two,mul_assoc] using ht
  have heigen : (3*inner ℝ v c) • c=(3*(inner ℝ v c)^2) • v := by
    have heq : lhs=(fun n => lambda n • vn n) := funext hrow
    exact tendsto_nhds_unique hlt (by rw [heq]; exact hlat.smul hvt')
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

def primaryRadialScalar (rho : ℝ) : ℝ := rho-(rho^2)⁻¹

theorem primaryRadialField_polar_inner (rho theta psi : ℝ) (hr : 0<rho) :
    inner ℝ (primaryRadialField (polarPoint rho theta)) (polarPoint 1 psi)=
      primaryRadialScalar rho*Real.cos (theta-psi) := by
  unfold primaryRadialField primaryRadialScalar
  rw [inner_sub_left,real_inner_smul_left,polarPoint_inner_radial,
    polarPoint_norm,abs_of_pos hr]
  have hi : rho*(rho^3)⁻¹=(rho^2)⁻¹ := by field_simp [ne_of_gt hr]
  linear_combination -Real.cos (theta-psi)*hi

/-- Exact source `eq:midpoint` from the actual vector rows. Its coefficient
is retained without dividing by the radial difference, so equal radii and
zero limiting pair fractions are covered. -/
theorem physical_pair_midpoint_identity (eps : ℝ) (mu r theta : Satellite → ℝ)
    (a b : Satellite) (hab : a≠b) (hr : ∀ i,0<r i)
    (hroot : ∀ i,vectorResidual eps mu (polarSatellites r theta) i=0) :
    (primaryRadialScalar (r b)-primaryRadialScalar (r a)-
      (eps*(mu a+mu b)/satelliteDistance (polarSatellites r theta) a b^3)*(r b-r a))*
      Real.cos ((theta b-theta a)/2)=
    -eps*inner ℝ
      (pairExteriorField mu (polarSatellites r theta) a b (polarPoint (r b) (theta b))-
        pairExteriorField mu (polarSatellites r theta) a b (polarPoint (r a) (theta a)))
      (polarPoint 1 ((theta a+theta b)/2)) := by
  have h := congrArg (fun z : Plane => inner ℝ z (polarPoint 1 ((theta a+theta b)/2)))
    (physical_pair_vector_difference eps mu (polarSatellites r theta) a b hab hroot)
  have hca : Real.cos (theta a-(theta a+theta b)/2)=Real.cos ((theta b-theta a)/2) := by
    rw [show theta a-(theta a+theta b)/2= -((theta b-theta a)/2) by ring,Real.cos_neg]
  have hcb : Real.cos (theta b-(theta a+theta b)/2)=Real.cos ((theta b-theta a)/2) :=
    congrArg Real.cos (by ring)
  simp only [inner_add_left,inner_sub_left,real_inner_smul_left,polarSatellites,
    primaryRadialField_polar_inner _ _ _ (hr b),primaryRadialField_polar_inner _ _ _ (hr a),
    polarPoint_inner_radial,hca,hcb] at h ⊢
  linarith

theorem normalized_pair_midpoint_identity (eps : ℝ) (mu : MassRatio)
    (x : Configuration) (hx : NormalizedCentralConfiguration (masses eps mu) x)
    (r theta : Satellite → ℝ) (hr : ∀ i,0<r i)
    (hpolar : satellitesRelative x=polarSatellites r theta)
    (a b : Satellite) (hab : a≠b) :
    (primaryRadialScalar (r b)-primaryRadialScalar (r a)-
      (eps*(mu a+mu b)/satelliteDistance (polarSatellites r theta) a b^3)*(r b-r a))*
      Real.cos ((theta b-theta a)/2)=
    -eps*inner ℝ
      (pairExteriorField mu (polarSatellites r theta) a b (polarPoint (r b) (theta b))-
        pairExteriorField mu (polarSatellites r theta) a b (polarPoint (r a) (theta a)))
      (polarPoint 1 ((theta a+theta b)/2)) := by
  apply physical_pair_midpoint_identity eps mu r theta a b hab hr
  rw [← hpolar]
  exact vectorResidual_zero_of_normalized eps mu x hx

/-- Exact uniformly invertible radial coefficient used after the tangential
alternative lambda→0. No division by rb-ra appears in this identity. -/
theorem primaryRadialScalar_difference (ra rb lambda : ℝ) (ha : ra≠0) (hb : rb≠0) :
    primaryRadialScalar rb-primaryRadialScalar ra-lambda*(rb-ra)=
      (rb-ra)*(1+(ra+rb)/(ra^2*rb^2)-lambda) := by
  unfold primaryRadialScalar
  field_simp [ha,hb]
  ring

theorem pairExteriorMass_eq (mu : MassRatio) (a b : Satellite) (hab : a≠b)
    (hsum : ∑ i,mu i=1) :
    (∑ j∈pairExteriorLabels a b,mu j)=1-(mu a+mu b) := by
  have hb : b∈Finset.univ.erase a := Finset.mem_erase.mpr ⟨Ne.symm hab,Finset.mem_univ b⟩
  have h1 := Finset.sum_erase_add Finset.univ mu (Finset.mem_univ a)
  have h2 := Finset.sum_erase_add (Finset.univ.erase a) mu hb
  rw [hsum] at h1
  change (∑ j∈pairExteriorLabels a b,mu j)+mu b=∑ j∈Finset.univ.erase a,mu j at h2
  linarith

theorem physicalNewtonTargetField_joint_contDiffAt (source target : Plane) (hsep : source≠target) :
    ContDiffAt ℝ ∞ (fun z : Plane×Plane => newtonTargetField z.1 z.2) (source,target) := by
  have hv : ContDiffAt ℝ ∞ (fun z : Plane×Plane => z.1-z.2) (source,target) := by fun_prop
  have hn := hv.norm ℝ (sub_ne_zero.mpr hsep)
  have hd : ‖source-target‖^3≠0 := pow_ne_zero 3 (norm_ne_zero_iff.mpr (sub_ne_zero.mpr hsep))
  exact ((hn.pow 3).inv hd).smul hv

/-- Current-mass exterior error bound C*sigma*d for a complete pair.
It is obtained separately for each separated source and then summed with
the CURRENT masses. Neither sigma nor the pair fractions have a mass floor;
no convergence of the current mass ratios is needed. -/
theorem complete_pair_exterior_error_bound
    (mu : ℕ → MassRatio) (q : ℕ → SatelliteConfiguration)
    (hm : ∀ n,PositiveRatio (mu n)) (qLimit : SatelliteConfiguration)
    (hqt : Tendsto q atTop (nhds qLimit)) (a b : Satellite) (hab : a≠b)
    (c : Plane) (hpair : CompleteLimitingSatellitePair qLimit a b c) :
    ∃ C : ℝ,0<C ∧ ∀ᶠ n in atTop,
      ‖pairExteriorField (mu n) (q n) a b (q n b)-pairExteriorField (mu n) (q n) a b (q n a)‖≤
        C*(1-(mu n a+mu n b))*satelliteDistance (q n) a b := by
  have hqa : qLimit a=c := (hpair a).mpr (Or.inl rfl)
  have hqb : qLimit b=c := (hpair b).mpr (Or.inr rfl)
  have hqat : Tendsto (fun n => q n a) atTop (nhds c) := by
    simpa only [Function.comp_def,hqa] using (continuous_apply a).tendsto qLimit |>.comp hqt
  have hqbt : Tendsto (fun n => q n b) atTop (nhds c) := by
    simpa only [Function.comp_def,hqb] using (continuous_apply b).tendsto qLimit |>.comp hqt
  have hw (j : Satellite) : ∃ K : ℝ,0<K ∧ ∀ᶠ n in atTop,
      j∈pairExteriorLabels a b →
      ‖newtonTargetField (q n j) (q n b)-newtonTargetField (q n j) (q n a)‖≤
        K*satelliteDistance (q n) a b := by
    by_cases hj : j∈pairExteriorLabels a b
    · have hsep : qLimit j≠c := by
        have hja : j≠a := (Finset.mem_erase.mp (Finset.mem_erase.mp hj).2).1
        have hjb : j≠b := (Finset.mem_erase.mp hj).1
        exact fun h => ((hpair j).mp h).elim hja hjb
      obtain ⟨K,U,hU,hLip⟩ := ((physicalNewtonTargetField_joint_contDiffAt (qLimit j) c hsep).of_le
        (by norm_num : (1 : ℕ∞ω)≤∞)).exists_lipschitzOnWith
      have hsource : Tendsto (fun n => q n j) atTop (nhds (qLimit j)) := by
        simpa only [Function.comp_def] using (continuous_apply j).tendsto qLimit |>.comp hqt
      have hUa := (hsource.prodMk_nhds hqat).eventually hU
      have hUb := (hsource.prodMk_nhds hqbt).eventually hU
      refine ⟨(K : ℝ)+1,by positivity,?_⟩
      filter_upwards [hUa,hUb] with n hna hnb _
      have hbound := hLip.dist_le_mul (q n j,q n b) hnb (q n j,q n a) hna
      have hd : dist (q n j,q n b) (q n j,q n a)=satelliteDistance (q n) a b := by
        rw [Prod.dist_eq,dist_self,max_eq_right (dist_nonneg),dist_eq_norm,norm_sub_rev]
        rfl
      rw [hd,dist_eq_norm] at hbound
      exact hbound.trans (mul_le_mul_of_nonneg_right (by linarith : (K : ℝ)≤(K : ℝ)+1)
        (norm_nonneg _))
    · exact ⟨1,by norm_num,Filter.Eventually.of_forall (fun _ h => (hj h).elim)⟩
  choose K hK hbound using hw
  let C : ℝ := (∑ j∈pairExteriorLabels a b,K j)+1
  have hsumK : 0≤∑ j∈pairExteriorLabels a b,K j :=
    Finset.sum_nonneg (fun j _ => (hK j).le)
  have hC : 0<C := by dsimp [C]; linarith
  have heach : ∀ᶠ n in atTop,∀ j∈pairExteriorLabels a b,
      ‖newtonTargetField (q n j) (q n b)-newtonTargetField (q n j) (q n a)‖≤
        K j*satelliteDistance (q n) a b := by
    apply (Finset.eventually_all (pairExteriorLabels a b)).mpr
    intro j hj
    exact (hbound j).mono (fun _ h => h hj)
  refine ⟨C,hC,?_⟩
  filter_upwards [heach] with n hn
  rw [pairExteriorField_eq_newton_sum,pairExteriorField_eq_newton_sum,← Finset.sum_sub_distrib]
  simp only [← smul_sub]
  calc
    ‖∑ j∈pairExteriorLabels a b,mu n j •
        (newtonTargetField (q n j) (q n b)-newtonTargetField (q n j) (q n a))‖
        ≤∑ j∈pairExteriorLabels a b,mu n j*
          ‖newtonTargetField (q n j) (q n b)-newtonTargetField (q n j) (q n a)‖ := by
      refine (norm_sum_le _ _).trans_eq ?_
      apply Finset.sum_congr rfl
      intro j _
      rw [norm_smul,Real.norm_eq_abs,abs_of_pos ((hm n).1 j)]
    _≤∑ j∈pairExteriorLabels a b,mu n j*(C*satelliteDistance (q n) a b) := by
      apply Finset.sum_le_sum
      intro j hj
      have hjK : K j≤C := by
        have hi := Finset.single_le_sum (fun l _ => (hK l).le) hj
        dsimp [C]
        linarith
      exact mul_le_mul_of_nonneg_left ((hn j hj).trans
        (mul_le_mul_of_nonneg_right hjK (norm_nonneg _))) ((hm n).1 j).le
    _=C*(1-(mu n a+mu n b))*satelliteDistance (q n) a b := by
      rw [← Finset.sum_mul,pairExteriorMass_eq (mu n) a b hab (hm n).2]
      ring

/-- Quantitative radial estimate from the actual midpoint identity whenever
the derived tangential coefficient is small. The exterior error contains
the current total exterior mass sigma, including arbitrarily small sigma. -/
theorem physical_pair_radial_bound (eps C : ℝ) (mu r theta : Satellite → ℝ)
    (a b : Satellite) (hab : a≠b) (hr : ∀ i,0<r i) (heps : 0≤eps)
    (hroot : ∀ i,vectorResidual eps mu (polarSatellites r theta) i=0)
    (hlambda : eps*(mu a+mu b)/satelliteDistance (polarSatellites r theta) a b^3≤1/2)
    (hcos : 1/2≤Real.cos ((theta b-theta a)/2))
    (hP : ‖pairExteriorField mu (polarSatellites r theta) a b (polarPoint (r b) (theta b))-
      pairExteriorField mu (polarSatellites r theta) a b (polarPoint (r a) (theta a))‖≤
        C*(1-(mu a+mu b))*satelliteDistance (polarSatellites r theta) a b) :
    |r b-r a|≤4*C*eps*(1-(mu a+mu b))*satelliteDistance (polarSatellites r theta) a b := by
  let lambda : ℝ := eps*(mu a+mu b)/satelliteDistance (polarSatellites r theta) a b^3
  let A : ℝ := 1+(r a+r b)/(r a^2*r b^2)-lambda
  have hA : 1/2≤A := by
    have hpositive : 0<(r a+r b)/(r a^2*r b^2) := div_pos (add_pos (hr a) (hr b))
      (mul_pos (sq_pos_of_pos (hr a)) (sq_pos_of_pos (hr b)))
    dsimp [A,lambda]
    linarith
  have hmid := physical_pair_midpoint_identity eps mu r theta a b hab hr hroot
  rw [primaryRadialScalar_difference (r a) (r b) lambda (ne_of_gt (hr a)) (ne_of_gt (hr b))] at hmid
  change (r b-r a)*A*Real.cos ((theta b-theta a)/2)=_ at hmid
  have hbound := congrArg abs hmid
  rw [abs_mul,abs_mul,abs_of_nonneg (show 0≤A by linarith),
    abs_of_nonneg (show 0≤Real.cos ((theta b-theta a)/2) by linarith),
    abs_mul,abs_neg,abs_of_nonneg heps] at hbound
  have hinner := abs_real_inner_le_norm
    (pairExteriorField mu (polarSatellites r theta) a b (polarPoint (r b) (theta b))-
      pairExteriorField mu (polarSatellites r theta) a b (polarPoint (r a) (theta a)))
    (polarPoint 1 ((theta a+theta b)/2))
  rw [polarPoint_norm,abs_one,mul_one] at hinner
  have hupper := mul_le_mul_of_nonneg_left (hinner.trans hP) heps
  have hlower : |r b-r a|/4≤|r b-r a| * A*Real.cos ((theta b-theta a)/2) := by
    have h1 := mul_le_mul_of_nonneg_left hA (abs_nonneg (r b-r a))
    have h2 := mul_le_mul_of_nonneg_left hcos
      (mul_nonneg (abs_nonneg (r b-r a)) (by linarith : 0≤A))
    nlinarith
  rw [← hbound] at hupper
  nlinarith

/-- Proposition 4.2's precise radial estimate on a selected tangential
complete-pair sequence. The two limiting facts in the hypotheses specify
the selected branch; the constant and actual C*epsilon*sigma*d estimate
are proved from its physical equations, not supplied by a chart. -/
theorem normalized_complete_pair_radial_bound_of_tangential
    (eps : ℕ → ℝ) (mu : ℕ → MassRatio) (x : ℕ → Configuration)
    (heps : ∀ n,0<eps n) (hm : ∀ n,PositiveRatio (mu n))
    (hx : ∀ n,NormalizedCentralConfiguration (masses (eps n) (mu n)) (x n))
    (r theta : ℕ → Satellite → ℝ) (hr : ∀ n,∀ i,0<r n i)
    (hpolar : ∀ n,satellitesRelative (x n)=polarSatellites (r n) (theta n))
    (qLimit : SatelliteConfiguration)
    (hqt : Tendsto (fun n => satellitesRelative (x n)) atTop (nhds qLimit))
    (a b : Satellite) (hab : a≠b) (c : Plane)
    (hpair : CompleteLimitingSatellitePair qLimit a b c)
    (hlambda : Tendsto
      (fun n => eps n*(mu n a+mu n b)/satelliteDistance (satellitesRelative (x n)) a b^3)
      atTop (nhds 0))
    (hgap : Tendsto (fun n => theta n b-theta n a) atTop (nhds 0)) :
    ∃ C : ℝ,0<C ∧ ∀ᶠ n in atTop,
      |r n b-r n a|≤C*eps n*(1-(mu n a+mu n b))*satelliteDistance (satellitesRelative (x n)) a b := by
  obtain ⟨K,hK,hP⟩ := complete_pair_exterior_error_bound mu
    (fun n => satellitesRelative (x n)) hm qLimit hqt a b hab c hpair
  have hlambdasmall := hlambda.eventually (Iio_mem_nhds (by norm_num : (0 : ℝ)<1/2))
  have hcos : Tendsto (fun n => Real.cos ((theta n b-theta n a)/2)) atTop (nhds 1) := by
    simpa only [zero_div,Real.cos_zero,Function.comp_def] using
      Real.continuous_cos.continuousAt.tendsto.comp (hgap.div_const 2)
  have hcossmall := hcos.eventually (Ioi_mem_nhds (by norm_num : (1/2 : ℝ)<1))
  refine ⟨4*K,by positivity,?_⟩
  filter_upwards [hP,hlambdasmall,hcossmall] with n hn hln hcn
  have hroot : ∀ i,vectorResidual (eps n) (mu n) (polarSatellites (r n) (theta n)) i=0 := by
    rw [← hpolar n]
    exact vectorResidual_zero_of_normalized (eps n) (mu n) (x n) (hx n)
  rw [hpolar n] at hn hln ⊢
  exact physical_pair_radial_bound (eps n) K (mu n) (r n) (theta n) a b hab (hr n)
    (heps n).le hroot hln.le hcn.le hn

theorem complete_pair_distance_tendsto_zero
    (q : ℕ → SatelliteConfiguration) (qLimit : SatelliteConfiguration)
    (hqt : Tendsto q atTop (nhds qLimit)) (a b : Satellite) (c : Plane)
    (hpair : CompleteLimitingSatellitePair qLimit a b c) :
    Tendsto (fun n => satelliteDistance (q n) a b) atTop (nhds 0) := by
  have ha : qLimit a=c := (hpair a).mpr (Or.inl rfl)
  have hb : qLimit b=c := (hpair b).mpr (Or.inr rfl)
  simpa only [Function.comp_def,ha,hb,sub_self,norm_zero,satelliteDistance] using
    (((continuous_apply a).tendsto qLimit |>.comp hqt).sub
      ((continuous_apply b).tendsto qLimit |>.comp hqt)).norm

theorem pairTangentialCoefficient_pos (mu r theta : Satellite → ℝ)
    (a b : Satellite) (hm : ∀ i,0<mu i) (hr : ∀ i,0<r i)
    (hd : 0<satelliteDistance (polarSatellites r theta) a b)
    (hda : satelliteDistance (polarSatellites r theta) a b<r a)
    (hdb : satelliteDistance (polarSatellites r theta) a b<r b) :
    0<(mu a*r a+mu b*r b)/satelliteDistance (polarSatellites r theta) a b^3-
      mu a/(r a)^2-mu b/(r b)^2 := by
  let d : ℝ := satelliteDistance (polarSatellites r theta) a b
  have hpowA : d^3<(r a)^3 := pow_lt_pow_left₀ hda hd.le (by decide : (3 : ℕ)≠0)
  have hpowB : d^3<(r b)^3 := pow_lt_pow_left₀ hdb hd.le (by decide : (3 : ℕ)≠0)
  have hia : r a/(r a)^3=1/(r a)^2 := by field_simp [ne_of_gt (hr a)]
  have hib : r b/(r b)^3=1/(r b)^2 := by field_simp [ne_of_gt (hr b)]
  have hca : 0<r a/d^3-1/(r a)^2 := by
    have h := div_lt_div_of_pos_left (hr a) (pow_pos hd 3) hpowA
    rw [hia] at h
    linarith
  have hcb : 0<r b/d^3-1/(r b)^2 := by
    have h := div_lt_div_of_pos_left (hr b) (pow_pos hd 3) hpowB
    rw [hib] at h
    linarith
  have ha := mul_pos (hm a) hca
  have hb := mul_pos (hm b) hcb
  change 0<(mu a*r a+mu b*r b)/d^3-mu a/(r a)^2-mu b/(r b)^2
  have heq : (mu a*r a+mu b*r b)/d^3-mu a/(r a)^2-mu b/(r b)^2=
      mu a*(r a/d^3-1/(r a)^2)+mu b*(r b/d^3-1/(r b)^2) := by ring
  rw [heq]
  exact add_pos ha hb

/-- The positive sign in `eq:pair-qdiff` is derived on every sufficiently
late actual complete-pair sequence from positive CURRENT masses, unit
radii, actual distance tending to zero and the original ordered polar
angles. No positive limiting pair share or exterior share is required. -/
theorem normalized_complete_pair_tangential_difference_positive
    (eps : ℕ → ℝ) (mu : ℕ → MassRatio) (x : ℕ → Configuration)
    (heps : ∀ n,0<eps n) (hepst : Tendsto eps atTop (nhds 0))
    (hm : ∀ n,PositiveRatio (mu n))
    (hx : ∀ n,NormalizedCentralConfiguration (masses (eps n) (mu n)) (x n))
    (r theta : ℕ → Satellite → ℝ) (hr : ∀ n,∀ i,0<r n i)
    (hpolar : ∀ n,satellitesRelative (x n)=polarSatellites (r n) (theta n))
    (horder : ∀ n,∀ i j,i<j → 0<theta n j-theta n i ∧ theta n j-theta n i<Real.pi)
    (qLimit : SatelliteConfiguration)
    (hqt : Tendsto (fun n => satellitesRelative (x n)) atTop (nhds qLimit))
    (a b : Satellite) (hab : a<b) (c : Plane)
    (hpair : CompleteLimitingSatellitePair qLimit a b c) :
    ∀ᶠ n in atTop,
      physicalPairExteriorAngularField (mu n) (r n) (theta n) a b (r n b) (theta n b)-
        physicalPairExteriorAngularField (mu n) (r n) (theta n) a b (r n a) (theta n a)=
      Real.sin (theta n b-theta n a)*
        ((mu n a*r n a+mu n b*r n b)/satelliteDistance (polarSatellites (r n) (theta n)) a b^3-
          mu n a/(r n a)^2-mu n b/(r n b)^2) ∧
      0<physicalPairExteriorAngularField (mu n) (r n) (theta n) a b (r n b) (theta n b)-
        physicalPairExteriorAngularField (mu n) (r n) (theta n) a b (r n a) (theta n a) := by
  have hrat (i : Satellite) : Tendsto (fun n => r n i) atTop (nhds 1) := by
    have hn (n : ℕ) : ‖satellitesRelative (x n) i‖=r n i := by
      rw [hpolar n]
      exact (polarPoint_norm _ _).trans (abs_of_pos (hr n i))
    simpa only [hn] using dominant_satellite_radius_tendsto eps mu x heps hepst hm hx i
  have hdist := complete_pair_distance_tendsto_zero
    (fun n => satellitesRelative (x n)) qLimit hqt a b c hpair
  have hra := (hrat a).eventually (Ioi_mem_nhds (by norm_num : (1/2 : ℝ)<1))
  have hrb := (hrat b).eventually (Ioi_mem_nhds (by norm_num : (1/2 : ℝ)<1))
  have hsmall := hdist.eventually (Iio_mem_nhds (by norm_num : (0 : ℝ)<1/2))
  filter_upwards [hra,hrb,hsmall] with n hna hnb hnd
  have heq := normalized_pair_tangential_difference (eps n) (mu n) (x n) (hx n)
    (ne_of_gt (heps n)) (r n) (theta n) (hr n) (hpolar n) a b (ne_of_lt hab)
  refine ⟨heq,?_⟩
  rw [heq]
  apply mul_pos (Real.sin_pos_of_pos_of_lt_pi (horder n a b hab).1 (horder n a b hab).2)
  have hd : 0<satelliteDistance (polarSatellites (r n) (theta n)) a b := by
    rw [← hpolar n]
    exact norm_pos_iff.mpr (sub_ne_zero.mpr
      ((satellitesRelative_collisionFree (x n) (hx n).1).2 a b (ne_of_lt hab)))
  rw [hpolar n] at hnd
  exact pairTangentialCoefficient_pos (mu n) (r n) (theta n) a b (hm n).1 (hr n) hd
    (by linarith) (by linarith)

def physicalSourceAngularField (s angle rho v : ℝ) : ℝ :=
  s*Real.sin (angle-v)*((‖polarPoint rho v-polarPoint s angle‖^3)⁻¹-(s^3)⁻¹)

def physicalSourceAngularRadialDerivative (s angle rho v : ℝ) : ℝ :=
  -3*s*Real.sin (angle-v)*(rho-s*Real.cos (angle-v))*
    (‖polarPoint rho v-polarPoint s angle‖^5)⁻¹

theorem physicalSourceAngularField_eq_cartesian (s angle rho v : ℝ) (hs : 0<s) :
    physicalSourceAngularField s angle rho v=
      inner ℝ (newtonTargetField (polarPoint s angle) (polarPoint rho v)-
        (‖polarPoint s angle‖^3)⁻¹ • polarPoint s angle) (quarterTurn (polarPoint 1 v)) := by
  unfold physicalSourceAngularField newtonTargetField
  simp only [inner_sub_left,real_inner_smul_left,polarPoint_inner_rotation,
    sub_self,Real.sin_zero,mul_zero,sub_zero,one_mul]
  rw [polarPoint_norm,abs_of_pos hs,norm_sub_rev (polarPoint s angle)]
  ring

/-- The radial derivative used in the endpoint radial-branch exclusion is
the actual derivative of the physical one-source angular field. All source
and target coordinates are retained; no limiting-mass assumption is used. -/
theorem physicalSourceAngularField_hasDerivAt_radius (s angle rho v : ℝ)
    (hs : 0<s) (hsep : polarPoint s angle≠polarPoint rho v) :
    HasDerivAt (fun r : ℝ => physicalSourceAngularField s angle r v)
      (physicalSourceAngularRadialDerivative s angle rho v) rho := by
  have hparam : HasDerivAt (fun r : ℝ => (r,v)) (1,0) rho :=
    (hasDerivAt_id rho).prodMk (hasDerivAt_const rho v)
  have hp : HasDerivAt (fun r : ℝ => polarPoint r v) (polarPoint 1 v) rho := by
    convert! (polarPoint_hasFDerivAt (rho,v)).comp_hasDerivAt rho hparam using 1
    simp [polarPointDerivative_apply]
  have hF := (newtonTargetField_hasFDerivAt (polarPoint s angle) (polarPoint rho v) hsep).comp_hasDerivAt rho hp
  have h := (hF.sub_const ((‖polarPoint s angle‖^3)⁻¹ • polarPoint s angle)).inner ℝ
    (hasDerivAt_const rho (quarterTurn (polarPoint 1 v)))
  convert! h using 1
  · funext r
    exact physicalSourceAngularField_eq_cartesian s angle r v hs
  · simp only [inner_zero_right,newtonTargetDerivative_apply,
      inner_sub_left,real_inner_smul_left,polarPoint_inner_radial,
      polarPoint_inner_rotation,sub_self,Real.sin_zero,Real.cos_zero,one_mul,
      mul_zero,sub_zero,mul_one]
    unfold physicalSourceAngularRadialDerivative
    rw [norm_sub_rev (polarPoint s angle)]
    simp only [div_eq_mul_inv]
    ring

theorem physicalSourceAngularRadialDerivative_joint_contDiffAt
    (d : (ℝ×ℝ)×(ℝ×ℝ))
    (hsep : polarPoint d.1.1 d.1.2≠polarPoint d.2.1 d.2.2) :
    ContDiffAt ℝ ∞ (fun z : (ℝ×ℝ)×(ℝ×ℝ) =>
      physicalSourceAngularRadialDerivative z.1.1 z.1.2 z.2.1 z.2.2) d := by
  have hsource : ContDiff ℝ ∞ (fun z : (ℝ×ℝ)×(ℝ×ℝ) => polarPoint z.1.1 z.1.2) :=
    (polarPoint_contDiff ∞).comp contDiff_fst
  have htarget : ContDiff ℝ ∞ (fun z : (ℝ×ℝ)×(ℝ×ℝ) => polarPoint z.2.1 z.2.2) :=
    (polarPoint_contDiff ∞).comp contDiff_snd
  have hn := (htarget.contDiffAt.sub hsource.contDiffAt).norm ℝ
    (sub_ne_zero.mpr (Ne.symm hsep))
  have hd : ‖polarPoint d.2.1 d.2.2-polarPoint d.1.1 d.1.2‖^5≠0 :=
    pow_ne_zero 5 (norm_ne_zero_iff.mpr (sub_ne_zero.mpr (Ne.symm hsep)))
  unfold physicalSourceAngularRadialDerivative
  apply ContDiffAt.mul
  · fun_prop
  · exact (hn.pow 5).inv hd

theorem physicalPairExteriorAngularField_hasDerivAt_radius
    (mu r theta : Satellite → ℝ) (a b : Satellite) (rho v : ℝ)
    (hr : ∀ i,0<r i)
    (hsep : ∀ j∈pairExteriorLabels a b,polarPoint (r j) (theta j)≠polarPoint rho v) :
    HasDerivAt (fun s : ℝ => physicalPairExteriorAngularField mu r theta a b s v)
      (∑ j∈pairExteriorLabels a b,mu j*physicalSourceAngularRadialDerivative (r j) (theta j) rho v)
      rho := by
  have h := HasDerivAt.sum (u := pairExteriorLabels a b) (fun j hj =>
    (physicalSourceAngularField_hasDerivAt_radius (r j) (theta j) rho v (hr j) (hsep j hj)).const_mul (mu j))
  convert! h using 1
  funext s
  unfold physicalPairExteriorAngularField physicalSourceAngularField
  simp only [Finset.sum_apply]
  apply Finset.sum_congr rfl
  intro j _
  ring

theorem physicalSourceAngularRadialDerivative_unit_neg (angle v : ℝ)
    (ha : 0<angle-v) (hb : angle-v<Real.pi) :
    physicalSourceAngularRadialDerivative 1 angle 1 v<0 := by
  have hs := Real.sin_pos_of_pos_of_lt_pi ha hb
  have hc : 0<1-Real.cos (angle-v) := by
    nlinarith [Real.sin_sq_add_cos_sq (angle-v),sq_pos_of_pos hs]
  have hdist : 0<‖polarPoint 1 v-polarPoint 1 angle‖ := by
    rw [norm_sub_rev]
    exact polar_distance_pos 1 1 v angle (by norm_num) (by norm_num) ⟨ha,hb⟩
  unfold physicalSourceAngularRadialDerivative
  have hp : 0<3*Real.sin (angle-v)*(1-Real.cos (angle-v))*
      (‖polarPoint 1 v-polarPoint 1 angle‖^5)⁻¹ := by positivity
  simp only [mul_one,one_mul]
  rw [show -3*Real.sin (angle-v)*(1-Real.cos (angle-v))*
      (‖polarPoint 1 v-polarPoint 1 angle‖^5)⁻¹=
    -(3*Real.sin (angle-v)*(1-Real.cos (angle-v))*
      (‖polarPoint 1 v-polarPoint 1 angle‖^5)⁻¹) by ring]
  exact neg_neg_of_pos hp

theorem physicalSourceAngularRadialDerivative_unit_pos (angle v : ℝ)
    (ha : -Real.pi<angle-v) (hb : angle-v<0) :
    0<physicalSourceAngularRadialDerivative 1 angle 1 v := by
  have hs : Real.sin (angle-v)<0 := by
    have hp := Real.sin_pos_of_pos_of_lt_pi (show 0< -(angle-v) by linarith)
      (show -(angle-v)<Real.pi by linarith)
    rw [Real.sin_neg] at hp
    linarith
  have hc : 0<1-Real.cos (angle-v) := by
    nlinarith [Real.sin_sq_add_cos_sq (angle-v),sq_pos_of_ne_zero (ne_of_lt hs)]
  have hdist : 0<‖polarPoint 1 v-polarPoint 1 angle‖ :=
    polar_distance_pos 1 1 angle v (by norm_num) (by norm_num) ⟨by linarith,by linarith⟩
  unfold physicalSourceAngularRadialDerivative
  have hp : 0<3*(-Real.sin (angle-v))*(1-Real.cos (angle-v))*
      (‖polarPoint 1 v-polarPoint 1 angle‖^5)⁻¹ :=
    mul_pos (mul_pos (mul_pos (by norm_num) (neg_pos.mpr hs)) hc)
      (inv_pos.mpr (pow_pos hdist 5))
  simp only [mul_one,one_mul]
  have heq : -3*Real.sin (angle-v)*(1-Real.cos (angle-v))*
      (‖polarPoint 1 v-polarPoint 1 angle‖^5)⁻¹=
    3*(-Real.sin (angle-v))*(1-Real.cos (angle-v))*
      (‖polarPoint 1 v-polarPoint 1 angle‖^5)⁻¹ := by ring
  rw [heq]
  exact hp

theorem physicalSourceAngularField_joint_contDiffAt
    (d : (ℝ×ℝ)×(ℝ×ℝ)) (hs : d.1.1≠0)
    (hsep : polarPoint d.1.1 d.1.2≠polarPoint d.2.1 d.2.2) :
    ContDiffAt ℝ ∞ (fun z : (ℝ×ℝ)×(ℝ×ℝ) =>
      physicalSourceAngularField z.1.1 z.1.2 z.2.1 z.2.2) d := by
  have hsource : ContDiff ℝ ∞ (fun z : (ℝ×ℝ)×(ℝ×ℝ) => polarPoint z.1.1 z.1.2) :=
    (polarPoint_contDiff ∞).comp contDiff_fst
  have htarget : ContDiff ℝ ∞ (fun z : (ℝ×ℝ)×(ℝ×ℝ) => polarPoint z.2.1 z.2.2) :=
    (polarPoint_contDiff ∞).comp contDiff_snd
  have hn := (htarget.contDiffAt.sub hsource.contDiffAt).norm ℝ
    (sub_ne_zero.mpr (Ne.symm hsep))
  have hd : ‖polarPoint d.2.1 d.2.2-polarPoint d.1.1 d.1.2‖^3≠0 :=
    pow_ne_zero 3 (norm_ne_zero_iff.mpr (sub_ne_zero.mpr (Ne.symm hsep)))
  have hsr : ContDiffAt ℝ ∞ (fun z : (ℝ×ℝ)×(ℝ×ℝ) => (z.1.1^3)⁻¹) d :=
    (by fun_prop : ContDiffAt ℝ ∞ (fun z : (ℝ×ℝ)×(ℝ×ℝ) => z.1.1^3) d).inv
      (pow_ne_zero 3 hs)
  unfold physicalSourceAngularField
  exact (by fun_prop : ContDiffAt ℝ ∞ (fun z : (ℝ×ℝ)×(ℝ×ℝ) =>
    z.1.1*Real.sin (z.1.2-z.2.2)) d).mul (((hn.pow 3).inv hd).sub hsr)

/-- The endpoint derivative sign persists on an independent source/target
rectangle. Its constant is chosen before any current satellite masses. -/
theorem physicalSourceAngularRadialDerivative_left_rectangle (angle v : ℝ)
    (ha : 0<angle-v) (hb : angle-v<Real.pi) :
    ∃ eta k : ℝ,0<eta ∧ 0<k ∧ ∀ (s theta rho w : ℝ),
      dist (s,theta) (1,angle)<eta → dist (rho,w) (1,v)<eta →
      physicalSourceAngularRadialDerivative s theta rho w≤ -k := by
  have hn : 0<‖polarPoint 1 angle-polarPoint 1 v‖ :=
    polar_distance_pos 1 1 v angle (by norm_num) (by norm_num) ⟨ha,hb⟩
  have hsep := sub_ne_zero.mp (norm_ne_zero_iff.mp (ne_of_gt hn))
  let k := -physicalSourceAngularRadialDerivative 1 angle 1 v/2
  have hneg := physicalSourceAngularRadialDerivative_unit_neg angle v ha hb
  have hk : 0<k := by dsimp [k]; linarith
  have hstrict : physicalSourceAngularRadialDerivative 1 angle 1 v< -k := by
    dsimp [k]; linarith
  have he := (physicalSourceAngularRadialDerivative_joint_contDiffAt
    ((1,angle),(1,v)) hsep).continuousAt.eventually (Iio_mem_nhds hstrict)
  obtain ⟨eta,heta,hball⟩ := Metric.eventually_nhds_iff.mp he
  refine ⟨eta,k,heta,hk,?_⟩
  intro s theta rho w hs ht
  exact (hball (y := ((s,theta),(rho,w)))
    (by rw [Prod.dist_eq]; exact max_lt hs ht)).le

theorem physicalSourceAngularRadialDerivative_right_rectangle (angle v : ℝ)
    (ha : -Real.pi<angle-v) (hb : angle-v<0) :
    ∃ eta k : ℝ,0<eta ∧ 0<k ∧ ∀ (s theta rho w : ℝ),
      dist (s,theta) (1,angle)<eta → dist (rho,w) (1,v)<eta →
      k≤physicalSourceAngularRadialDerivative s theta rho w := by
  have hn : 0<‖polarPoint 1 v-polarPoint 1 angle‖ :=
    polar_distance_pos 1 1 angle v (by norm_num) (by norm_num) ⟨by linarith,by linarith⟩
  have hsep := Ne.symm (sub_ne_zero.mp (norm_ne_zero_iff.mp (ne_of_gt hn)))
  let k := physicalSourceAngularRadialDerivative 1 angle 1 v/2
  have hpos := physicalSourceAngularRadialDerivative_unit_pos angle v ha hb
  have hk : 0<k := by dsimp [k]; linarith
  have hstrict : k<physicalSourceAngularRadialDerivative 1 angle 1 v := by
    dsimp [k]; linarith
  have he := (physicalSourceAngularRadialDerivative_joint_contDiffAt
    ((1,angle),(1,v)) hsep).continuousAt.eventually (Ioi_mem_nhds hstrict)
  obtain ⟨eta,heta,hball⟩ := Metric.eventually_nhds_iff.mp he
  refine ⟨eta,k,heta,hk,?_⟩
  intro s theta rho w hs ht
  exact (hball (y := ((s,theta),(rho,w)))
    (by rw [Prod.dist_eq]; exact max_lt hs ht)).le

/-- Angular error is controlled in the same independent local parameter
product, with the exact source held fixed in the two evaluations. -/
theorem physicalSourceAngularField_angular_rectangle (angle v : ℝ)
    (hsep : polarPoint 1 angle≠polarPoint 1 v) :
    ∃ eta C : ℝ,0<eta ∧ 0<C ∧ ∀ (s theta rho va vb : ℝ),
      dist (s,theta) (1,angle)<eta → dist (rho,va) (1,v)<eta →
      dist (rho,vb) (1,v)<eta →
      |physicalSourceAngularField s theta rho vb-physicalSourceAngularField s theta rho va|≤
        C*|vb-va| := by
  obtain ⟨K,U,hU,hLip⟩ := ((physicalSourceAngularField_joint_contDiffAt
    ((1,angle),(1,v)) (by norm_num) hsep).of_le
      (by norm_num : (1 : ℕ∞ω)≤∞)).exists_lipschitzOnWith
  obtain ⟨eta,heta,hball⟩ := Metric.mem_nhds_iff.mp hU
  refine ⟨eta,(K : ℝ)+1,heta,by positivity,?_⟩
  intro s theta rho va vb hs ha hb
  have hUa : ((s,theta),(rho,va))∈U := hball (by
    rw [Metric.mem_ball,Prod.dist_eq]; exact max_lt hs ha)
  have hUb : ((s,theta),(rho,vb))∈U := hball (by
    rw [Metric.mem_ball,Prod.dist_eq]; exact max_lt hs hb)
  have h := hLip.dist_le_mul _ hUb _ hUa
  have hd : dist ((s,theta),(rho,vb)) ((s,theta),(rho,va))=|vb-va| := by
    simp only [Prod.dist_eq,dist_self,Real.dist_eq]
    simp [abs_nonneg]
  rw [hd,Real.dist_eq] at h
  exact h.trans (mul_le_mul_of_nonneg_right (by linarith : (K : ℝ)≤(K : ℝ)+1)
    (abs_nonneg _))

theorem physicalSourceAngularField_regular_rectangle (angle v : ℝ)
    (hsep : polarPoint 1 angle≠polarPoint 1 v) :
    ∃ eta : ℝ,0<eta ∧ ∀ (s theta rho w : ℝ),
      dist (s,theta) (1,angle)<eta → dist (rho,w) (1,v)<eta →
      0<s ∧ polarPoint s theta≠polarPoint rho w := by
  have hsource : Continuous (fun z : (ℝ×ℝ)×(ℝ×ℝ) => polarPoint z.1.1 z.1.2) :=
    (polarPoint_contDiff ∞).continuous.comp continuous_fst
  have htarget : Continuous (fun z : (ℝ×ℝ)×(ℝ×ℝ) => polarPoint z.2.1 z.2.2) :=
    (polarPoint_contDiff ∞).continuous.comp continuous_snd
  have hnorm : 0<‖polarPoint 1 angle-polarPoint 1 v‖ :=
    norm_pos_iff.mpr (sub_ne_zero.mpr hsep)
  have hnormcont : Continuous (fun z : (ℝ×ℝ)×(ℝ×ℝ) =>
      ‖polarPoint z.1.1 z.1.2-polarPoint z.2.1 z.2.2‖) := (hsource.sub htarget).norm
  have he : ∀ᶠ z : (ℝ×ℝ)×(ℝ×ℝ) in nhds ((1,angle),(1,v)),
      0<‖polarPoint z.1.1 z.1.2-polarPoint z.2.1 z.2.2‖ :=
    hnormcont.continuousAt.eventually (Ioi_mem_nhds hnorm)
  have hscont : Continuous (fun z : (ℝ×ℝ)×(ℝ×ℝ) => z.1.1) := by fun_prop
  have hs : ∀ᶠ z : (ℝ×ℝ)×(ℝ×ℝ) in nhds ((1,angle),(1,v)),0<z.1.1 :=
    hscont.continuousAt.eventually
      (Ioi_mem_nhds (by norm_num : (0 : ℝ)<1))
  obtain ⟨eta,heta,hball⟩ := Metric.eventually_nhds_iff.mp (hs.and he)
  refine ⟨eta,heta,?_⟩
  intro s theta rho w hst hrt
  have h := hball (y := ((s,theta),(rho,w))) (by
    rw [Prod.dist_eq]; exact max_lt hst hrt)
  exact ⟨h.1,sub_ne_zero.mp (norm_ne_zero_iff.mp (ne_of_gt h.2))⟩

/-- Joint source/target controls for a left endpoint pair. The independent
rectangle and all constants precede the arbitrary CURRENT mass fractions.
The complete exterior sum retains sigma even when it tends to zero. -/
theorem physical_pair_left_endpoint_rectangular_controls
    (theta0 : Satellite → ℝ) (a b : Satellite) (hab : a≠b) (psi : ℝ)
    (hside : ∀ j∈pairExteriorLabels a b,0<theta0 j-psi ∧ theta0 j-psi<Real.pi) :
    ∃ eta k C : ℝ,0<eta ∧ 0<k ∧ 0<C ∧
      ∀ (mu r theta : Satellite → ℝ),PositiveRatio mu →
      (∀ j∈pairExteriorLabels a b,dist (r j,theta j) (1,theta0 j)<eta) →
      (∀ rho w,dist (rho,w) (1,psi)<eta →
        (∀ j∈pairExteriorLabels a b,0<r j ∧ polarPoint (r j) (theta j)≠polarPoint rho w) ∧
        (∑ j∈pairExteriorLabels a b,
          mu j*physicalSourceAngularRadialDerivative (r j) (theta j) rho w)≤
          -k*(1-(mu a+mu b))) ∧
      (∀ rho va vb,dist (rho,va) (1,psi)<eta → dist (rho,vb) (1,psi)<eta →
        |physicalPairExteriorAngularField mu r theta a b rho vb-
          physicalPairExteriorAngularField mu r theta a b rho va|≤
          C*(1-(mu a+mu b))*|vb-va|) := by
  have hw (j : Satellite) : ∃ eta k C : ℝ,0<eta ∧ 0<k ∧ 0<C ∧
      ∀ s theta rho w, j∈pairExteriorLabels a b →
        dist (s,theta) (1,theta0 j)<eta → dist (rho,w) (1,psi)<eta →
        (0<s ∧ polarPoint s theta≠polarPoint rho w) ∧
        physicalSourceAngularRadialDerivative s theta rho w≤ -k ∧
        ∀ va vb,dist (rho,va) (1,psi)<eta → dist (rho,vb) (1,psi)<eta →
          |physicalSourceAngularField s theta rho vb-physicalSourceAngularField s theta rho va|≤
            C*|vb-va| := by
    by_cases hj : j∈pairExteriorLabels a b
    · have hsep : polarPoint 1 (theta0 j)≠polarPoint 1 psi := by
        exact sub_ne_zero.mp (norm_ne_zero_iff.mp (ne_of_gt
          (polar_distance_pos 1 1 psi (theta0 j) (by norm_num) (by norm_num) (hside j hj))))
      obtain ⟨e0,he0,hregular⟩ := physicalSourceAngularField_regular_rectangle (theta0 j) psi hsep
      obtain ⟨e1,k,he1,hk,hderiv⟩ :=
        physicalSourceAngularRadialDerivative_left_rectangle (theta0 j) psi
          (hside j hj).1 (hside j hj).2
      obtain ⟨e2,C,he2,hC,hangular⟩ := physicalSourceAngularField_angular_rectangle (theta0 j) psi hsep
      let eta := min e0 (min e1 e2)
      have h0 : eta≤e0 := min_le_left _ _
      have h1 : eta≤e1 := (min_le_right _ _).trans (min_le_left _ _)
      have h2 : eta≤e2 := (min_le_right _ _).trans (min_le_right _ _)
      refine ⟨eta,k,C,lt_min he0 (lt_min he1 he2),hk,hC,?_⟩
      intro s theta rho w _ hs ht
      refine ⟨hregular _ _ _ _ (hs.trans_le h0) (ht.trans_le h0),
        hderiv _ _ _ _ (hs.trans_le h1) (ht.trans_le h1),?_⟩
      intro va vb ha hb
      exact hangular _ _ _ _ _ (hs.trans_le h2) (ha.trans_le h2) (hb.trans_le h2)
    · exact ⟨1,1,1,by norm_num,by norm_num,by norm_num,
        fun _ _ _ _ hm _ _ => (hj hm).elim⟩
  choose eta0 k0 C0 heta0 hk0 hC0 hcontrol using hw
  obtain ⟨eta,heta,hetas⟩ := Pi.exists_forall_pos_add_lt (fun j => heta0 j)
  obtain ⟨k,hk,hks⟩ := Pi.exists_forall_pos_add_lt (fun j => hk0 j)
  let C := (∑ j∈pairExteriorLabels a b,C0 j)+1
  have hC : 0<C := by
    have hsum := Finset.sum_nonneg (fun j (_ : j∈pairExteriorLabels a b) => (hC0 j).le)
    dsimp [C]; linarith
  have heta_bound (j : Satellite) : eta≤eta0 j := by simpa using (hetas j).le
  have hk_bound (j : Satellite) : k≤k0 j := by simpa using (hks j).le
  have hC_bound (j : Satellite) (hj : j∈pairExteriorLabels a b) : C0 j≤C := by
    have hs := Finset.single_le_sum (fun l (_ : l∈pairExteriorLabels a b) => (hC0 l).le) hj
    dsimp [C]; linarith
  refine ⟨eta,k,C,heta,hk,hC,?_⟩
  intro mu r theta hm hs
  refine ⟨?_,?_⟩
  · intro rho w ht
    refine ⟨fun j hj => (hcontrol j _ _ _ _ hj
      ((hs j hj).trans_le (heta_bound j)) (ht.trans_le (heta_bound j))).1,?_⟩
    calc
      _≤∑ j∈pairExteriorLabels a b,mu j*(-k) := by
        apply Finset.sum_le_sum
        intro j hj
        exact mul_le_mul_of_nonneg_left
          ((hcontrol j _ _ _ _ hj ((hs j hj).trans_le (heta_bound j))
            (ht.trans_le (heta_bound j))).2.1.trans (neg_le_neg (hk_bound j))) (hm.1 j).le
      _= -k*(1-(mu a+mu b)) := by
        rw [← Finset.sum_mul,pairExteriorMass_eq mu a b hab hm.2]
        ring
  · intro rho va vb ha hb
    have heq (v : ℝ) : physicalPairExteriorAngularField mu r theta a b rho v=
        ∑ j∈pairExteriorLabels a b,mu j*physicalSourceAngularField (r j) (theta j) rho v := by
      unfold physicalPairExteriorAngularField physicalSourceAngularField
      apply Finset.sum_congr rfl
      intro j _
      ring
    rw [heq,heq,← Finset.sum_sub_distrib]
    simp only [← mul_sub]
    calc
      _≤∑ j∈pairExteriorLabels a b,
          |mu j*(physicalSourceAngularField (r j) (theta j) rho vb-
            physicalSourceAngularField (r j) (theta j) rho va)| := Finset.abs_sum_le_sum_abs _ _
      _≤∑ j∈pairExteriorLabels a b,mu j*(C*|vb-va|) := by
        apply Finset.sum_le_sum
        intro j hj
        rw [abs_mul,abs_of_pos (hm.1 j)]
        apply mul_le_mul_of_nonneg_left _ (hm.1 j).le
        exact ((hcontrol j _ _ _ va hj ((hs j hj).trans_le (heta_bound j))
          (ha.trans_le (heta_bound j))).2.2 va vb
            (ha.trans_le (heta_bound j)) (hb.trans_le (heta_bound j))).trans
          (mul_le_mul_of_nonneg_right (hC_bound j hj) (abs_nonneg _))
      _=C*(1-(mu a+mu b))*|vb-va| := by
        rw [← Finset.sum_mul,pairExteriorMass_eq mu a b hab hm.2]
        ring

theorem physical_pair_direction_polar_components (r theta : Satellite → ℝ) (a b : Satellite) :
    inner ℝ (physicalPairDirection (polarSatellites r theta) a b)
      (quarterTurn (polarPoint 1 (theta a)))=
        r b*Real.sin (theta b-theta a)/satelliteDistance (polarSatellites r theta) a b ∧
    inner ℝ (physicalPairDirection (polarSatellites r theta) a b)
      (polarPoint 1 ((theta a+theta b)/2))=
        (r b-r a)*Real.cos ((theta b-theta a)/2)/satelliteDistance (polarSatellites r theta) a b := by
  have hca : Real.cos (theta a-(theta a+theta b)/2)=Real.cos ((theta b-theta a)/2) := by
    rw [show theta a-(theta a+theta b)/2= -((theta b-theta a)/2) by ring,Real.cos_neg]
  have hcb : Real.cos (theta b-(theta a+theta b)/2)=Real.cos ((theta b-theta a)/2) :=
    congrArg Real.cos (by ring)
  constructor
  · simp only [physicalPairDirection,real_inner_smul_left,inner_sub_left,polarSatellites,
      polarPoint_inner_rotation,sub_self,Real.sin_zero,one_mul,mul_zero,sub_zero]
    ring
  · simp only [physicalPairDirection,real_inner_smul_left,inner_sub_left,polarSatellites,
      polarPoint_inner_radial,hca,hcb]
    ring

/-- The angular and radial distance quotients of an actual polar pair are
derived from its normalized direction, using exact sinc and midpoint
identities. No radial/tangential asymptotic is supplied as a hypothesis. -/
theorem physical_pair_direction_polar_ratio_limits
    (r theta : ℕ → Satellite → ℝ) (a b : Satellite) (psi : ℝ)
    (hr : ∀ n,0<r n b)
    (hd : ∀ n,0<satelliteDistance (polarSatellites (r n) (theta n)) a b)
    (hrbt : Tendsto (fun n => r n b) atTop (nhds 1))
    (hat : Tendsto (fun n => theta n a) atTop (nhds psi))
    (hbt : Tendsto (fun n => theta n b) atTop (nhds psi))
    (v : Plane)
    (hvt : Tendsto (fun n => physicalPairDirection (polarSatellites (r n) (theta n)) a b)
      atTop (nhds v)) :
    Tendsto (fun n => (theta n b-theta n a)/satelliteDistance (polarSatellites (r n) (theta n)) a b)
      atTop (nhds (inner ℝ v (quarterTurn (polarPoint 1 psi)))) ∧
    Tendsto (fun n => (r n b-r n a)/satelliteDistance (polarSatellites (r n) (theta n)) a b)
      atTop (nhds (inner ℝ v (polarPoint 1 psi))) := by
  have hgap : Tendsto (fun n => theta n b-theta n a) atTop (nhds 0) := by
    simpa only [sub_self] using hbt.sub hat
  have he : Tendsto (fun n => polarPoint 1 (theta n a)) atTop (nhds (polarPoint 1 psi)) := by
    exact ((polarPoint_contDiff ∞).continuous.tendsto (1,psi)).comp
      (tendsto_const_nhds.prodMk_nhds hat)
  have het : Tendsto (fun n => quarterTurn (polarPoint 1 (theta n a))) atTop
      (nhds (quarterTurn (polarPoint 1 psi))) :=
    quarterTurnLinear.toContinuousLinearMap.continuous.tendsto _ |>.comp he
  have hsinc : Tendsto (fun n => Real.sinc (theta n b-theta n a)) atTop (nhds 1) := by
    simpa only [Real.sinc_zero,Function.comp_def] using Real.continuous_sinc.continuousAt.tendsto.comp hgap
  have hsincnz := hsinc.eventually_ne (by norm_num : (1 : ℝ)≠0)
  have hang := (hvt.inner (𝕜 := ℝ) het).div (hrbt.mul hsinc) (by norm_num : (1 : ℝ)*1≠0)
  have hmidt : Tendsto (fun n => (theta n a+theta n b)/2) atTop (nhds psi) := by
    simpa only [show (psi+psi)/2=psi by ring] using (hat.add hbt).div_const 2
  have hem : Tendsto (fun n => polarPoint 1 ((theta n a+theta n b)/2)) atTop
      (nhds (polarPoint 1 psi)) :=
    ((polarPoint_contDiff ∞).continuous.tendsto (1,psi)).comp
      (tendsto_const_nhds.prodMk_nhds hmidt)
  have hcos : Tendsto (fun n => Real.cos ((theta n b-theta n a)/2)) atTop (nhds 1) := by
    simpa only [zero_div,Real.cos_zero,Function.comp_def] using Real.continuous_cos.continuousAt.tendsto.comp
      (hgap.div_const 2)
  have hcosnz := hcos.eventually_ne (by norm_num : (1 : ℝ)≠0)
  have hrad := (hvt.inner (𝕜 := ℝ) hem).div hcos (by norm_num : (1 : ℝ)≠0)
  constructor
  · have hang' : Tendsto (fun n =>
        inner ℝ (physicalPairDirection (polarSatellites (r n) (theta n)) a b)
          (quarterTurn (polarPoint 1 (theta n a)))/(r n b*Real.sinc (theta n b-theta n a)))
        atTop (nhds (inner ℝ v (quarterTurn (polarPoint 1 psi)))) := by
      convert! hang using 1; simp
    apply hang'.congr'
    filter_upwards [hsincnz] with n hn
    rw [(physical_pair_direction_polar_components (r n) (theta n) a b).1,
      ← sinc_mul_argument (theta n b-theta n a)]
    field_simp [ne_of_gt (hd n),ne_of_gt (hr n),hn]
  · have hrad' : Tendsto (fun n =>
        inner ℝ (physicalPairDirection (polarSatellites (r n) (theta n)) a b)
          (polarPoint 1 ((theta n a+theta n b)/2))/Real.cos ((theta n b-theta n a)/2))
        atTop (nhds (inner ℝ v (polarPoint 1 psi))) := by
      convert! hrad using 1; simp
    apply hrad'.congr'
    filter_upwards [hcosnz] with n hn
    rw [(physical_pair_direction_polar_components (r n) (theta n) a b).2]
    field_simp [ne_of_gt (hd n),hn]

theorem polar_rectangle_radius_interval (ra rb w psi eta : ℝ)
    (ha : dist (ra,w) (1,psi)<eta) (hb : dist (rb,w) (1,psi)<eta) :
    ∀ rho∈Set.Icc ra rb,dist (rho,w) (1,psi)<eta := by
  rw [Prod.dist_eq,max_lt_iff] at ha hb
  intro rho hrho
  rw [Prod.dist_eq,max_lt_iff]
  refine ⟨?_,ha.2⟩
  rw [Real.dist_eq,abs_lt] at ha hb ⊢
  exact ⟨by linarith [hrho.1],by linarith [hrho.2]⟩

/-- The actual field difference has the endpoint upper bound needed to
exclude an outward radial pair. This is proved by the scalar mean value
theorem on the full radial interval and the independent angular estimate. -/
theorem physical_pair_left_endpoint_difference_control
    (theta0 : Satellite → ℝ) (a b : Satellite) (hab : a≠b) (psi : ℝ)
    (hside : ∀ j∈pairExteriorLabels a b,0<theta0 j-psi ∧ theta0 j-psi<Real.pi) :
    ∃ eta k C : ℝ,0<eta ∧ 0<k ∧ 0<C ∧
      ∀ (mu r theta : Satellite → ℝ),PositiveRatio mu → (∀ i,0<r i) →
      (∀ j∈pairExteriorLabels a b,dist (r j,theta j) (1,theta0 j)<eta) →
      ∀ ra rb va vb,ra≤rb → dist (ra,va) (1,psi)<eta →
      dist (rb,va) (1,psi)<eta → dist (rb,vb) (1,psi)<eta →
      physicalPairExteriorAngularField mu r theta a b rb vb-
        physicalPairExteriorAngularField mu r theta a b ra va≤
        -k*(1-(mu a+mu b))*(rb-ra)+C*(1-(mu a+mu b))*|vb-va| := by
  obtain ⟨eta,k,C,heta,hk,hC,hcontrol⟩ :=
    physical_pair_left_endpoint_rectangular_controls theta0 a b hab psi hside
  refine ⟨eta,k,C,heta,hk,hC,?_⟩
  intro mu r theta hm hr hs ra rb va vb habr ha hb hc
  obtain ⟨hderiv,hangular⟩ := hcontrol mu r theta hm hs
  have hrect := polar_rectangle_radius_interval ra rb va psi eta ha hb
  have hF (rho : ℝ) (hp : rho∈Set.Icc ra rb) :=
    physicalPairExteriorAngularField_hasDerivAt_radius mu r theta a b rho va hr
      (fun j hj => ((hderiv rho va (hrect rho hp)).1 j hj).2)
  have hcont : ContinuousOn (fun rho => physicalPairExteriorAngularField mu r theta a b rho va)
      (Set.Icc ra rb) := fun rho hp => (hF rho hp).continuousAt.continuousWithinAt
  have hdiff : DifferentiableOn ℝ (fun rho => physicalPairExteriorAngularField mu r theta a b rho va)
      (interior (Set.Icc ra rb)) :=
    fun rho hp => (hF rho (interior_subset hp)).differentiableAt.differentiableWithinAt
  have hbound : ∀ rho∈interior (Set.Icc ra rb),
      deriv (fun s => physicalPairExteriorAngularField mu r theta a b s va) rho≤
        -k*(1-(mu a+mu b)) := by
    intro rho hp
    rw [(hF rho (interior_subset hp)).deriv]
    exact (hderiv rho va (hrect rho (interior_subset hp))).2
  have hrad := (convex_Icc ra rb).image_sub_le_mul_sub_of_deriv_le hcont hdiff hbound
    ra (Set.left_mem_Icc.mpr habr) rb (Set.right_mem_Icc.mpr habr) habr
  have hang := (le_abs_self (physicalPairExteriorAngularField mu r theta a b rb vb-
    physicalPairExteriorAngularField mu r theta a b rb va)).trans (hangular rb va vb hb hc)
  linarith

theorem pairExteriorLabels_nonempty (a b : Satellite) (hab : a≠b) :
    (pairExteriorLabels a b).Nonempty := by
  have hb : b∈Finset.univ.erase a := Finset.mem_erase.mpr ⟨Ne.symm hab,Finset.mem_univ b⟩
  apply Finset.card_pos.mp
  unfold pairExteriorLabels
  rw [Finset.card_erase_of_mem hb,Finset.card_erase_of_mem (Finset.mem_univ a),Finset.card_univ]
  norm_num

theorem pairExteriorMass_pos (mu : MassRatio) (hm : PositiveRatio mu)
    (a b : Satellite) (hab : a≠b) : 0<1-(mu a+mu b) := by
  rw [← pairExteriorMass_eq mu a b hab hm.2]
  exact Finset.sum_pos (fun j _ => hm.1 j) (pairExteriorLabels_nonempty a b hab)

/-- The actual angular rows exclude the outward radial limit at a left
endpoint complete pair. Delta/d and Delta-rho/d are derived from the
direction limit by `physical_pair_direction_polar_ratio_limits`. -/
theorem normalized_complete_pair_left_outward_radial_impossible
    (eps : ℕ → ℝ) (mu : ℕ → MassRatio) (x : ℕ → Configuration)
    (heps : ∀ n,0<eps n) (hepst : Tendsto eps atTop (nhds 0))
    (hm : ∀ n,PositiveRatio (mu n))
    (hx : ∀ n,NormalizedCentralConfiguration (masses (eps n) (mu n)) (x n))
    (r theta : ℕ → Satellite → ℝ) (hr : ∀ n,∀ i,0<r n i)
    (hpolar : ∀ n,satellitesRelative (x n)=polarSatellites (r n) (theta n))
    (horder : ∀ n,∀ i j,i<j → 0<theta n j-theta n i ∧ theta n j-theta n i<Real.pi)
    (qLimit : SatelliteConfiguration)
    (hqt : Tendsto (fun n => satellitesRelative (x n)) atTop (nhds qLimit))
    (a b : Satellite) (hab : a<b) (psi : ℝ)
    (hpair : CompleteLimitingSatellitePair qLimit a b (polarPoint 1 psi))
    (theta0 : Satellite → ℝ) (hthetat : Tendsto theta atTop (nhds theta0))
    (hpa : theta0 a=psi) (hpb : theta0 b=psi)
    (hside : ∀ j∈pairExteriorLabels a b,0<theta0 j-psi ∧ theta0 j-psi<Real.pi)
    (hvt : Tendsto (fun n => physicalPairDirection (satellitesRelative (x n)) a b)
      atTop (nhds (polarPoint 1 psi))) : False := by
  have hab' := ne_of_lt hab
  have hrat (i : Satellite) : Tendsto (fun n => r n i) atTop (nhds 1) := by
    convert! dominant_satellite_radius_tendsto eps mu x heps hepst hm hx i using 1
    funext n
    rw [hpolar n]
    simp only [polarSatellites,polarPoint_norm,abs_of_pos (hr n i)]
  have htat (i : Satellite) : Tendsto (fun n => theta n i) atTop (nhds (theta0 i)) := by
    simpa only [Function.comp_def] using (continuous_apply i).tendsto theta0 |>.comp hthetat
  have hdist (n : ℕ) : 0<satelliteDistance (polarSatellites (r n) (theta n)) a b := by
    rw [← hpolar n]
    exact norm_pos_iff.mpr (sub_ne_zero.mpr
      ((satellitesRelative_collisionFree (x n) (hx n).1).2 a b hab'))
  have hvt' : Tendsto (fun n => physicalPairDirection (polarSatellites (r n) (theta n)) a b)
      atTop (nhds (polarPoint 1 psi)) := by
    simpa only [← hpolar] using hvt
  obtain ⟨hgap,hrad⟩ := physical_pair_direction_polar_ratio_limits r theta a b psi
    (fun n => hr n b) hdist (hrat b) (by simpa only [hpa] using htat a)
      (by simpa only [hpb] using htat b) (polarPoint 1 psi) hvt'
  have hgap0 : Tendsto (fun n => (theta n b-theta n a)/
      satelliteDistance (polarSatellites (r n) (theta n)) a b) atTop (nhds 0) := by
    simpa only [polarPoint_inner_rotation,sub_self,Real.sin_zero,mul_zero] using hgap
  have hrad1 : Tendsto (fun n => (r n b-r n a)/
      satelliteDistance (polarSatellites (r n) (theta n)) a b) atTop (nhds 1) := by
    simpa only [polarPoint_inner_radial,sub_self,Real.cos_zero,mul_one] using hrad
  obtain ⟨eta,k,C,heta,hk,hC,hcontrol⟩ :=
    physical_pair_left_endpoint_difference_control theta0 a b hab' psi hside
  have hsource : ∀ᶠ n in atTop,∀ j∈pairExteriorLabels a b,
      dist (r n j,theta n j) (1,theta0 j)<eta := by
    apply (Finset.eventually_all (pairExteriorLabels a b)).mpr
    intro j _
    exact ((hrat j).prodMk_nhds (htat j)).eventually (Metric.ball_mem_nhds _ heta)
  have ha : Tendsto (fun n => (r n a,theta n a)) atTop (nhds (1,psi)) := by
    simpa only [hpa] using (hrat a).prodMk_nhds (htat a)
  have hba : Tendsto (fun n => (r n b,theta n a)) atTop (nhds (1,psi)) := by
    simpa only [hpa] using (hrat b).prodMk_nhds (htat a)
  have hb : Tendsto (fun n => (r n b,theta n b)) atTop (nhds (1,psi)) := by
    simpa only [hpb] using (hrat b).prodMk_nhds (htat b)
  have hsmallgap := hgap0.eventually (Iio_mem_nhds (div_pos hk (by positivity : 0<4*C)))
  have hlargerad := hrad1.eventually (Ioi_mem_nhds (by norm_num : (1/2 : ℝ)<1))
  have hQ := normalized_complete_pair_tangential_difference_positive eps mu x heps hepst hm hx
    r theta hr hpolar horder qLimit hqt a b hab (polarPoint 1 psi) hpair
  have he : ∀ᶠ (_n : ℕ) in atTop,False := by
    filter_upwards [hsource,ha.eventually (Metric.ball_mem_nhds _ heta),
      hba.eventually (Metric.ball_mem_nhds _ heta),hb.eventually (Metric.ball_mem_nhds _ heta),
      hsmallgap,hlargerad,hQ] with n hn hna hnba hnb hng hnr hnQ
    have hradpos : 0<r n b-r n a := (div_pos_iff.mp (lt_trans (by norm_num) hnr)).elim
      (fun h => h.1) (fun h => (not_lt_of_gt (hdist n) h.2).elim)
    have hbound := hcontrol (mu n) (r n) (theta n) (hm n) (hr n) hn
      (r n a) (r n b) (theta n a) (theta n b) (by linarith) hna hnba hnb
    rw [abs_of_pos (horder n a b hab).1] at hbound
    have hCg : C*((theta n b-theta n a)/satelliteDistance (polarSatellites (r n) (theta n)) a b)<k/4 := by
      have h := (lt_div_iff₀ (show 0<4*C by positivity)).mp hng
      nlinarith
    have hkr : k/2<k*((r n b-r n a)/satelliteDistance (polarSatellites (r n) (theta n)) a b) := by
      exact (by simpa only [mul_one_div] using mul_lt_mul_of_pos_left hnr hk)
    have hneg : -k*((r n b-r n a)/satelliteDistance (polarSatellites (r n) (theta n)) a b)+
        C*((theta n b-theta n a)/satelliteDistance (polarSatellites (r n) (theta n)) a b)<0 := by linarith
    have hfactor : -k*(1-(mu n a+mu n b))*(r n b-r n a)+
        C*(1-(mu n a+mu n b))*(theta n b-theta n a)=
        ((1-(mu n a+mu n b))*satelliteDistance (polarSatellites (r n) (theta n)) a b)*
          (-k*((r n b-r n a)/satelliteDistance (polarSatellites (r n) (theta n)) a b)+
            C*((theta n b-theta n a)/satelliteDistance (polarSatellites (r n) (theta n)) a b)) := by
      field_simp [ne_of_gt (hdist n)]
    rw [hfactor] at hbound
    have hnneg := mul_neg_of_pos_of_neg (mul_pos (pairExteriorMass_pos (mu n) (hm n) a b hab')
      (hdist n)) hneg
    linarith [hnQ.2]
  exact he.exists.elim (fun _ hn => hn)

theorem polarPoint_distance_neg_angles (r s theta phi : ℝ) :
    ‖polarPoint r (-theta)-polarPoint s (-phi)‖=
      ‖polarPoint r theta-polarPoint s phi‖ := by
  have he : ‖polarPoint r (-theta)-polarPoint s (-phi)‖^2=
      ‖polarPoint r theta-polarPoint s phi‖^2 := by
    rw [polar_distance_sq s r (-phi) (-theta),polar_distance_sq s r phi theta]
    rw [show -theta- -phi= -(theta-phi) by ring,neg_div,Real.sin_neg]
    ring
  exact (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp he

theorem physicalSourceAngularField_neg_angles (s angle rho v : ℝ) :
    physicalSourceAngularField s (-angle) rho (-v)= -physicalSourceAngularField s angle rho v := by
  unfold physicalSourceAngularField
  rw [show -angle- -v= -(angle-v) by ring,Real.sin_neg,
    polarPoint_distance_neg_angles]
  ring

theorem physicalPairExteriorAngularField_neg_angles (mu r theta : Satellite → ℝ)
    (a b : Satellite) (rho v : ℝ) :
    physicalPairExteriorAngularField mu r (fun i => -theta i) a b rho (-v)=
      -physicalPairExteriorAngularField mu r theta a b rho v := by
  unfold physicalPairExteriorAngularField
  rw [← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro j _
  rw [show -theta j- -v= -(theta j-v) by ring,Real.sin_neg,
    polarPoint_distance_neg_angles]
  ring

theorem polar_rectangle_neg_angle_dist (rho v psi : ℝ) :
    dist (rho,-v) (1,-psi)=dist (rho,v) (1,psi) := by
  simp only [Prod.dist_eq,Real.dist_eq]
  rw [show -v- -psi= -(v-psi) by ring,abs_neg]

/-- Right endpoint estimate obtained by the exact scalar angle-reversal
identity, used only in the analytic inequality. Similarity uniqueness
remains the original SO(2) relation. -/
theorem physical_pair_right_endpoint_difference_control
    (theta0 : Satellite → ℝ) (a b : Satellite) (hab : a≠b) (psi : ℝ)
    (hside : ∀ j∈pairExteriorLabels a b,-Real.pi<theta0 j-psi ∧ theta0 j-psi<0) :
    ∃ eta k C : ℝ,0<eta ∧ 0<k ∧ 0<C ∧
      ∀ (mu r theta : Satellite → ℝ),PositiveRatio mu → (∀ i,0<r i) →
      (∀ j∈pairExteriorLabels a b,dist (r j,theta j) (1,theta0 j)<eta) →
      ∀ ra rb va vb,rb≤ra → dist (rb,vb) (1,psi)<eta →
      dist (ra,vb) (1,psi)<eta → dist (ra,va) (1,psi)<eta →
      physicalPairExteriorAngularField mu r theta a b rb vb-
        physicalPairExteriorAngularField mu r theta a b ra va≤
        -k*(1-(mu a+mu b))*(ra-rb)+C*(1-(mu a+mu b))*|vb-va| := by
  have hleft : ∀ j∈pairExteriorLabels a b,0< -theta0 j- -psi ∧ -theta0 j- -psi<Real.pi := by
    intro j hj
    constructor <;> linarith [(hside j hj).1,(hside j hj).2]
  obtain ⟨eta,k,C,heta,hk,hC,hcontrol⟩ :=
    physical_pair_left_endpoint_difference_control (fun i => -theta0 i) a b hab (-psi) hleft
  refine ⟨eta,k,C,heta,hk,hC,?_⟩
  intro mu r theta hm hr hs ra rb va vb habr ha hb hc
  have h := hcontrol mu r (fun i => -theta i) hm hr
    (fun j hj => by simpa only [polar_rectangle_neg_angle_dist] using hs j hj)
    rb ra (-vb) (-va) habr
    (by simpa only [polar_rectangle_neg_angle_dist] using ha)
    (by simpa only [polar_rectangle_neg_angle_dist] using hb)
    (by simpa only [polar_rectangle_neg_angle_dist] using hc)
  rw [physicalPairExteriorAngularField_neg_angles,physicalPairExteriorAngularField_neg_angles,
    show -va- -vb=vb-va by ring] at h
  linarith

/-- Actual right endpoint radial-branch exclusion. -/
theorem normalized_complete_pair_right_inward_radial_impossible
    (eps : ℕ → ℝ) (mu : ℕ → MassRatio) (x : ℕ → Configuration)
    (heps : ∀ n,0<eps n) (hepst : Tendsto eps atTop (nhds 0))
    (hm : ∀ n,PositiveRatio (mu n))
    (hx : ∀ n,NormalizedCentralConfiguration (masses (eps n) (mu n)) (x n))
    (r theta : ℕ → Satellite → ℝ) (hr : ∀ n,∀ i,0<r n i)
    (hpolar : ∀ n,satellitesRelative (x n)=polarSatellites (r n) (theta n))
    (horder : ∀ n,∀ i j,i<j → 0<theta n j-theta n i ∧ theta n j-theta n i<Real.pi)
    (qLimit : SatelliteConfiguration)
    (hqt : Tendsto (fun n => satellitesRelative (x n)) atTop (nhds qLimit))
    (a b : Satellite) (hab : a<b) (psi : ℝ)
    (hpair : CompleteLimitingSatellitePair qLimit a b (polarPoint 1 psi))
    (theta0 : Satellite → ℝ) (hthetat : Tendsto theta atTop (nhds theta0))
    (hpa : theta0 a=psi) (hpb : theta0 b=psi)
    (hside : ∀ j∈pairExteriorLabels a b,-Real.pi<theta0 j-psi ∧ theta0 j-psi<0)
    (hvt : Tendsto (fun n => physicalPairDirection (satellitesRelative (x n)) a b)
      atTop (nhds (-polarPoint 1 psi))) : False := by
  have hab' := ne_of_lt hab
  have hrat (i : Satellite) : Tendsto (fun n => r n i) atTop (nhds 1) := by
    convert! dominant_satellite_radius_tendsto eps mu x heps hepst hm hx i using 1
    funext n
    rw [hpolar n]
    simp only [polarSatellites,polarPoint_norm,abs_of_pos (hr n i)]
  have htat (i : Satellite) : Tendsto (fun n => theta n i) atTop (nhds (theta0 i)) := by
    simpa only [Function.comp_def] using (continuous_apply i).tendsto theta0 |>.comp hthetat
  have hdist (n : ℕ) : 0<satelliteDistance (polarSatellites (r n) (theta n)) a b := by
    rw [← hpolar n]
    exact norm_pos_iff.mpr (sub_ne_zero.mpr
      ((satellitesRelative_collisionFree (x n) (hx n).1).2 a b hab'))
  have hvt' : Tendsto (fun n => physicalPairDirection (polarSatellites (r n) (theta n)) a b)
      atTop (nhds (-polarPoint 1 psi)) := by
    simpa only [← hpolar] using hvt
  obtain ⟨hgap,hrad⟩ := physical_pair_direction_polar_ratio_limits r theta a b psi
    (fun n => hr n b) hdist (hrat b) (by simpa only [hpa] using htat a)
      (by simpa only [hpb] using htat b) (-polarPoint 1 psi) hvt'
  have hgap0 : Tendsto (fun n => (theta n b-theta n a)/
      satelliteDistance (polarSatellites (r n) (theta n)) a b) atTop (nhds 0) := by
    simpa only [inner_neg_left,polarPoint_inner_rotation,sub_self,Real.sin_zero,mul_zero,neg_zero] using hgap
  have hradneg : Tendsto (fun n => (r n b-r n a)/
      satelliteDistance (polarSatellites (r n) (theta n)) a b) atTop (nhds (-1)) := by
    simpa only [inner_neg_left,polarPoint_inner_radial,sub_self,Real.cos_zero,mul_one] using hrad
  have hrad1 : Tendsto (fun n => (r n a-r n b)/
      satelliteDistance (polarSatellites (r n) (theta n)) a b) atTop (nhds 1) := by
    convert! hradneg.neg using 1
    · funext n; ring
    · norm_num
  obtain ⟨eta,k,C,heta,hk,hC,hcontrol⟩ :=
    physical_pair_right_endpoint_difference_control theta0 a b hab' psi hside
  have hsource : ∀ᶠ n in atTop,∀ j∈pairExteriorLabels a b,
      dist (r n j,theta n j) (1,theta0 j)<eta := by
    apply (Finset.eventually_all (pairExteriorLabels a b)).mpr
    intro j _
    exact ((hrat j).prodMk_nhds (htat j)).eventually (Metric.ball_mem_nhds _ heta)
  have ha : Tendsto (fun n => (r n a,theta n a)) atTop (nhds (1,psi)) := by
    simpa only [hpa] using (hrat a).prodMk_nhds (htat a)
  have hba : Tendsto (fun n => (r n a,theta n b)) atTop (nhds (1,psi)) := by
    simpa only [hpb] using (hrat a).prodMk_nhds (htat b)
  have hb : Tendsto (fun n => (r n b,theta n b)) atTop (nhds (1,psi)) := by
    simpa only [hpb] using (hrat b).prodMk_nhds (htat b)
  have hsmallgap := hgap0.eventually (Iio_mem_nhds (div_pos hk (by positivity : 0<4*C)))
  have hlargerad := hrad1.eventually (Ioi_mem_nhds (by norm_num : (1/2 : ℝ)<1))
  have hQ := normalized_complete_pair_tangential_difference_positive eps mu x heps hepst hm hx
    r theta hr hpolar horder qLimit hqt a b hab (polarPoint 1 psi) hpair
  have he : ∀ᶠ (_n : ℕ) in atTop,False := by
    filter_upwards [hsource,ha.eventually (Metric.ball_mem_nhds _ heta),
      hba.eventually (Metric.ball_mem_nhds _ heta),hb.eventually (Metric.ball_mem_nhds _ heta),
      hsmallgap,hlargerad,hQ] with n hn hna hnba hnb hng hnr hnQ
    have hradpos : 0<r n a-r n b := (div_pos_iff.mp (lt_trans (by norm_num) hnr)).elim
      (fun h => h.1) (fun h => (not_lt_of_gt (hdist n) h.2).elim)
    have hbound := hcontrol (mu n) (r n) (theta n) (hm n) (hr n) hn
      (r n a) (r n b) (theta n a) (theta n b) (by linarith) hnb hnba hna
    rw [abs_of_pos (horder n a b hab).1] at hbound
    have hCg : C*((theta n b-theta n a)/satelliteDistance (polarSatellites (r n) (theta n)) a b)<k/4 := by
      have h := (lt_div_iff₀ (show 0<4*C by positivity)).mp hng
      nlinarith
    have hkr : k/2<k*((r n a-r n b)/satelliteDistance (polarSatellites (r n) (theta n)) a b) := by
      exact (by simpa only [mul_one_div] using mul_lt_mul_of_pos_left hnr hk)
    have hneg : -k*((r n a-r n b)/satelliteDistance (polarSatellites (r n) (theta n)) a b)+
        C*((theta n b-theta n a)/satelliteDistance (polarSatellites (r n) (theta n)) a b)<0 := by linarith
    have hfactor : -k*(1-(mu n a+mu n b))*(r n a-r n b)+
        C*(1-(mu n a+mu n b))*(theta n b-theta n a)=
        ((1-(mu n a+mu n b))*satelliteDistance (polarSatellites (r n) (theta n)) a b)*
          (-k*((r n a-r n b)/satelliteDistance (polarSatellites (r n) (theta n)) a b)+
            C*((theta n b-theta n a)/satelliteDistance (polarSatellites (r n) (theta n)) a b)) := by
      field_simp [ne_of_gt (hdist n)]
    rw [hfactor] at hbound
    have hnneg := mul_neg_of_pos_of_neg (mul_pos (pairExteriorMass_pos (mu n) (hm n) a b hab')
      (hdist n)) hneg
    linarith [hnQ.2]
  exact he.exists.elim (fun _ hn => hn)

/-- Equal physical limiting angles are consecutive under the original
positive ordered polar gauge, so a complete two-label class is adjacent. -/
theorem complete_pair_ordered_angles_adjacent (theta0 : Satellite → ℝ)
    (hmono : Monotone theta0) (hspan : theta0 3-theta0 0<Real.pi)
    (qLimit : SatelliteConfiguration) (hpolar : ∀ i,qLimit i=polarPoint 1 (theta0 i))
    (a b : Satellite) (hab : a<b) (c : Plane)
    (hpair : CompleteLimitingSatellitePair qLimit a b c) :
    b.val=a.val+1 ∧ theta0 b=theta0 a := by
  have hqa : qLimit a=c := (hpair a).mpr (Or.inl rfl)
  have hqb : qLimit b=c := (hpair b).mpr (Or.inr rfl)
  have hgapbound : theta0 b-theta0 a<Real.pi := by
    have ha := hmono (Fin.zero_le a)
    have hb := hmono (Fin.le_last b)
    change theta0 b≤theta0 3 at hb
    linarith
  have hsame : theta0 b=theta0 a := by
    apply le_antisymm
    · apply le_of_not_gt
      intro he
      have hn := polar_distance_pos 1 1 (theta0 a) (theta0 b)
        (by norm_num) (by norm_num) ⟨sub_pos.mpr he,hgapbound⟩
      rw [← hpolar a,← hpolar b,hqa,hqb,sub_self,norm_zero] at hn
      exact lt_irrefl 0 hn
    · exact hmono hab.le
  refine ⟨?_,hsame⟩
  by_contra he
  have habval : a.val<b.val := hab
  let k : Satellite := ⟨a.val+1,by have hb := b.isLt; omega⟩
  have hak : a<k := by change a.val<a.val+1; omega
  have hkb : k<b := by change a.val+1<b.val; omega
  have hthetak : theta0 k=theta0 a := by
    have h1 := hmono hak.le
    have h2 := hmono hkb.le
    linarith
  have hkq : qLimit k=c := by rw [hpolar k,hthetak,← hpolar a,hqa]
  rcases (hpair k).mp hkq with hk|hk
  · exact (ne_of_lt hak) hk.symm
  · exact (ne_of_lt hkb) hk

/-- The original all-five-point directed support inequality supplies every
exterior support inequality for an actual adjacent satellite pair. -/
theorem strictConvex_adjacent_pair_support (x : Configuration)
    (hconv : StrictConvexInOrder ⟨Equiv.refl Label,rfl⟩ x)
    (a b : Satellite) (hab : b.val=a.val+1) :
    ∀ j∈pairExteriorLabels a b,
      0<det2 (satellitesRelative x b-satellitesRelative x a)
        (satellitesRelative x j-satellitesRelative x a) := by
  have hnext : (a.succ : Label)+1=b.succ := by
    apply Fin.ext
    change (a.val+1+1)%5=b.val+1
    have hb := b.isLt
    omega
  intro j hj
  have hja : j≠a := (Finset.mem_erase.mp (Finset.mem_erase.mp hj).2).1
  have hjb : j≠b := (Finset.mem_erase.mp hj).1
  have h := hconv a.succ j.succ
    (by intro he; exact hja (Fin.succ_injective _ he))
    (by rw [hnext]; intro he; exact hjb (Fin.succ_injective _ he))
  rw [hnext] at h
  have hdiff (i : Satellite) : satellitesRelative x i-satellitesRelative x a=
      x i.succ-x a.succ := by
    unfold satellitesRelative primaryRelative
    module
  simpa only [orientedArea,Equiv.refl_apply,hdiff] using h

theorem pairDet2_continuous : Continuous (fun z : Plane×Plane => det2 z.1 z.2) := by
  unfold det2
  have h0 : Continuous (fun z : Plane×Plane => z.1 0) := by fun_prop
  have h1 : Continuous (fun z : Plane×Plane => z.1 1) := by fun_prop
  have h2 : Continuous (fun z : Plane×Plane => z.2 0) := by fun_prop
  have h3 : Continuous (fun z : Plane×Plane => z.2 1) := by fun_prop
  exact (h0.mul h3).sub (h1.mul h2)

theorem pairDet2_unit_sub (psi theta : ℝ) :
    det2 (polarPoint 1 psi) (polarPoint 1 theta-polarPoint 1 psi)=Real.sin (theta-psi) := by
  simp only [det2,polarPoint,point,PiLp.sub_apply,Matrix.cons_val_zero,Matrix.cons_val_one,
    one_mul,Real.sin_sub]
  ring

/-- Any selected physical pair-direction limit remains in every closed
support half-plane. This scales the actual strict support inequality by
the positive physical distance; no limiting field or mass is substituted. -/
theorem complete_pair_direction_support_nonneg (q : ℕ → SatelliteConfiguration)
    (qLimit : SatelliteConfiguration) (hqt : Tendsto q atTop (nhds qLimit))
    (a b : Satellite) (hc : ∀ n,q n a≠q n b) (c v : Plane)
    (hqa : qLimit a=c)
    (hvt : Tendsto (fun n => physicalPairDirection (q n) a b) atTop (nhds v))
    (j : Satellite)
    (hsupport : ∀ᶠ n in atTop,0<det2 (q n b-q n a) (q n j-q n a)) :
    0≤det2 v (qLimit j-c) := by
  have hqjt : Tendsto (fun n => q n j) atTop (nhds (qLimit j)) := by
    simpa only [Function.comp_def] using (continuous_apply j).tendsto qLimit |>.comp hqt
  have hqat : Tendsto (fun n => q n a) atTop (nhds c) := by
    simpa only [Function.comp_def,hqa] using (continuous_apply a).tendsto qLimit |>.comp hqt
  have ht : Tendsto (fun n => det2 (physicalPairDirection (q n) a b) (q n j-q n a))
      atTop (nhds (det2 v (qLimit j-c))) := by
    exact pairDet2_continuous.continuousAt.tendsto.comp
      (hvt.prodMk_nhds (hqjt.sub hqat))
  apply ge_of_tendsto ht
  filter_upwards [hsupport] with n hn
  have hd : 0<satelliteDistance (q n) a b := norm_pos_iff.mpr (sub_ne_zero.mpr (hc n))
  have he : det2 (q n b-q n a) (q n j-q n a)=
      satelliteDistance (q n) a b*det2 (physicalPairDirection (q n) a b) (q n j-q n a) := by
    rw [physicalPairDirection_gap (q n) a b (hc n)]
    simp only [det2,PiLp.smul_apply,smul_eq_mul]
    ring
  rw [he] at hn
  exact ((mul_pos_iff_of_pos_left hd).mp hn).le

theorem pairDet2_neg_left (u w : Plane) : det2 (-u) w= -det2 u w := by
  simp only [det2,PiLp.neg_apply]
  ring

/-- The full radial alternative is excluded for every selected complete
pair of actual strictly convex roots. The ordered polar-limit span is the
genuine geometry bound from Proposition 4.1. The limiting direction, its
positive orientation and both physical distance ratios are conclusions. -/
theorem normalized_complete_pair_selected_tangential
    (eps : ℕ → ℝ) (mu : ℕ → MassRatio) (x : ℕ → Configuration)
    (heps : ∀ n,0<eps n) (hepst : Tendsto eps atTop (nhds 0))
    (hm : ∀ n,PositiveRatio (mu n))
    (hx : ∀ n,NormalizedCentralConfiguration (masses (eps n) (mu n)) (x n))
    (hconv : ∀ n,StrictConvexInOrder ⟨Equiv.refl Label,rfl⟩ (x n))
    (r theta : ℕ → Satellite → ℝ) (hr : ∀ n,∀ i,0<r n i)
    (hpolar : ∀ n,satellitesRelative (x n)=polarSatellites (r n) (theta n))
    (horder : ∀ n,∀ i j,i<j → 0<theta n j-theta n i ∧ theta n j-theta n i<Real.pi)
    (muLimit : MassRatio) (hmt : Tendsto mu atTop (nhds muLimit))
    (qLimit : SatelliteConfiguration)
    (hqt : Tendsto (fun n => satellitesRelative (x n)) atTop (nhds qLimit))
    (a b : Satellite) (hab : a<b) (c : Plane)
    (hpair : CompleteLimitingSatellitePair qLimit a b c)
    (theta0 : Satellite → ℝ) (hthetat : Tendsto theta atTop (nhds theta0)) (v : Plane)
    (hvt : Tendsto (fun n => physicalPairDirection (satellitesRelative (x n)) a b)
      atTop (nhds v)) :
    b.val=a.val+1 ∧ v=quarterTurn (polarPoint 1 (theta0 a)) ∧
      Tendsto (fun n => eps n*(mu n a+mu n b)/satelliteDistance (satellitesRelative (x n)) a b^3)
        atTop (nhds 0) ∧
      Tendsto (fun n => (theta n b-theta n a)/satelliteDistance (satellitesRelative (x n)) a b)
        atTop (nhds 1) ∧
      Tendsto (fun n => (r n b-r n a)/satelliteDistance (satellitesRelative (x n)) a b)
        atTop (nhds 0) := by
  have hab' := ne_of_lt hab
  have hrat (i : Satellite) : Tendsto (fun n => r n i) atTop (nhds 1) := by
    convert! dominant_satellite_radius_tendsto eps mu x heps hepst hm hx i using 1
    funext n
    rw [hpolar n]
    simp only [polarSatellites,polarPoint_norm,abs_of_pos (hr n i)]
  have htat (i : Satellite) : Tendsto (fun n => theta n i) atTop (nhds (theta0 i)) := by
    simpa only [Function.comp_def] using (continuous_apply i).tendsto theta0 |>.comp hthetat
  have hrt : Tendsto r atTop (nhds (fun _ => (1 : ℝ))) := tendsto_pi_nhds.mpr hrat
  have hangroot : ∀ n i,angularResidual (eps n) (mu n) (r n) (theta n) i=0 :=
    fun n => (polarResiduals_zero_of_normalized (eps n) (mu n) (x n) (hx n)
      (hm n) (heps n) (r n) (theta n) (hr n) (hpolar n)).2
  have hspan : theta0 3-theta0 0<Real.pi :=
    ordered_full_angular_limit_span_lt_pi eps heps hepst mu r theta (fun n => (hm n).1)
      (fun n => (hm n).2) hr hangroot horder muLimit (fun _ => 1) theta0
        (fun _ => rfl) hmt hrt hthetat
  have hpolarlimit (i : Satellite) : qLimit i=polarPoint 1 (theta0 i) := by
    have hqi : Tendsto (fun n => satellitesRelative (x n) i) atTop (nhds (qLimit i)) := by
      simpa only [Function.comp_def] using (continuous_apply i).tendsto qLimit |>.comp hqt
    have hp : Tendsto (fun n => polarPoint (r n i) (theta n i)) atTop
        (nhds (polarPoint 1 (theta0 i))) :=
      (polarPoint_contDiff ∞).continuous.continuousAt.tendsto.comp
        ((hrat i).prodMk_nhds (htat i))
    apply tendsto_nhds_unique hqi
    simpa only [hpolar,polarSatellites,Function.comp_def] using hp
  have hmono : Monotone theta0 := by
    intro i j hij
    rcases hij.eq_or_lt with rfl|hlt
    · rfl
    · have ht := (htat j).sub (htat i)
      exact sub_nonneg.mp (ge_of_tendsto ht (Eventually.of_forall
        (fun n => (horder n i j hlt).1.le)))
  obtain ⟨hadj,hpb⟩ := complete_pair_ordered_angles_adjacent theta0 hmono hspan
    qLimit hpolarlimit a b hab c hpair
  have hqa : qLimit a=c := (hpair a).mpr (Or.inl rfl)
  have hceq : c=polarPoint 1 (theta0 a) := by rw [← hqa,hpolarlimit a]
  have hpair : CompleteLimitingSatellitePair qLimit a b (polarPoint 1 (theta0 a)) := by
    simpa only [hceq] using hpair
  have hbound (i j : Satellite) : theta0 j-theta0 i<Real.pi := by
    have hi := hmono (Fin.zero_le i)
    have hj := hmono (Fin.le_last j)
    change theta0 j≤theta0 3 at hj
    linarith
  have hseparated (j : Satellite) (hj : j∈pairExteriorLabels a b) : theta0 j≠theta0 a := by
    intro he
    have hqj : qLimit j=polarPoint 1 (theta0 a) := by rw [hpolarlimit j,he]
    rcases (hpair j).mp hqj with hja|hjb
    · exact (Finset.mem_erase.mp (Finset.mem_erase.mp hj).2).1 hja
    · exact (Finset.mem_erase.mp hj).1 hjb
  have hsupport (j : Satellite) (hj : j∈pairExteriorLabels a b) :
      0≤det2 v (qLimit j-polarPoint 1 (theta0 a)) :=
    complete_pair_direction_support_nonneg (fun n => satellitesRelative (x n)) qLimit hqt
      a b (fun n => (satellitesRelative_collisionFree (x n) (hx n).1).2 a b hab')
      (polarPoint 1 (theta0 a)) v (hpolarlimit a) hvt j (Eventually.of_forall
        (fun n => strictConvex_adjacent_pair_support (x n) (hconv n) a b hadj j hj))
  have htangent :
      Tendsto (fun n => eps n*(mu n a+mu n b)/satelliteDistance (satellitesRelative (x n)) a b^3)
        atTop (nhds 0) ∧ inner ℝ v (polarPoint 1 (theta0 a))=0 := by
    rcases normalized_complete_pair_direction_alternative eps mu x heps hepst hm hx
      muLimit hmt qLimit hqt a b hab' (polarPoint 1 (theta0 a)) hpair v hvt with ht|hrd
    · exact ht
    · rcases hrd.2 with rfl|rfl
      · have hleft : ∀ j∈pairExteriorLabels a b,
            0<theta0 j-theta0 a ∧ theta0 j-theta0 a<Real.pi := by
          intro j hj
          refine ⟨?_,hbound a j⟩
          apply sub_pos.mpr
          apply lt_of_le_of_ne ?_ (hseparated j hj).symm
          apply le_of_not_gt
          intro hneg
          have hs := hsupport j hj
          rw [hpolarlimit j,pairDet2_unit_sub] at hs
          have hp := Real.sin_pos_of_pos_of_lt_pi (sub_pos.mpr hneg) (hbound j a)
          rw [show theta0 a-theta0 j= -(theta0 j-theta0 a) by ring,Real.sin_neg] at hp
          linarith
        exact (normalized_complete_pair_left_outward_radial_impossible eps mu x heps hepst hm hx
          r theta hr hpolar horder qLimit hqt a b hab (theta0 a) hpair theta0 hthetat
          rfl hpb hleft hvt).elim
      · have hright : ∀ j∈pairExteriorLabels a b,
            -Real.pi<theta0 j-theta0 a ∧ theta0 j-theta0 a<0 := by
          intro j hj
          refine ⟨by linarith [hbound j a],?_⟩
          apply sub_neg.mpr
          apply lt_of_le_of_ne ?_ (hseparated j hj)
          apply le_of_not_gt
          intro hpos
          have hs := hsupport j hj
          rw [hpolarlimit j,pairDet2_neg_left,pairDet2_unit_sub] at hs
          have hp := Real.sin_pos_of_pos_of_lt_pi (sub_pos.mpr hpos) (hbound a j)
          linarith
        exact (normalized_complete_pair_right_inward_radial_impossible eps mu x heps hepst hm hx
          r theta hr hpolar horder qLimit hqt a b hab (theta0 a) hpair theta0 hthetat
          rfl hpb hright hvt).elim
  have hdist (n : ℕ) : 0<satelliteDistance (polarSatellites (r n) (theta n)) a b := by
    rw [← hpolar n]
    exact norm_pos_iff.mpr (sub_ne_zero.mpr
      ((satellitesRelative_collisionFree (x n) (hx n).1).2 a b hab'))
  have hvt' : Tendsto (fun n => physicalPairDirection (polarSatellites (r n) (theta n)) a b)
      atTop (nhds v) := by simpa only [← hpolar] using hvt
  obtain ⟨hg,hrd⟩ := physical_pair_direction_polar_ratio_limits r theta a b (theta0 a)
    (fun n => hr n b) hdist (hrat b) (htat a) (by simpa only [hpb] using htat b) v hvt'
  have hcoef : 0 ≤ inner ℝ v (quarterTurn (polarPoint 1 (theta0 a))) :=
    ge_of_tendsto hg (Eventually.of_forall (fun n =>
      (div_pos (horder n a b hab).1 (hdist n)).le))
  have hnv : ‖v‖=1 := by
    apply tendsto_nhds_unique hvt.norm
    convert! (tendsto_const_nhds : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (nhds 1)) using 1
    funext n
    exact physicalPairDirection_norm (satellitesRelative (x n)) a b
      ((satellitesRelative_collisionFree (x n) (hx n).1).2 a b hab')
  have hvdecomp := polarOrthonormal_decomposition (theta0 a) v
  rw [htangent.2,zero_smul,zero_add] at hvdecomp
  have hJ : inner ℝ (quarterTurn (polarPoint 1 (theta0 a)))
      (quarterTurn (polarPoint 1 (theta0 a)))=1 := by
    rw [quarterTurn_inner_quarterTurn,polarPoint_inner_radial]
    simp
  have hvi : inner ℝ v v=1 := by rw [real_inner_self_eq_norm_sq,hnv]; norm_num
  have hi := congrArg (fun z : Plane => inner ℝ z z) hvdecomp
  rw [hvi,real_inner_smul_left,real_inner_smul_right,hJ,mul_one] at hi
  have hcoeffone : inner ℝ v (quarterTurn (polarPoint 1 (theta0 a)))=1 := by nlinarith
  have hvJ : v=quarterTurn (polarPoint 1 (theta0 a)) := by simpa only [hcoeffone,one_smul] using hvdecomp
  refine ⟨hadj,hvJ,htangent.1,?_,?_⟩
  · simpa only [hpolar,hcoeffone] using hg
  · simpa only [hpolar,htangent.2] using hrd

theorem physicalPairExteriorAngularField_eq_source_sum (mu r theta : Satellite → ℝ)
    (a b : Satellite) (rho v : ℝ) :
    physicalPairExteriorAngularField mu r theta a b rho v=
      ∑ j∈pairExteriorLabels a b,mu j*physicalSourceAngularField (r j) (theta j) rho v := by
  unfold physicalPairExteriorAngularField physicalSourceAngularField
  apply Finset.sum_congr rfl
  intro j _
  ring

/-- Full polar target error for the actual complete exterior angular field.
The estimate is source-by-source with CURRENT masses and contains their
exact sum sigma. Radial and angular differences are both retained. -/
theorem complete_pair_exterior_angular_error_bound
    (mu : ℕ → MassRatio) (hm : ∀ n,PositiveRatio (mu n))
    (r theta : ℕ → Satellite → ℝ)
    (hrt : ∀ i,Tendsto (fun n => r n i) atTop (nhds 1))
    (theta0 : Satellite → ℝ) (hthetat : Tendsto theta atTop (nhds theta0))
    (a b : Satellite) (hab : a≠b) (hpair : theta0 b=theta0 a)
    (hsep : ∀ j∈pairExteriorLabels a b,polarPoint 1 (theta0 j)≠polarPoint 1 (theta0 a)) :
    ∃ C : ℝ,0<C ∧ ∀ᶠ n in atTop,
      |physicalPairExteriorAngularField (mu n) (r n) (theta n) a b (r n b) (theta n b)-
        physicalPairExteriorAngularField (mu n) (r n) (theta n) a b (r n a) (theta n a)|≤
        C*(1-(mu n a+mu n b))*max |r n b-r n a| |theta n b-theta n a| := by
  have htat (i : Satellite) : Tendsto (fun n => theta n i) atTop (nhds (theta0 i)) := by
    simpa only [Function.comp_def] using (continuous_apply i).tendsto theta0 |>.comp hthetat
  have hw (j : Satellite) : ∃ K : ℝ,0<K ∧ ∀ᶠ n in atTop,
      j∈pairExteriorLabels a b →
      |physicalSourceAngularField (r n j) (theta n j) (r n b) (theta n b)-
        physicalSourceAngularField (r n j) (theta n j) (r n a) (theta n a)|≤
        K*max |r n b-r n a| |theta n b-theta n a| := by
    by_cases hj : j∈pairExteriorLabels a b
    · obtain ⟨K,U,hU,hLip⟩ := ((physicalSourceAngularField_joint_contDiffAt
        ((1,theta0 j),(1,theta0 a)) (by norm_num) (hsep j hj)).of_le
          (by norm_num : (1 : ℕ∞ω)≤∞)).exists_lipschitzOnWith
      have ha := ((hrt j).prodMk_nhds (htat j)).prodMk_nhds
        ((hrt a).prodMk_nhds (htat a))
      have hb : Tendsto (fun n => ((r n j,theta n j),(r n b,theta n b))) atTop
          (nhds ((1,theta0 j),(1,theta0 a))) := by
        simpa only [hpair] using ((hrt j).prodMk_nhds (htat j)).prodMk_nhds
          ((hrt b).prodMk_nhds (htat b))
      refine ⟨(K : ℝ)+1,by positivity,?_⟩
      filter_upwards [ha.eventually hU,hb.eventually hU] with n hna hnb _
      have h := hLip.dist_le_mul _ hnb _ hna
      have hd : dist ((r n j,theta n j),(r n b,theta n b))
          ((r n j,theta n j),(r n a,theta n a))=
          max |r n b-r n a| |theta n b-theta n a| := by
        simp only [Prod.dist_eq,dist_self,Real.dist_eq]
        exact max_eq_right (le_max_of_le_left (abs_nonneg _))
      rw [Real.dist_eq,hd] at h
      exact h.trans (mul_le_mul_of_nonneg_right (by linarith : (K : ℝ)≤(K : ℝ)+1)
        (le_max_of_le_left (abs_nonneg _)))
    · exact ⟨1,by norm_num,Eventually.of_forall (fun _ he => (hj he).elim)⟩
  choose K hK hbound using hw
  let C := (∑ j∈pairExteriorLabels a b,K j)+1
  have hC : 0<C := by
    have hsum := Finset.sum_nonneg (fun j (_ : j∈pairExteriorLabels a b) => (hK j).le)
    dsimp [C]; linarith
  have heach : ∀ᶠ n in atTop,∀ j∈pairExteriorLabels a b,
      |physicalSourceAngularField (r n j) (theta n j) (r n b) (theta n b)-
        physicalSourceAngularField (r n j) (theta n j) (r n a) (theta n a)|≤
        K j*max |r n b-r n a| |theta n b-theta n a| := by
    apply (Finset.eventually_all (pairExteriorLabels a b)).mpr
    intro j hj
    exact (hbound j).mono (fun _ he => he hj)
  refine ⟨C,hC,?_⟩
  filter_upwards [heach] with n hn
  rw [physicalPairExteriorAngularField_eq_source_sum,physicalPairExteriorAngularField_eq_source_sum,
    ← Finset.sum_sub_distrib]
  simp only [← mul_sub]
  calc
    _≤∑ j∈pairExteriorLabels a b,
        |mu n j*(physicalSourceAngularField (r n j) (theta n j) (r n b) (theta n b)-
          physicalSourceAngularField (r n j) (theta n j) (r n a) (theta n a))| :=
      Finset.abs_sum_le_sum_abs _ _
    _≤∑ j∈pairExteriorLabels a b,
        mu n j*(C*max |r n b-r n a| |theta n b-theta n a|) := by
      apply Finset.sum_le_sum
      intro j hj
      have hjK : K j≤C := by
        have hs := Finset.single_le_sum (fun l (_ : l∈pairExteriorLabels a b) => (hK l).le) hj
        dsimp [C]; linarith
      rw [abs_mul,abs_of_pos ((hm n).1 j)]
      exact mul_le_mul_of_nonneg_left ((hn j hj).trans
        (mul_le_mul_of_nonneg_right hjK (le_max_of_le_left (abs_nonneg _)))) ((hm n).1 j).le
    _=C*(1-(mu n a+mu n b))*max |r n b-r n a| |theta n b-theta n a| := by
      rw [← Finset.sum_mul,pairExteriorMass_eq (mu n) a b hab (hm n).2]
      ring

theorem pair_single_tangential_coefficient_lower (rho d : ℝ)
    (hr : (1/2 : ℝ)≤rho) (hd : 0<d) (hsmall : d≤1/4) :
    1/(4*d^3)≤rho/d^3-1/rho^2 := by
  have hrpos : 0<rho := by linarith
  have hd3 : 0<d^3 := pow_pos hd 3
  have htwo : 2*d≤rho := by linarith
  have hcube := pow_le_pow_left₀ (by positivity : 0≤2*d) htwo 3
  have hden : 2*d^3≤rho^3 := by nlinarith [pow_pos hd 3]
  have hinv : 1/rho^2≤rho/(2*d^3) := by
    apply (div_le_div_iff₀ (sq_pos_of_pos hrpos) (by positivity : 0<2*d^3)).mpr
    nlinarith
  have hhalf : 1/(4*d^3)≤rho/(2*d^3) := by
    apply (div_le_div_iff₀ (by positivity : 0<4*d^3) (by positivity : 0<2*d^3)).mpr
    nlinarith
  have heq : rho/d^3=2*(rho/(2*d^3)) := by ring
  rw [heq]
  linarith

/-- Quantitative version of the genuine angular difference. Each CURRENT
pair mass multiplies the same uniform positive coefficient; no individual
fraction is divided out. -/
theorem pair_tangential_coefficient_lower (mu r theta : Satellite → ℝ) (a b : Satellite)
    (hm : ∀ i,0<mu i) (hra : (1/2 : ℝ)≤r a) (hrb : (1/2 : ℝ)≤r b)
    (hd : 0<satelliteDistance (polarSatellites r theta) a b)
    (hsmall : satelliteDistance (polarSatellites r theta) a b≤1/4) :
    (mu a+mu b)/(4*satelliteDistance (polarSatellites r theta) a b^3)≤
      (mu a*r a+mu b*r b)/satelliteDistance (polarSatellites r theta) a b^3-
        mu a/(r a)^2-mu b/(r b)^2 := by
  have ha := mul_le_mul_of_nonneg_left
    (pair_single_tangential_coefficient_lower (r a) _ hra hd hsmall) (hm a).le
  have hb := mul_le_mul_of_nonneg_left
    (pair_single_tangential_coefficient_lower (r b) _ hrb hd hsmall) (hm b).le
  have heq : (mu a*r a+mu b*r b)/satelliteDistance (polarSatellites r theta) a b^3-
      mu a/(r a)^2-mu b/(r b)^2=
      mu a*(r a/satelliteDistance (polarSatellites r theta) a b^3-1/(r a)^2)+
        mu b*(r b/satelliteDistance (polarSatellites r theta) a b^3-1/(r b)^2) := by ring
  have hsum : (mu a+mu b)/(4*satelliteDistance (polarSatellites r theta) a b^3)=
      mu a*(1/(4*satelliteDistance (polarSatellites r theta) a b^3))+
        mu b*(1/(4*satelliteDistance (polarSatellites r theta) a b^3)) := by ring
  rw [heq,hsum]
  exact add_le_add ha hb

/-- Exact angular difference plus a genuine CURRENT exterior error gives
the pair-mass cubic upper bound. The quotient assumptions here are
quantitative neighborhoods of the previously derived positive tangent
limit, and will be supplied by the actual sequence theorem below. -/
theorem pair_mass_cube_bound_of_angular_difference
    (C : ℝ) (mu r theta : Satellite → ℝ) (a b : Satellite)
    (hm : ∀ i,0<mu i) (hra : (1/2 : ℝ)≤r a) (hrb : (1/2 : ℝ)≤r b)
    (hd : 0<satelliteDistance (polarSatellites r theta) a b)
    (hsmall : satelliteDistance (polarSatellites r theta) a b≤1/4)
    (hgap : (1/2 : ℝ)≤(theta b-theta a)/satelliteDistance (polarSatellites r theta) a b)
    (hsinc : (1/2 : ℝ)≤Real.sinc (theta b-theta a))
    (heq : physicalPairExteriorAngularField mu r theta a b (r b) (theta b)-
      physicalPairExteriorAngularField mu r theta a b (r a) (theta a)=
      Real.sin (theta b-theta a)*
        ((mu a*r a+mu b*r b)/satelliteDistance (polarSatellites r theta) a b^3-
          mu a/(r a)^2-mu b/(r b)^2))
    (hupper : physicalPairExteriorAngularField mu r theta a b (r b) (theta b)-
      physicalPairExteriorAngularField mu r theta a b (r a) (theta a)≤
      C*(1-(mu a+mu b))*satelliteDistance (polarSatellites r theta) a b) :
    (mu a+mu b)/satelliteDistance (polarSatellites r theta) a b^3≤16*C*(1-(mu a+mu b)) := by
  let d := satelliteDistance (polarSatellites r theta) a b
  have hg : d/2≤theta b-theta a := by
    have h := (le_div_iff₀ hd).mp hgap
    dsimp [d]
    linarith
  have hgpos : 0<theta b-theta a := lt_of_lt_of_le (by dsimp [d]; positivity) hg
  have hsin : d/4≤Real.sin (theta b-theta a) := by
    rw [← sinc_mul_argument (theta b-theta a)]
    have h := mul_le_mul_of_nonneg_left hsinc hgpos.le
    nlinarith
  have hco := pair_tangential_coefficient_lower mu r theta a b hm hra hrb hd hsmall
  have hcononneg : 0≤(mu a+mu b)/(4*d^3) :=
    div_nonneg (add_pos (hm a) (hm b)).le (by dsimp [d]; positivity)
  have hprod := mul_le_mul hsin hco hcononneg
    (lt_of_lt_of_le (show 0<d/4 by dsimp [d]; positivity) hsin).le
  rw [← heq] at hprod
  have h := mul_le_mul_of_nonneg_right (hprod.trans hupper) (show 0≤16/d by dsimp [d]; positivity)
  convert! h using 1 <;> dsimp [d] <;> field_simp [ne_of_gt hd]; ring

/-- Actual selected complete-pair roots have bounded current nu/d³, nu→0,
and the source's epsilon*sigma*d radial estimate. Every branch condition
is supplied by the physical direction/support theorem above. -/
theorem normalized_complete_pair_selected_mass_scale
    (eps : ℕ → ℝ) (mu : ℕ → MassRatio) (x : ℕ → Configuration)
    (heps : ∀ n,0<eps n) (hepst : Tendsto eps atTop (nhds 0))
    (hm : ∀ n,PositiveRatio (mu n))
    (hx : ∀ n,NormalizedCentralConfiguration (masses (eps n) (mu n)) (x n))
    (hconv : ∀ n,StrictConvexInOrder ⟨Equiv.refl Label,rfl⟩ (x n))
    (r theta : ℕ → Satellite → ℝ) (hr : ∀ n,∀ i,0<r n i)
    (hpolar : ∀ n,satellitesRelative (x n)=polarSatellites (r n) (theta n))
    (horder : ∀ n,∀ i j,i<j → 0<theta n j-theta n i ∧ theta n j-theta n i<Real.pi)
    (muLimit : MassRatio) (hmt : Tendsto mu atTop (nhds muLimit))
    (qLimit : SatelliteConfiguration)
    (hqt : Tendsto (fun n => satellitesRelative (x n)) atTop (nhds qLimit))
    (a b : Satellite) (hab : a<b) (c : Plane)
    (hpair : CompleteLimitingSatellitePair qLimit a b c)
    (theta0 : Satellite → ℝ) (hthetat : Tendsto theta atTop (nhds theta0)) (v : Plane)
    (hvt : Tendsto (fun n => physicalPairDirection (satellitesRelative (x n)) a b)
      atTop (nhds v)) :
    (∃ C : ℝ,0<C ∧ ∀ᶠ n in atTop,
      (mu n a+mu n b)/satelliteDistance (satellitesRelative (x n)) a b^3≤
        C*(1-(mu n a+mu n b))) ∧
    Tendsto (fun n => mu n a+mu n b) atTop (nhds 0) ∧
    (∃ C : ℝ,0<C ∧ ∀ᶠ n in atTop,
      |r n b-r n a|≤C*eps n*(1-(mu n a+mu n b))*satelliteDistance (satellitesRelative (x n)) a b) := by
  have hab' := ne_of_lt hab
  obtain ⟨_,_,hlambda,hg,hrad⟩ := normalized_complete_pair_selected_tangential eps mu x heps hepst hm hx
    hconv r theta hr hpolar horder muLimit hmt qLimit hqt a b hab c hpair theta0 hthetat v hvt
  have hdistt := complete_pair_distance_tendsto_zero (fun n => satellitesRelative (x n))
    qLimit hqt a b c hpair
  have hdist (n : ℕ) : 0<satelliteDistance (satellitesRelative (x n)) a b :=
    norm_pos_iff.mpr (sub_ne_zero.mpr
      ((satellitesRelative_collisionFree (x n) (hx n).1).2 a b hab'))
  have hgap0 : Tendsto (fun n => theta n b-theta n a) atTop (nhds 0) := by
    convert! hg.mul hdistt using 1
    · funext n; field_simp [ne_of_gt (hdist n)]
    · norm_num
  have hrat (i : Satellite) : Tendsto (fun n => r n i) atTop (nhds 1) := by
    convert! dominant_satellite_radius_tendsto eps mu x heps hepst hm hx i using 1
    funext n
    rw [hpolar n]
    simp only [polarSatellites,polarPoint_norm,abs_of_pos (hr n i)]
  have htat (i : Satellite) : Tendsto (fun n => theta n i) atTop (nhds (theta0 i)) := by
    simpa only [Function.comp_def] using (continuous_apply i).tendsto theta0 |>.comp hthetat
  have hpb : theta0 b=theta0 a := sub_eq_zero.mp (tendsto_nhds_unique
    ((htat b).sub (htat a)) hgap0)
  have hpolarlimit (i : Satellite) : qLimit i=polarPoint 1 (theta0 i) := by
    have hqi : Tendsto (fun n => satellitesRelative (x n) i) atTop (nhds (qLimit i)) := by
      simpa only [Function.comp_def] using (continuous_apply i).tendsto qLimit |>.comp hqt
    have hp : Tendsto (fun n => polarPoint (r n i) (theta n i)) atTop
        (nhds (polarPoint 1 (theta0 i))) :=
      (polarPoint_contDiff ∞).continuous.continuousAt.tendsto.comp
        ((hrat i).prodMk_nhds (htat i))
    apply tendsto_nhds_unique hqi
    simpa only [hpolar,polarSatellites,Function.comp_def] using hp
  have hsep (j : Satellite) (hj : j∈pairExteriorLabels a b) :
      polarPoint 1 (theta0 j)≠polarPoint 1 (theta0 a) := by
    rw [← hpolarlimit j,← hpolarlimit a,(hpair a).mpr (Or.inl rfl)]
    intro he
    rcases (hpair j).mp he with hja|hjb
    · exact (Finset.mem_erase.mp (Finset.mem_erase.mp hj).2).1 hja
    · exact (Finset.mem_erase.mp hj).1 hjb
  obtain ⟨K,hK,hH⟩ := complete_pair_exterior_angular_error_bound mu hm r theta hrat
    theta0 hthetat a b hab' hpb hsep
  have hsinct : Tendsto (fun n => Real.sinc (theta n b-theta n a)) atTop (nhds 1) := by
    simpa only [Function.comp_def,Real.sinc_zero] using Real.continuous_sinc.continuousAt.tendsto.comp hgap0
  have hQ := normalized_complete_pair_tangential_difference_positive eps mu x heps hepst hm hx
    r theta hr hpolar horder qLimit hqt a b hab c hpair
  have hbound : ∀ᶠ n in atTop,
      (mu n a+mu n b)/satelliteDistance (satellitesRelative (x n)) a b^3≤
        (32*K)*(1-(mu n a+mu n b)) := by
    filter_upwards [hH,hQ,hsinct.eventually (Ioi_mem_nhds (by norm_num : (1/2 : ℝ)<1)),
      (hrat a).eventually (Ioi_mem_nhds (by norm_num : (1/2 : ℝ)<1)),
      (hrat b).eventually (Ioi_mem_nhds (by norm_num : (1/2 : ℝ)<1)),
      hdistt.eventually (Iio_mem_nhds (by norm_num : (0 : ℝ)<1/4)),
      hg.eventually (Ioi_mem_nhds (by norm_num : (1/2 : ℝ)<1)),
      hg.eventually (Iio_mem_nhds (by norm_num : (1 : ℝ)<2)),
      hrad.abs.eventually (Iio_mem_nhds (by norm_num : |(0 : ℝ)|<1))]
      with n hnH hnQ hnsinc hna hnb hnd hng hng2 hnr
    have hdr := hdist n
    have hrr : |r n b-r n a|≤2*satelliteDistance (satellitesRelative (x n)) a b := by
      rw [abs_div,abs_of_pos hdr] at hnr
      have h := (div_lt_iff₀ hdr).mp hnr
      linarith
    have hgg : |theta n b-theta n a|≤2*satelliteDistance (satellitesRelative (x n)) a b := by
      rw [abs_of_pos (horder n a b hab).1]
      exact ((div_lt_iff₀ hdr).mp hng2).le
    have hmax := max_le hrr hgg
    have hupper := (le_abs_self _).trans (hnH.trans
      (mul_le_mul_of_nonneg_left hmax (mul_nonneg hK.le (pairExteriorMass_pos (mu n) (hm n) a b hab').le)))
    have hupper' : physicalPairExteriorAngularField (mu n) (r n) (theta n) a b (r n b) (theta n b)-
        physicalPairExteriorAngularField (mu n) (r n) (theta n) a b (r n a) (theta n a)≤
        (2*K)*(1-(mu n a+mu n b))*satelliteDistance (polarSatellites (r n) (theta n)) a b := by
      rw [← hpolar n]
      nlinarith
    have h := pair_mass_cube_bound_of_angular_difference (2*K) (mu n) (r n) (theta n) a b
      (hm n).1 hna.le hnb.le (by rw [← hpolar n]; exact hdr)
      (by rw [← hpolar n]; exact hnd.le)
      (by rw [← hpolar n]; exact hng.le) hnsinc.le hnQ.1 hupper'
    rw [← hpolar n] at h
    nlinarith
  have hnu0 : Tendsto (fun n => mu n a+mu n b) atTop (nhds 0) := by
    have hcube := hdistt.pow 3
    have hupp : ∀ᶠ n in atTop,mu n a+mu n b≤(32*K)*satelliteDistance (satellitesRelative (x n)) a b^3 := by
      filter_upwards [hbound] with n hn
      have hnu : 0<mu n a+mu n b := add_pos ((hm n).1 a) ((hm n).1 b)
      have hsig : 1-(mu n a+mu n b)≤1 := by linarith
      have hs := hn.trans (mul_le_mul_of_nonneg_left hsig (by positivity : 0≤32*K))
      exact (div_le_iff₀ (pow_pos (hdist n) 3)).mp (by simpa only [mul_one] using hs)
    have hmult : Tendsto (fun n => (32*K)*satelliteDistance (satellitesRelative (x n)) a b^3)
        atTop (nhds 0) := by
      simpa using
        (tendsto_const_nhds : Tendsto (fun _ : ℕ => 32*K) atTop (nhds (32*K))).mul hcube
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le'
      tendsto_const_nhds hmult
      (Eventually.of_forall (fun n => (add_pos ((hm n).1 a) ((hm n).1 b)).le)) hupp
  exact ⟨⟨32*K,by positivity,hbound⟩,hnu0,
    normalized_complete_pair_radial_bound_of_tangential eps mu x heps hm hx r theta hr hpolar
      qLimit hqt a b hab' c hpair hlambda hgap0⟩

/-- A complete pair's positive tangential direction converges on the
original sequence. Compactness of the true physical unit directions and
the proved selected-limit theorem remove the direction-convergence
hypothesis; no additional asymptotic condition remains. -/
theorem normalized_complete_pair_direction_tendsto
    (eps : ℕ → ℝ) (mu : ℕ → MassRatio) (x : ℕ → Configuration)
    (heps : ∀ n,0<eps n) (hepst : Tendsto eps atTop (nhds 0))
    (hm : ∀ n,PositiveRatio (mu n))
    (hx : ∀ n,NormalizedCentralConfiguration (masses (eps n) (mu n)) (x n))
    (hconv : ∀ n,StrictConvexInOrder ⟨Equiv.refl Label,rfl⟩ (x n))
    (r theta : ℕ → Satellite → ℝ) (hr : ∀ n,∀ i,0<r n i)
    (hpolar : ∀ n,satellitesRelative (x n)=polarSatellites (r n) (theta n))
    (horder : ∀ n,∀ i j,i<j → 0<theta n j-theta n i ∧ theta n j-theta n i<Real.pi)
    (muLimit : MassRatio) (hmt : Tendsto mu atTop (nhds muLimit))
    (qLimit : SatelliteConfiguration)
    (hqt : Tendsto (fun n => satellitesRelative (x n)) atTop (nhds qLimit))
    (a b : Satellite) (hab : a<b) (c : Plane)
    (hpair : CompleteLimitingSatellitePair qLimit a b c)
    (theta0 : Satellite → ℝ) (hthetat : Tendsto theta atTop (nhds theta0)) :
    Tendsto (fun n => physicalPairDirection (satellitesRelative (x n)) a b)
      atTop (nhds (quarterTurn (polarPoint 1 (theta0 a)))) := by
  let u : ℕ → Plane := fun n => physicalPairDirection (satellitesRelative (x n)) a b
  let target := quarterTurn (polarPoint 1 (theta0 a))
  have hunit (n : ℕ) : ‖u n‖=1 := physicalPairDirection_norm (satellitesRelative (x n)) a b
    ((satellitesRelative_collisionFree (x n) (hx n).1).2 a b (ne_of_lt hab))
  change Tendsto u atTop (nhds target)
  apply Metric.tendsto_atTop.mpr
  intro eta heta
  by_contra hbad
  push Not at hbad
  have hfreq : ∃ᶠ n in atTop,eta≤dist (u n) target := frequently_atTop.mpr hbad
  let S : Set Plane := Metric.sphere 0 1 ∩ {z | eta≤dist z target}
  have hS : IsCompact S := (isCompact_sphere (0 : Plane) 1).inter_right
    (isClosed_le continuous_const (continuous_id.dist continuous_const))
  have hfreqS : ∃ᶠ n in atTop,u n∈S := hfreq.mono (fun n hn =>
    ⟨by simpa only [Metric.mem_sphere,dist_eq_norm,sub_zero] using hunit n,hn⟩)
  obtain ⟨v,hv,phi,hphi,hvt⟩ := hS.tendsto_subseq' hfreqS
  have hp := hphi.tendsto_atTop
  have hsel := normalized_complete_pair_selected_tangential (eps ∘ phi) (mu ∘ phi) (x ∘ phi)
    (fun n => heps (phi n)) (hepst.comp hp) (fun n => hm (phi n)) (fun n => hx (phi n))
    (fun n => hconv (phi n)) (r ∘ phi) (theta ∘ phi) (fun n => hr (phi n))
    (fun n => hpolar (phi n)) (fun n => horder (phi n)) muLimit (hmt.comp hp) qLimit
    (hqt.comp hp) a b hab c hpair theta0 (hthetat.comp hp) v hvt
  have hvJ : v=target := hsel.2.1
  have he : eta≤0 := by simpa only [Set.mem_ofPred_eq,hvJ,dist_self] using hv.2
  linarith

/-- Complete-pair first-stage scale package on the original actual root
sequence. The selected-direction prerequisite has been discharged. The
positive limiting probe coefficient is a subsequent theorem, not part of
the current package. -/
theorem normalized_complete_pair_tangential_mass_scale
    (eps : ℕ → ℝ) (mu : ℕ → MassRatio) (x : ℕ → Configuration)
    (heps : ∀ n,0<eps n) (hepst : Tendsto eps atTop (nhds 0))
    (hm : ∀ n,PositiveRatio (mu n))
    (hx : ∀ n,NormalizedCentralConfiguration (masses (eps n) (mu n)) (x n))
    (hconv : ∀ n,StrictConvexInOrder ⟨Equiv.refl Label,rfl⟩ (x n))
    (r theta : ℕ → Satellite → ℝ) (hr : ∀ n,∀ i,0<r n i)
    (hpolar : ∀ n,satellitesRelative (x n)=polarSatellites (r n) (theta n))
    (horder : ∀ n,∀ i j,i<j → 0<theta n j-theta n i ∧ theta n j-theta n i<Real.pi)
    (muLimit : MassRatio) (hmt : Tendsto mu atTop (nhds muLimit))
    (qLimit : SatelliteConfiguration)
    (hqt : Tendsto (fun n => satellitesRelative (x n)) atTop (nhds qLimit))
    (a b : Satellite) (hab : a<b) (c : Plane)
    (hpair : CompleteLimitingSatellitePair qLimit a b c)
    (theta0 : Satellite → ℝ) (hthetat : Tendsto theta atTop (nhds theta0)) :
    b.val=a.val+1 ∧
    Tendsto (fun n => (theta n b-theta n a)/satelliteDistance (satellitesRelative (x n)) a b)
      atTop (nhds 1) ∧
    Tendsto (fun n => (r n b-r n a)/satelliteDistance (satellitesRelative (x n)) a b)
      atTop (nhds 0) ∧
    (∃ C : ℝ,0<C ∧ ∀ᶠ n in atTop,
      (mu n a+mu n b)/satelliteDistance (satellitesRelative (x n)) a b^3≤
        C*(1-(mu n a+mu n b))) ∧
    Tendsto (fun n => mu n a+mu n b) atTop (nhds 0) ∧
    (∃ C : ℝ,0<C ∧ ∀ᶠ n in atTop,
      |r n b-r n a|≤C*eps n*(1-(mu n a+mu n b))*satelliteDistance (satellitesRelative (x n)) a b) := by
  have hv := normalized_complete_pair_direction_tendsto eps mu x heps hepst hm hx hconv
    r theta hr hpolar horder muLimit hmt qLimit hqt a b hab c hpair theta0 hthetat
  obtain ⟨hadj,_,_,hg,hrd⟩ := normalized_complete_pair_selected_tangential eps mu x heps hepst hm hx hconv
    r theta hr hpolar horder muLimit hmt qLimit hqt a b hab c hpair theta0 hthetat
      (quarterTurn (polarPoint 1 (theta0 a))) hv
  obtain ⟨hC,hnu,hR⟩ := normalized_complete_pair_selected_mass_scale eps mu x heps hepst hm hx hconv
    r theta hr hpolar horder muLimit hmt qLimit hqt a b hab c hpair theta0 hthetat
      (quarterTurn (polarPoint 1 (theta0 a))) hv
  exact ⟨hadj,hg,hrd,hC,hnu,hR⟩

/-- Two distinct complete two-label classes exhaust the four satellite
labels. Both classes' current masses would tend to zero by the actual
scale theorem, contradicting the unchanged unit mass normalization. -/
theorem normalized_complete_pairs_cannot_coexist
    (eps : ℕ → ℝ) (mu : ℕ → MassRatio) (x : ℕ → Configuration)
    (heps : ∀ n,0<eps n) (hepst : Tendsto eps atTop (nhds 0))
    (hm : ∀ n,PositiveRatio (mu n))
    (hx : ∀ n,NormalizedCentralConfiguration (masses (eps n) (mu n)) (x n))
    (hconv : ∀ n,StrictConvexInOrder ⟨Equiv.refl Label,rfl⟩ (x n))
    (r theta : ℕ → Satellite → ℝ) (hr : ∀ n,∀ i,0<r n i)
    (hpolar : ∀ n,satellitesRelative (x n)=polarSatellites (r n) (theta n))
    (horder : ∀ n,∀ i j,i<j → 0<theta n j-theta n i ∧ theta n j-theta n i<Real.pi)
    (muLimit : MassRatio) (hmt : Tendsto mu atTop (nhds muLimit))
    (qLimit : SatelliteConfiguration)
    (hqt : Tendsto (fun n => satellitesRelative (x n)) atTop (nhds qLimit))
    (a b u w : Satellite) (hab : a<b) (huw : u<w) (c d : Plane) (hcd : c≠d)
    (hpair : CompleteLimitingSatellitePair qLimit a b c)
    (hpair2 : CompleteLimitingSatellitePair qLimit u w d)
    (theta0 : Satellite → ℝ) (hthetat : Tendsto theta atTop (nhds theta0)) : False := by
  have hdisj : Disjoint ({a,b} : Finset Satellite) {u,w} := by
    apply Finset.disjoint_left.mpr
    intro j hj1 hj2
    have hjc : qLimit j=c := (hpair j).mpr (by simpa only [Finset.mem_insert,Finset.mem_singleton] using hj1)
    have hjd : qLimit j=d := (hpair2 j).mpr (by simpa only [Finset.mem_insert,Finset.mem_singleton] using hj2)
    exact hcd (hjc.symm.trans hjd)
  have hU : ({a,b} : Finset Satellite)∪{u,w}=Finset.univ := by
    apply Finset.eq_univ_of_card
    rw [Finset.card_union_of_disjoint hdisj]
    simp [ne_of_lt hab,ne_of_lt huw]
  have hsum (n : ℕ) : (mu n a+mu n b)+(mu n u+mu n w)=1 := by
    have he := (hm n).2
    rw [← hU,Finset.sum_union hdisj] at he
    simpa [ne_of_lt hab,ne_of_lt huw] using he
  have hmass1 := (normalized_complete_pair_tangential_mass_scale eps mu x heps hepst hm hx hconv
    r theta hr hpolar horder muLimit hmt qLimit hqt a b hab c hpair theta0 hthetat).2.2.2.2.1
  have hmass2 := (normalized_complete_pair_tangential_mass_scale eps mu x heps hepst hm hx hconv
    r theta hr hpolar horder muLimit hmt qLimit hqt u w huw d hpair2 theta0 hthetat).2.2.2.2.1
  have hs : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (nhds 0) := by
    simpa only [hsum,add_zero] using hmass1.add hmass2
  have he : (1 : ℝ)=0 := tendsto_nhds_unique tendsto_const_nhds hs
  norm_num at he

theorem pairExteriorLabels_card (a b : Satellite) (hab : a≠b) :
    (pairExteriorLabels a b).card=2 := by
  have hb : b∈Finset.univ.erase a := Finset.mem_erase.mpr ⟨Ne.symm hab,Finset.mem_univ b⟩
  unfold pairExteriorLabels
  rw [Finset.card_erase_of_mem hb,Finset.card_erase_of_mem (Finset.mem_univ a),Finset.card_univ]
  norm_num

theorem pairExteriorLabels_eq_two (a b u w : Satellite) (hab : a≠b)
    (hu : u∈pairExteriorLabels a b) (hw : w∈pairExteriorLabels a b) (huw : u≠w) :
    pairExteriorLabels a b={u,w} := by
  apply Eq.symm
  apply Finset.eq_of_subset_of_card_le
  · intro j hj
    rcases Finset.mem_insert.mp hj with rfl|hj
    · exact hu
    · exact (Finset.mem_singleton.mp hj) ▸ hw
  · rw [pairExteriorLabels_card a b hab,Finset.card_pair huw]

/-- The other two labels of an actual complete pair have distinct physical
limits. If they collided, the complete complementary pair would violate
the proved two-pair exclusion. -/
theorem normalized_complete_pair_exterior_limits_distinct
    (eps : ℕ → ℝ) (mu : ℕ → MassRatio) (x : ℕ → Configuration)
    (heps : ∀ n,0<eps n) (hepst : Tendsto eps atTop (nhds 0))
    (hm : ∀ n,PositiveRatio (mu n))
    (hx : ∀ n,NormalizedCentralConfiguration (masses (eps n) (mu n)) (x n))
    (hconv : ∀ n,StrictConvexInOrder ⟨Equiv.refl Label,rfl⟩ (x n))
    (r theta : ℕ → Satellite → ℝ) (hr : ∀ n,∀ i,0<r n i)
    (hpolar : ∀ n,satellitesRelative (x n)=polarSatellites (r n) (theta n))
    (horder : ∀ n,∀ i j,i<j → 0<theta n j-theta n i ∧ theta n j-theta n i<Real.pi)
    (muLimit : MassRatio) (hmt : Tendsto mu atTop (nhds muLimit))
    (qLimit : SatelliteConfiguration)
    (hqt : Tendsto (fun n => satellitesRelative (x n)) atTop (nhds qLimit))
    (a b : Satellite) (hab : a<b) (c : Plane)
    (hpair : CompleteLimitingSatellitePair qLimit a b c)
    (theta0 : Satellite → ℝ) (hthetat : Tendsto theta atTop (nhds theta0))
    (u w : Satellite) (huw : u<w)
    (hu : u∈pairExteriorLabels a b) (hw : w∈pairExteriorLabels a b) : qLimit u≠qLimit w := by
  have hset := pairExteriorLabels_eq_two a b u w (ne_of_lt hab) hu hw (ne_of_lt huw)
  intro he
  have huc : qLimit u≠c := by
    intro hh
    rcases (hpair u).mp hh with hja|hjb
    · exact (Finset.mem_erase.mp (Finset.mem_erase.mp hu).2).1 hja
    · exact (Finset.mem_erase.mp hu).1 hjb
  have hpair2 : CompleteLimitingSatellitePair qLimit u w (qLimit u) := by
    intro j
    constructor
    · intro hj
      by_cases hja : j=a
      · rw [hja,(hpair a).mpr (Or.inl rfl)] at hj
        exact (huc hj.symm).elim
      by_cases hjb : j=b
      · rw [hjb,(hpair b).mpr (Or.inr rfl)] at hj
        exact (huc hj.symm).elim
      have hjext : j∈pairExteriorLabels a b := by
        simp only [pairExteriorLabels,Finset.mem_erase,Finset.mem_univ,and_true]
        exact ⟨hjb,hja⟩
      rw [hset] at hjext
      simpa only [Finset.mem_insert,Finset.mem_singleton] using hjext
    · rintro (rfl|rfl)
      · rfl
      · exact he.symm
  exact normalized_complete_pairs_cannot_coexist eps mu x heps hepst hm hx hconv r theta hr hpolar
    horder muLimit hmt qLimit hqt a b u w hab huw c (qLimit u) huc.symm hpair hpair2 theta0 hthetat

def physicalSourceFullAngularField (eps s angle rho v : ℝ) : ℝ :=
  rho*s*Real.sin (angle-v)*((‖polarPoint rho v-polarPoint s angle‖^3)⁻¹-(1+eps)⁻¹)

theorem physicalSourceFullAngularField_joint_contDiffAt
    (d : ℝ×((ℝ×ℝ)×(ℝ×ℝ))) (heps : 1+d.1≠0)
    (hsep : polarPoint d.2.1.1 d.2.1.2≠polarPoint d.2.2.1 d.2.2.2) :
    ContDiffAt ℝ ∞ (fun z : ℝ×((ℝ×ℝ)×(ℝ×ℝ)) =>
      physicalSourceFullAngularField z.1 z.2.1.1 z.2.1.2 z.2.2.1 z.2.2.2) d := by
  have hsource : ContDiff ℝ ∞ (fun z : ℝ×((ℝ×ℝ)×(ℝ×ℝ)) => polarPoint z.2.1.1 z.2.1.2) :=
    (polarPoint_contDiff ∞).comp (by fun_prop)
  have htarget : ContDiff ℝ ∞ (fun z : ℝ×((ℝ×ℝ)×(ℝ×ℝ)) => polarPoint z.2.2.1 z.2.2.2) :=
    (polarPoint_contDiff ∞).comp (by fun_prop)
  have hn := (htarget.contDiffAt.sub hsource.contDiffAt).norm ℝ
    (sub_ne_zero.mpr (Ne.symm hsep))
  have hd : ‖polarPoint d.2.2.1 d.2.2.2-polarPoint d.2.1.1 d.2.1.2‖^3≠0 :=
    pow_ne_zero 3 (norm_ne_zero_iff.mpr (sub_ne_zero.mpr (Ne.symm hsep)))
  have hsr : ContDiffAt ℝ ∞ (fun z : ℝ×((ℝ×ℝ)×(ℝ×ℝ)) => (1+z.1)⁻¹) d :=
    (by fun_prop : ContDiffAt ℝ ∞ (fun z : ℝ×((ℝ×ℝ)×(ℝ×ℝ)) => 1+z.1) d).inv heps
  unfold physicalSourceFullAngularField
  exact (by fun_prop : ContDiffAt ℝ ∞ (fun z : ℝ×((ℝ×ℝ)×(ℝ×ℝ)) =>
    z.2.2.1*z.2.1.1*Real.sin (z.2.1.2-z.2.2.2)) d).mul (((hn.pow 3).inv hd).sub hsr)

theorem fullAngularMatrix_eq_physicalSourceFullAngularField (eps : ℝ)
    (r theta : Satellite → ℝ) (i j : Satellite) :
    fullAngularMatrix eps r theta i j=
      physicalSourceFullAngularField eps (r j) (theta j) (r i) (theta i) := rfl

/-- A separated actual angular row passes to its unit-radius limiting row
even when OTHER rows collide. Only this target's true source separations
are required; no full-matrix continuity at a collision is asserted. -/
theorem separated_full_angular_row_limit
    (eps : ℕ → ℝ) (hepst : Tendsto eps atTop (nhds 0))
    (mu r theta : ℕ → Satellite → ℝ)
    (muLimit theta0 : Satellite → ℝ) (hmt : Tendsto mu atTop (nhds muLimit))
    (hrt : ∀ i,Tendsto (fun n => r n i) atTop (nhds 1))
    (hthetat : Tendsto theta atTop (nhds theta0)) (i : Satellite)
    (hroot : ∀ n,angularResidual (eps n) (mu n) (r n) (theta n) i=0)
    (hsep : ∀ j,j≠i → polarPoint 1 (theta0 j)≠polarPoint 1 (theta0 i)) :
    ∑ j,muLimit j*fullAngularMatrix 0 (fun _ => 1) theta0 i j=0 := by
  have htat (j : Satellite) : Tendsto (fun n => theta n j) atTop (nhds (theta0 j)) := by
    simpa only [Function.comp_def] using (continuous_apply j).tendsto theta0 |>.comp hthetat
  have hmass (j : Satellite) : Tendsto (fun n => mu n j) atTop (nhds (muLimit j)) := by
    simpa only [Function.comp_def] using (continuous_apply j).tendsto muLimit |>.comp hmt
  have hterm (j : Satellite) : Tendsto (fun n => mu n j*fullAngularMatrix (eps n) (r n) (theta n) i j)
      atTop (nhds (muLimit j*fullAngularMatrix 0 (fun _ => 1) theta0 i j)) := by
    by_cases hj : j=i
    · subst j
      simpa only [fullAngularMatrix_self,mul_zero] using
        (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (nhds 0))
    · have ht := (physicalSourceFullAngularField_joint_contDiffAt
        (0,((1,theta0 j),(1,theta0 i))) (by norm_num) (hsep j hj)).continuousAt.tendsto.comp
          (hepst.prodMk_nhds (((hrt j).prodMk_nhds (htat j)).prodMk_nhds
            ((hrt i).prodMk_nhds (htat i))))
      simpa only [Function.comp_def,fullAngularMatrix,physicalSourceFullAngularField,
        satelliteDistance,polarSatellites] using
        (hmass j).mul ht
  have hsum := tendsto_finsetSum Finset.univ (fun j _ => hterm j)
  have hzero : Tendsto (fun n => ∑ j,mu n j*fullAngularMatrix (eps n) (r n) (theta n) i j)
      atTop (nhds 0) := by
    simp only [← angularResidual_eq_full_matrix_sum,hroot]
    exact tendsto_const_nhds
  exact tendsto_nhds_unique hsum hzero

def physicalPairExteriorFullAngularField (eps : ℝ) (mu r theta : Satellite → ℝ)
    (a b : Satellite) (rho v : ℝ) : ℝ :=
  ∑ j∈pairExteriorLabels a b,mu j*physicalSourceFullAngularField eps (r j) (theta j) rho v

theorem angularResidual_split_physical_pair (eps : ℝ) (mu r theta : Satellite → ℝ)
    (a b : Satellite) (hab : a≠b) :
    angularResidual eps mu r theta a=mu b*fullAngularMatrix eps r theta a b+
      physicalPairExteriorFullAngularField eps mu r theta a b (r a) (theta a) := by
  rw [angularResidual_eq_full_matrix_sum]
  have hb : b∈Finset.univ.erase a := Finset.mem_erase.mpr ⟨Ne.symm hab,Finset.mem_univ b⟩
  rw [← Finset.sum_erase_add _ _ (Finset.mem_univ a)]
  simp only [fullAngularMatrix_self,mul_zero,add_zero]
  rw [← Finset.sum_erase_add _ _ hb]
  rw [add_comm]
  congr 1

theorem physical_pair_weighted_full_angular_average (eps : ℝ) (mu r theta : Satellite → ℝ)
    (a b : Satellite) (hab : a≠b)
    (hroot : ∀ i,angularResidual eps mu r theta i=0) :
    mu a*physicalPairExteriorFullAngularField eps mu r theta a b (r a) (theta a)+
      mu b*physicalPairExteriorFullAngularField eps mu r theta a b (r b) (theta b)=0 := by
  have ha := hroot a
  have hb := hroot b
  rw [angularResidual_split_physical_pair eps mu r theta a b hab] at ha
  rw [angularResidual_split_physical_pair eps mu r theta b a (Ne.symm hab),
    fullAngularMatrix_reverse eps r theta a b] at hb
  have hcomm : physicalPairExteriorFullAngularField eps mu r theta b a=
      physicalPairExteriorFullAngularField eps mu r theta a b := by
    unfold physicalPairExteriorFullAngularField
    rw [pairExteriorLabels_comm b a]
  rw [hcomm] at hb
  nlinarith [congrArg (fun z : ℝ => mu a*z) ha,congrArg (fun z : ℝ => mu b*z) hb]

theorem physicalPairExteriorFullAngularField_tendsto
    (eps : ℕ → ℝ) (hepst : Tendsto eps atTop (nhds 0))
    (mu r theta : ℕ → Satellite → ℝ)
    (muLimit theta0 : Satellite → ℝ) (hmt : Tendsto mu atTop (nhds muLimit))
    (hrt : ∀ i,Tendsto (fun n => r n i) atTop (nhds 1))
    (hthetat : Tendsto theta atTop (nhds theta0))
    (a b : Satellite) (rho v : ℕ → ℝ) (psi : ℝ)
    (hrhot : Tendsto rho atTop (nhds 1)) (hvt : Tendsto v atTop (nhds psi))
    (hsep : ∀ j∈pairExteriorLabels a b,polarPoint 1 (theta0 j)≠polarPoint 1 psi) :
    Tendsto (fun n => physicalPairExteriorFullAngularField (eps n) (mu n) (r n) (theta n) a b (rho n) (v n))
      atTop (nhds (physicalPairExteriorFullAngularField 0 muLimit (fun _ => 1) theta0 a b 1 psi)) := by
  unfold physicalPairExteriorFullAngularField
  apply tendsto_finsetSum
  intro j hj
  have htat : Tendsto (fun n => theta n j) atTop (nhds (theta0 j)) := by
    simpa only [Function.comp_def] using (continuous_apply j).tendsto theta0 |>.comp hthetat
  have hmass : Tendsto (fun n => mu n j) atTop (nhds (muLimit j)) := by
    simpa only [Function.comp_def] using (continuous_apply j).tendsto muLimit |>.comp hmt
  have ht := (physicalSourceFullAngularField_joint_contDiffAt
    (0,((1,theta0 j),(1,psi))) (by norm_num) (hsep j hj)).continuousAt.tendsto.comp
      (hepst.prodMk_nhds (((hrt j).prodMk_nhds htat).prodMk_nhds (hrhot.prodMk_nhds hvt)))
  simpa only [Function.comp_def] using hmass.mul ht

theorem physicalPairExteriorFullAngularField_unit_kernel
    (mu theta : Satellite → ℝ) (a b : Satellite) (psi : ℝ)
    (hne : ∀ j∈pairExteriorLabels a b,psi≠theta j)
    (hpi : ∀ j∈pairExteriorLabels a b,|theta j-psi|<Real.pi) :
    physicalPairExteriorFullAngularField 0 mu (fun _ => 1) theta a b 1 psi=
      ∑ j∈pairExteriorLabels a b,mu j*coorbitalKernel (theta j-psi) := by
  unfold physicalPairExteriorFullAngularField
  apply Finset.sum_congr rfl
  intro j hj
  unfold physicalSourceFullAngularField
  simp only [one_mul,mul_one,add_zero,inv_one]
  rw [← coorbitalKernel_polar_chord psi (theta j) (hne j hj) (hpi j hj)]

/-- A vanishing current positive weighted average of two functions with
one common limit forces that limit to vanish. No convergence, lower bound
or division is imposed on either current weight. -/
theorem common_limit_of_positive_weighted_zero (A B alpha beta : ℕ → ℝ) (L : ℝ)
    (hA : Tendsto A atTop (nhds L)) (hB : Tendsto B atTop (nhds L))
    (halpha : ∀ n,0<alpha n) (hbeta : ∀ n,0<beta n)
    (hzero : ∀ n,alpha n*A n+beta n*B n=0) : L=0 := by
  rcases lt_trichotomy L 0 with hL|hL|hL
  · have he := (hA.eventually (Iio_mem_nhds hL)).and (hB.eventually (Iio_mem_nhds hL))
    obtain ⟨n,hn⟩ := he.exists
    have ha := mul_neg_of_pos_of_neg (halpha n) hn.1
    have hb := mul_neg_of_pos_of_neg (hbeta n) hn.2
    linarith [hzero n]
  · exact hL
  · have he := (hA.eventually (Ioi_mem_nhds hL)).and (hB.eventually (Ioi_mem_nhds hL))
    obtain ⟨n,hn⟩ := he.exists
    have ha := mul_pos (halpha n) hn.1
    have hb := mul_pos (hbeta n) hn.2
    linarith [hzero n]

/-- Positivity is used only on current masses. A complete pair whose total
mass tends to zero has two zero limiting entries, leaving total exterior
limiting mass one. Either of the two exterior entries may vanish. -/
theorem complete_pair_limiting_masses (mu : ℕ → MassRatio)
    (hm : ∀ n,PositiveRatio (mu n)) (muLimit : MassRatio)
    (hmt : Tendsto mu atTop (nhds muLimit)) (a b : Satellite) (hab : a≠b)
    (hnu : Tendsto (fun n => mu n a+mu n b) atTop (nhds 0)) :
    (∀ i,0≤muLimit i) ∧ muLimit a=0 ∧ muLimit b=0 ∧
      ∑ j∈pairExteriorLabels a b,muLimit j=1 := by
  have hmi (i : Satellite) : Tendsto (fun n => mu n i) atTop (nhds (muLimit i)) := by
    simpa only [Function.comp_def] using (continuous_apply i).tendsto muLimit |>.comp hmt
  have hnonneg (i : Satellite) : 0≤muLimit i :=
    ge_of_tendsto (hmi i) (Eventually.of_forall (fun n => (hm n).1 i |>.le))
  have hab0 : muLimit a+muLimit b=0 := tendsto_nhds_unique ((hmi a).add (hmi b)) hnu
  have ha : muLimit a=0 := by linarith [hnonneg a,hnonneg b]
  have hb : muLimit b=0 := by linarith [hnonneg a,hnonneg b]
  have hsum : ∑ i,muLimit i=1 := by
    have ht := tendsto_finsetSum Finset.univ (fun i _ => hmi i)
    have hone : Tendsto (fun n => ∑ i,mu n i) atTop (nhds 1) := by
      simp only [(hm _).2]
      exact tendsto_const_nhds
    exact tendsto_nhds_unique ht hone
  have hbin : b∈Finset.univ.erase a := Finset.mem_erase.mpr ⟨Ne.symm hab,Finset.mem_univ b⟩
  rw [← Finset.sum_erase_add _ _ (Finset.mem_univ a),ha,add_zero,
    ← Finset.sum_erase_add _ _ hbin,hb,add_zero] at hsum
  exact ⟨hnonneg,ha,hb,hsum⟩

theorem sum_eq_pairExterior_of_pair_zero (f : Satellite → ℝ) (a b : Satellite)
    (hab : a≠b) (ha : f a=0) (hb : f b=0) :
    ∑ i,f i=∑ i∈pairExteriorLabels a b,f i := by
  have hbin : b∈Finset.univ.erase a := Finset.mem_erase.mpr ⟨Ne.symm hab,Finset.mem_univ b⟩
  rw [← Finset.sum_erase_add _ _ (Finset.mem_univ a),ha,add_zero,
    ← Finset.sum_erase_add _ _ hbin,hb,add_zero]
  rfl

/-- Both actual unweighted exterior rows survive the limit. Their sum
forces the source gap to be h even when one exterior limiting mass is
zero. No division by an individual limiting mass occurs. -/
theorem two_source_unit_rows_force_h (mass theta : Satellite → ℝ)
    (a b u w : Satellite) (hab : a≠b) (huw : u≠w)
    (hu : u∈pairExteriorLabels a b) (hw : w∈pairExteriorLabels a b)
    (ha : mass a=0) (hb : mass b=0)
    (hsum : ∑ j∈pairExteriorLabels a b,mass j=1)
    (hgap : 0<theta w-theta u ∧ theta w-theta u<Real.pi)
    (hrowu : ∑ j,mass j*fullAngularMatrix 0 (fun _ => 1) theta u j=0)
    (hroww : ∑ j,mass j*fullAngularMatrix 0 (fun _ => 1) theta w j=0) :
    theta w-theta u=Coorbital.h := by
  have hset := pairExteriorLabels_eq_two a b u w hab hu hw huw
  have hm : mass u+mass w=1 := by simpa [hset,huw] using hsum
  rw [sum_eq_pairExterior_of_pair_zero _ a b hab (by rw [ha,zero_mul])
    (by rw [hb,zero_mul]),hset] at hrowu hroww
  have hU : mass w*fullAngularMatrix 0 (fun _ => 1) theta u w=0 := by
    simpa [huw,fullAngularMatrix_self] using hrowu
  have hW : mass u*(-fullAngularMatrix 0 (fun _ => 1) theta u w)=0 := by
    simpa [huw,fullAngularMatrix_self,fullAngularMatrix_reverse 0 (fun _ => 1) theta u w] using hroww
  have hz : (mass u+mass w)*fullAngularMatrix 0 (fun _ => 1) theta u w=0 := by nlinarith
  rw [hm,one_mul,fullAngularMatrix_unit_positive_gap theta u w ⟨hgap.1.le,hgap.2.le⟩] at hz
  exact (Coorbital.kernelF_eq_zero_iff hgap.1 hgap.2).mp hz

theorem two_source_probe_positive_at_angles (mass theta : Satellite → ℝ)
    (u w k : Satellite) (hmono : Monotone theta) (hspan : theta 3-theta 0<Real.pi)
    (hmu : 0≤mass u) (hmw : 0≤mass w) (hsum : mass u+mass w=1)
    (hgap : theta w-theta u=Coorbital.h)
    (hku : theta k≠theta u) (hkw : theta k≠theta w)
    (hroot : mass u*coorbitalKernel (theta u-theta k)+
      mass w*coorbitalKernel (theta w-theta k)=0) :
    0<mass u*Coorbital.kappa |theta k-theta u|+
      mass w*Coorbital.kappa |theta k-theta w| := by
  let z := theta k-theta u
  have hshift : z-Coorbital.h=theta k-theta w := by dsimp [z]; linarith
  have hzero : z≠0 := sub_ne_zero.mpr hku
  have hzh : z≠Coorbital.h := by
    intro hz
    have hsame : theta k=theta w := by dsimp [z] at hz; linarith
    exact hkw hsame
  have hU := hmono (Fin.zero_le u)
  have hW := hmono (Fin.le_last w)
  have hKlo := hmono (Fin.zero_le k)
  have hKhi := hmono (Fin.le_last k)
  change theta w≤theta 3 at hW
  change theta k≤theta 3 at hKhi
  have hmax : max Coorbital.h z≤theta 3-theta u := by
    apply max_le
    · linarith
    · dsimp [z]; linarith
  have hmin : theta 0-theta u≤min 0 z := by
    apply le_min
    · linarith
    · dsimp [z]; linarith
  have hzs : twoSourceSpan z<Real.pi := by unfold twoSourceSpan; linarith
  have hzroot : mass u*coorbitalKernel z+mass w*coorbitalKernel (z-Coorbital.h)=0 := by
    rw [show theta u-theta k= -z by dsimp [z]; ring,
      show theta w-theta k= -(z-Coorbital.h) by rw [hshift]; ring,
      coorbitalKernel_neg,coorbitalKernel_neg] at hroot
    linarith
  simpa only [hshift] using twoSourceProbe hmu hmw hsum hzero hzh hzs hzroot

theorem complete_pair_exterior_separated (q : SatelliteConfiguration)
    (a b u w : Satellite) (hab : a≠b) (huw : u≠w)
    (hu : u∈pairExteriorLabels a b) (hw : w∈pairExteriorLabels a b)
    (c : Plane) (hpair : CompleteLimitingSatellitePair q a b c) (hdist : q u≠q w) :
    ∀ i∈pairExteriorLabels a b,∀ j,j≠i → q j≠q i := by
  have hset := pairExteriorLabels_eq_two a b u w hab hu hw huw
  intro i hi j hji he
  have hiNot : q i≠c := by
    intro hc
    rcases (hpair i).mp hc with hia|hib
    · exact (Finset.mem_erase.mp (Finset.mem_erase.mp hi).2).1 hia
    · exact (Finset.mem_erase.mp hi).1 hib
  by_cases hj : j=a ∨ j=b
  · exact hiNot (he.symm.trans ((hpair j).mpr hj))
  have hjmem : j∈pairExteriorLabels a b := by
    simp only [pairExteriorLabels,Finset.mem_erase,Finset.mem_univ,and_true]
    exact ⟨fun h => hj (Or.inr h),fun h => hj (Or.inl h)⟩
  rw [hset] at hi hjmem
  simp only [Finset.mem_insert,Finset.mem_singleton] at hi hjmem
  rcases hi with rfl|rfl <;> rcases hjmem with rfl|rfl
  · exact hji rfl
  · exact hdist he.symm
  · exact hdist he
  · exact hji rfl

/-- The actual complete-pair limit has two zero pair masses, two separated
exterior sources at gap h, and the genuine two-source probe equation with
strictly positive derivative. The exterior limiting weights include both
zero-mass endpoints. The positive derivative is proved, not assumed. -/
theorem normalized_complete_pair_limiting_sources_and_probe
    (eps : ℕ → ℝ) (mu : ℕ → MassRatio) (x : ℕ → Configuration)
    (heps : ∀ n,0<eps n) (hepst : Tendsto eps atTop (nhds 0))
    (hm : ∀ n,PositiveRatio (mu n))
    (hx : ∀ n,NormalizedCentralConfiguration (masses (eps n) (mu n)) (x n))
    (hconv : ∀ n,StrictConvexInOrder ⟨Equiv.refl Label,rfl⟩ (x n))
    (r theta : ℕ → Satellite → ℝ) (hr : ∀ n,∀ i,0<r n i)
    (hpolar : ∀ n,satellitesRelative (x n)=polarSatellites (r n) (theta n))
    (horder : ∀ n,∀ i j,i<j → 0<theta n j-theta n i ∧ theta n j-theta n i<Real.pi)
    (muLimit : MassRatio) (hmt : Tendsto mu atTop (nhds muLimit))
    (qLimit : SatelliteConfiguration)
    (hqt : Tendsto (fun n => satellitesRelative (x n)) atTop (nhds qLimit))
    (a b : Satellite) (hab : a<b) (c : Plane)
    (hpair : CompleteLimitingSatellitePair qLimit a b c)
    (theta0 : Satellite → ℝ) (hthetat : Tendsto theta atTop (nhds theta0))
    (u w : Satellite) (huw : u<w)
    (hu : u∈pairExteriorLabels a b) (hw : w∈pairExteriorLabels a b) :
    (∀ i,0≤muLimit i) ∧ muLimit a=0 ∧ muLimit b=0 ∧ muLimit u+muLimit w=1 ∧
    theta0 w-theta0 u=Coorbital.h ∧
    muLimit u*coorbitalKernel (theta0 u-theta0 a)+
      muLimit w*coorbitalKernel (theta0 w-theta0 a)=0 ∧
    0<muLimit u*Coorbital.kappa |theta0 a-theta0 u|+
      muLimit w*Coorbital.kappa |theta0 a-theta0 w| := by
  have hnu := (normalized_complete_pair_tangential_mass_scale eps mu x heps hepst hm hx hconv
    r theta hr hpolar horder muLimit hmt qLimit hqt a b hab c hpair theta0 hthetat).2.2.2.2.1
  obtain ⟨hnonneg,hma,hmb,hmsum⟩ := complete_pair_limiting_masses mu hm muLimit hmt a b (ne_of_lt hab) hnu
  have hset := pairExteriorLabels_eq_two a b u w (ne_of_lt hab) hu hw (ne_of_lt huw)
  have hmusum : muLimit u+muLimit w=1 := by simpa [hset,ne_of_lt huw] using hmsum
  have hrat (i : Satellite) : Tendsto (fun n => r n i) atTop (nhds 1) := by
    convert! dominant_satellite_radius_tendsto eps mu x heps hepst hm hx i using 1
    funext n
    rw [hpolar n]
    simp only [polarSatellites,polarPoint_norm,abs_of_pos (hr n i)]
  have htat (i : Satellite) : Tendsto (fun n => theta n i) atTop (nhds (theta0 i)) := by
    simpa only [Function.comp_def] using (continuous_apply i).tendsto theta0 |>.comp hthetat
  have hangroot : ∀ n i,angularResidual (eps n) (mu n) (r n) (theta n) i=0 :=
    fun n => (polarResiduals_zero_of_normalized (eps n) (mu n) (x n) (hx n)
      (hm n) (heps n) (r n) (theta n) (hr n) (hpolar n)).2
  have hspan : theta0 3-theta0 0<Real.pi :=
    ordered_full_angular_limit_span_lt_pi eps heps hepst mu r theta (fun n => (hm n).1)
      (fun n => (hm n).2) hr hangroot horder muLimit (fun _ => 1) theta0
        (fun _ => rfl) hmt (tendsto_pi_nhds.mpr hrat) hthetat
  have hunit (i : Satellite) : qLimit i=polarPoint 1 (theta0 i) := by
    have hqi : Tendsto (fun n => satellitesRelative (x n) i) atTop (nhds (qLimit i)) := by
      simpa only [Function.comp_def] using (continuous_apply i).tendsto qLimit |>.comp hqt
    have hp := (polarPoint_contDiff ∞).continuous.continuousAt.tendsto.comp
      ((hrat i).prodMk_nhds (htat i))
    apply tendsto_nhds_unique hqi
    simpa only [hpolar,polarSatellites,Function.comp_def] using hp
  have hmono : Monotone theta0 := by
    intro i j hij
    rcases hij.eq_or_lt with rfl|hlt
    · rfl
    · exact sub_nonneg.mp (ge_of_tendsto ((htat j).sub (htat i))
        (Eventually.of_forall (fun n => (horder n i j hlt).1.le)))
  have hbound (i j : Satellite) : |theta0 j-theta0 i|<Real.pi := by
    have hiLo := hmono (Fin.zero_le i)
    have hjLo := hmono (Fin.zero_le j)
    have hiHi := hmono (Fin.le_last i)
    have hjHi := hmono (Fin.le_last j)
    change theta0 i≤theta0 3 at hiHi
    change theta0 j≤theta0 3 at hjHi
    exact abs_lt.mpr ⟨by linarith,by linarith⟩
  have hdist := normalized_complete_pair_exterior_limits_distinct eps mu x heps hepst hm hx hconv
    r theta hr hpolar horder muLimit hmt qLimit hqt a b hab c hpair theta0 hthetat u w huw hu hw
  have hextSep := complete_pair_exterior_separated qLimit a b u w (ne_of_lt hab) (ne_of_lt huw)
    hu hw c hpair hdist
  have hangle : theta0 u≠theta0 w := by
    intro he
    exact hdist (by rw [hunit u,hunit w,he])
  have hgap : 0<theta0 w-theta0 u ∧ theta0 w-theta0 u<Real.pi :=
    ⟨sub_pos.mpr (lt_of_le_of_ne (hmono huw.le) hangle),
      lt_of_le_of_lt (le_abs_self _) (hbound u w)⟩
  have hrow (i : Satellite) (hi : i∈pairExteriorLabels a b) :
      ∑ j,muLimit j*fullAngularMatrix 0 (fun _ => 1) theta0 i j=0 := by
    apply separated_full_angular_row_limit eps hepst mu r theta muLimit theta0 hmt hrat hthetat i
      (fun n => hangroot n i)
    intro j hji
    rw [← hunit j,← hunit i]
    exact hextSep i hi j hji
  have hh := two_source_unit_rows_force_h muLimit theta0 a b u w (ne_of_lt hab) (ne_of_lt huw)
    hu hw hma hmb hmsum hgap (hrow u hu) (hrow w hw)
  have hpb := (complete_pair_ordered_angles_adjacent theta0 hmono hspan qLimit hunit a b hab c hpair).2
  have hsep (j : Satellite) (hj : j∈pairExteriorLabels a b) :
      polarPoint 1 (theta0 j)≠polarPoint 1 (theta0 a) := by
    rw [← hunit j,← hunit a]
    intro he
    have hc : qLimit j=c := he.trans ((hpair a).mpr (Or.inl rfl))
    rcases (hpair j).mp hc with hja|hjb
    · exact (Finset.mem_erase.mp (Finset.mem_erase.mp hj).2).1 hja
    · exact (Finset.mem_erase.mp hj).1 hjb
  have hfa := physicalPairExteriorFullAngularField_tendsto eps hepst mu r theta muLimit theta0
    hmt hrat hthetat a b (fun n => r n a) (fun n => theta n a) (theta0 a) (hrat a) (htat a) hsep
  have hfb := physicalPairExteriorFullAngularField_tendsto eps hepst mu r theta muLimit theta0
    hmt hrat hthetat a b (fun n => r n b) (fun n => theta n b) (theta0 a) (hrat b)
      (by simpa only [hpb] using htat b) hsep
  have hmean := common_limit_of_positive_weighted_zero _ _ (fun n => mu n a) (fun n => mu n b) _
    hfa hfb (fun n => (hm n).1 a) (fun n => (hm n).1 b)
      (fun n => physical_pair_weighted_full_angular_average (eps n) (mu n) (r n) (theta n)
        a b (ne_of_lt hab) (hangroot n))
  have hangleSep (j : Satellite) (hj : j∈pairExteriorLabels a b) : theta0 a≠theta0 j := by
    intro he
    exact hsep j hj (by rw [he])
  rw [physicalPairExteriorFullAngularField_unit_kernel muLimit theta0 a b (theta0 a)
    hangleSep (fun j _ => hbound a j),hset] at hmean
  have hprobe : muLimit u*coorbitalKernel (theta0 u-theta0 a)+
      muLimit w*coorbitalKernel (theta0 w-theta0 a)=0 := by
    simpa [ne_of_lt huw] using hmean
  exact ⟨hnonneg,hma,hmb,hmusum,hh,hprobe,
    two_source_probe_positive_at_angles muLimit theta0 u w a hmono hspan (hnonneg u) (hnonneg w)
      hmusum hh (hangleSep u hu) (hangleSep w hw) hprobe⟩

/-- A strict derivative controls two moving endpoints with an arbitrary
positive current scale. Both endpoints, including their common source
parameters, may move. The scaled vector difference supplies the only
first-order direction; no source convergence rate is imposed. -/
theorem strict_fderiv_scaled_difference_limit
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (F : E → ℝ) (L : E →L[ℝ] ℝ) (z : E) (hF : HasStrictFDerivAt F L z)
    (A B : ℕ → E) (hA : Tendsto A atTop (nhds z)) (hB : Tendsto B atTop (nhds z))
    (d : ℕ → ℝ) (hd : ∀ n,0<d n) (v : E)
    (hv : Tendsto (fun n => (d n)⁻¹ • (B n-A n)) atTop (nhds v)) :
    Tendsto (fun n => (F (B n)-F (A n))/d n) atTop (nhds (L v)) := by
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
  have hrem : Tendsto (fun n => (F (B n)-F (A n)-L (B n-A n))/d n) atTop (nhds 0) := by
    have ho := hF.isLittleO.comp_tendsto (hB.prodMk_nhds hA)
    simpa only [Function.comp_def] using (ho.trans_isBigO hbound).tendsto_div_nhds_zero
  have hlin : Tendsto (fun n => L (B n-A n)/d n) atTop (nhds (L v)) := by
    simpa only [Function.comp_def,map_smul,smul_eq_mul,div_eq_mul_inv,mul_comm] using
      L.continuous.continuousAt.tendsto.comp hv
  convert hrem.add hlin using 1
  · funext n
    ring
  · rw [zero_add]

theorem physicalSourceAngularField_unit_kernel (angle v : ℝ)
    (hne : angle≠v) (hpi : |angle-v|<Real.pi) :
    physicalSourceAngularField 1 angle 1 v=coorbitalKernel (angle-v) := by
  unfold physicalSourceAngularField
  simp only [one_mul,one_pow,inv_one]
  rw [← coorbitalKernel_polar_chord v angle hne.symm hpi]

theorem physicalSourceAngularField_unit_hasDerivAt (angle psi : ℝ)
    (hne : angle≠psi) (hpi : |angle-psi|<Real.pi) :
    HasDerivAt (fun v => physicalSourceAngularField 1 angle 1 v)
      (Coorbital.kappa |psi-angle|) psi := by
  have hd := (coorbitalKernel_hasDerivAt (sub_ne_zero.mpr hne) hpi).comp psi
    ((hasDerivAt_const psi angle).sub (hasDerivAt_id psi))
  have hd' : HasDerivAt (fun v => coorbitalKernel (angle-v)) (Coorbital.kappa |psi-angle|) psi := by
    simpa only [Function.comp_def,abs_sub_comm,zero_sub,neg_mul,mul_neg_one,neg_neg,mul_one] using hd
  have heq : (fun v => physicalSourceAngularField 1 angle 1 v)=ᶠ[nhds psi]
      (fun v => coorbitalKernel (angle-v)) := by
    have hs := (show Continuous (fun v : ℝ => |angle-v|) by fun_prop).continuousAt.eventually
      (Iio_mem_nhds hpi)
    filter_upwards [eventually_ne_nhds hne.symm,hs] with v hv hvs
    exact physicalSourceAngularField_unit_kernel angle v hv.symm hvs
  exact hd'.congr_of_eventuallyEq heq

theorem physicalSourceAngularField_moving_secant_limit
    (s angle ra va rb vb d : ℕ → ℝ) (angle0 psi : ℝ)
    (hst : Tendsto s atTop (nhds 1)) (hangt : Tendsto angle atTop (nhds angle0))
    (hrat : Tendsto ra atTop (nhds 1)) (hrbt : Tendsto rb atTop (nhds 1))
    (hvat : Tendsto va atTop (nhds psi)) (hvbt : Tendsto vb atTop (nhds psi))
    (hd : ∀ n,0<d n)
    (hrd : Tendsto (fun n => (rb n-ra n)/d n) atTop (nhds 0))
    (hvd : Tendsto (fun n => (vb n-va n)/d n) atTop (nhds 1))
    (hne : angle0≠psi) (hpi : |angle0-psi|<Real.pi) :
    Tendsto (fun n => (physicalSourceAngularField (s n) (angle n) (rb n) (vb n)-
      physicalSourceAngularField (s n) (angle n) (ra n) (va n))/d n)
      atTop (nhds (Coorbital.kappa |psi-angle0|)) := by
  let F : (ℝ×ℝ)×(ℝ×ℝ) → ℝ := fun z => physicalSourceAngularField z.1.1 z.1.2 z.2.1 z.2.2
  let z0 : (ℝ×ℝ)×(ℝ×ℝ) := ((1,angle0),(1,psi))
  have hc : ContDiffAt ℝ ∞ F z0 := physicalSourceAngularField_joint_contDiffAt z0 (by norm_num [z0])
    (polarUnit_ne_of_angle_ne angle0 psi hne (by simpa only [abs_sub_comm] using hpi))
  have hA : Tendsto (fun n => ((s n,angle n),(ra n,va n))) atTop (nhds z0) :=
    (hst.prodMk_nhds hangt).prodMk_nhds (hrat.prodMk_nhds hvat)
  have hB : Tendsto (fun n => ((s n,angle n),(rb n,vb n))) atTop (nhds z0) :=
    (hst.prodMk_nhds hangt).prodMk_nhds (hrbt.prodMk_nhds hvbt)
  have hv : Tendsto (fun n => (d n)⁻¹ •
      (((s n,angle n),(rb n,vb n))-((s n,angle n),(ra n,va n))))
      atTop (nhds (((0,0),(0,1)) : (ℝ×ℝ)×(ℝ×ℝ))) := by
    have ht := (tendsto_const_nhds : Tendsto (fun _ : ℕ => ((0,0) : ℝ×ℝ)) atTop (nhds (0,0))).prodMk_nhds
      (hrd.prodMk_nhds hvd)
    simpa only [Prod.smul_mk,Prod.mk_sub_mk,Prod.zero_eq_mk,smul_zero,smul_eq_mul,sub_self,mul_zero,
      div_eq_mul_inv,mul_comm] using ht
  have hp : HasDerivAt (fun v : ℝ => (((1 : ℝ),angle0),((1 : ℝ),v)))
      (((0,0),(0,1)) : (ℝ×ℝ)×(ℝ×ℝ)) psi := by
    have h0 : HasDerivAt (fun _ : ℝ => ((1 : ℝ),angle0)) ((0,0) : ℝ×ℝ) psi :=
      hasDerivAt_const psi ((1 : ℝ),angle0)
    have h1 : HasDerivAt (fun v : ℝ => ((1 : ℝ),v)) ((0,1) : ℝ×ℝ) psi :=
      (hasDerivAt_const psi (1 : ℝ)).prodMk (hasDerivAt_id psi)
    exact h0.prodMk h1
  have hpartial : (fderiv ℝ F z0) ((0,0),(0,1))=Coorbital.kappa |psi-angle0| := by
    have hp' := (hc.differentiableAt (by simp)).hasFDerivAt.comp_hasDerivAt psi hp
    exact hp'.unique (physicalSourceAngularField_unit_hasDerivAt angle0 psi hne hpi)
  have ht := strict_fderiv_scaled_difference_limit F (fderiv ℝ F z0) z0
    (hc.hasStrictFDerivAt (by simp)) _ _ hA hB d hd ((0,0),(0,1)) hv
  simpa only [F,hpartial] using ht

/-- The actual exterior angular difference divided by the actual physical
pair distance converges to the true probe derivative. The sources, radii,
angles and current masses remain joint variables throughout the limit. -/
theorem complete_pair_exterior_difference_quotient_limit
    (mu r theta : ℕ → Satellite → ℝ) (muLimit theta0 : Satellite → ℝ)
    (hmt : Tendsto mu atTop (nhds muLimit))
    (hrt : ∀ i,Tendsto (fun n => r n i) atTop (nhds 1))
    (hthetat : Tendsto theta atTop (nhds theta0)) (a b : Satellite) (psi : ℝ)
    (hpa : theta0 a=psi) (hpb : theta0 b=psi) (d : ℕ → ℝ) (hd : ∀ n,0<d n)
    (hrd : Tendsto (fun n => (r n b-r n a)/d n) atTop (nhds 0))
    (hvd : Tendsto (fun n => (theta n b-theta n a)/d n) atTop (nhds 1))
    (hne : ∀ j∈pairExteriorLabels a b,theta0 j≠psi)
    (hpi : ∀ j∈pairExteriorLabels a b,|theta0 j-psi|<Real.pi) :
    Tendsto (fun n => (physicalPairExteriorAngularField (mu n) (r n) (theta n) a b (r n b) (theta n b)-
      physicalPairExteriorAngularField (mu n) (r n) (theta n) a b (r n a) (theta n a))/d n)
      atTop (nhds (∑ j∈pairExteriorLabels a b,muLimit j*Coorbital.kappa |psi-theta0 j|)) := by
  have htat (i : Satellite) : Tendsto (fun n => theta n i) atTop (nhds (theta0 i)) := by
    simpa only [Function.comp_def] using (continuous_apply i).tendsto theta0 |>.comp hthetat
  have hmi (i : Satellite) : Tendsto (fun n => mu n i) atTop (nhds (muLimit i)) := by
    simpa only [Function.comp_def] using (continuous_apply i).tendsto muLimit |>.comp hmt
  have hterm (j : Satellite) (hj : j∈pairExteriorLabels a b) :
      Tendsto (fun n => mu n j*((physicalSourceAngularField (r n j) (theta n j) (r n b) (theta n b)-
        physicalSourceAngularField (r n j) (theta n j) (r n a) (theta n a))/d n))
        atTop (nhds (muLimit j*Coorbital.kappa |psi-theta0 j|)) := by
    exact (hmi j).mul (physicalSourceAngularField_moving_secant_limit _ _ _ _ _ _ d (theta0 j) psi
      (hrt j) (htat j) (hrt a) (hrt b) (by simpa only [hpa] using htat a)
      (by simpa only [hpb] using htat b) hd hrd hvd (hne j hj) (hpi j hj))
  have ht := tendsto_finsetSum (pairExteriorLabels a b) hterm
  convert ht using 1
  funext n
  rw [physicalPairExteriorAngularField_eq_source_sum,physicalPairExteriorAngularField_eq_source_sum,
    ← Finset.sum_sub_distrib,Finset.sum_div]
  apply Finset.sum_congr rfl
  intro j _
  ring

theorem current_positive_weighted_average_tendsto
    (alpha beta A B : ℕ → ℝ) (L : ℝ)
    (halpha : ∀ n,0<alpha n) (hbeta : ∀ n,0<beta n)
    (hA : Tendsto A atTop (nhds L)) (hB : Tendsto B atTop (nhds L)) :
    Tendsto (fun n => (alpha n*A n+beta n*B n)/(alpha n+beta n)) atTop (nhds L) := by
  apply tendsto_order.mpr
  constructor
  · intro c hc
    filter_upwards [hA.eventually (Ioi_mem_nhds hc),hB.eventually (Ioi_mem_nhds hc)] with n hnA hnB
    apply (lt_div_iff₀ (add_pos (halpha n) (hbeta n))).mpr
    nlinarith [mul_lt_mul_of_pos_left hnA (halpha n),mul_lt_mul_of_pos_left hnB (hbeta n)]
  · intro c hc
    filter_upwards [hA.eventually (Iio_mem_nhds hc),hB.eventually (Iio_mem_nhds hc)] with n hnA hnB
    apply (div_lt_iff₀ (add_pos (halpha n) (hbeta n))).mpr
    nlinarith [mul_lt_mul_of_pos_left hnA (halpha n),mul_lt_mul_of_pos_left hnB (hbeta n)]

/-- Exact Q differences determine the mass-to-distance cube limit. The
current positive mass weighted radius tends to one independently of any
individual mass fraction; all singular divisions are justified pointwise. -/
theorem pair_mass_cube_tendsto_of_angular_difference
    (mu r theta : ℕ → Satellite → ℝ) (a b : Satellite) (d : ℕ → ℝ)
    (hm : ∀ n i,0<mu n i) (hr : ∀ n i,0<r n i) (hd : ∀ n,0<d n)
    (horder : ∀ n,0<theta n b-theta n a ∧ theta n b-theta n a<Real.pi)
    (hmat : Tendsto (fun n => mu n a) atTop (nhds 0))
    (hmbt : Tendsto (fun n => mu n b) atTop (nhds 0))
    (hrat : Tendsto (fun n => r n a) atTop (nhds 1))
    (hrbt : Tendsto (fun n => r n b) atTop (nhds 1))
    (hgap : Tendsto (fun n => theta n b-theta n a) atTop (nhds 0))
    (hgd : Tendsto (fun n => (theta n b-theta n a)/d n) atTop (nhds 1))
    (Hdiff : ℕ → ℝ) (D : ℝ) (hHt : Tendsto (fun n => Hdiff n/d n) atTop (nhds D))
    (hQdiff : ∀ n,Hdiff n=Real.sin (theta n b-theta n a)*
      ((mu n a*r n a+mu n b*r n b)/d n^3-mu n a/(r n a)^2-mu n b/(r n b)^2)) :
    Tendsto (fun n => (mu n a+mu n b)/d n^3) atTop (nhds D) := by
  have hsinc : Tendsto (fun n => Real.sinc (theta n b-theta n a)) atTop (nhds 1) := by
    simpa only [Function.comp_def,Real.sinc_zero] using Real.continuous_sinc.continuousAt.tendsto.comp hgap
  have hsine : Tendsto (fun n => Real.sin (theta n b-theta n a)/d n) atTop (nhds 1) := by
    convert hsinc.mul hgd using 1
    · funext n
      rw [← sinc_mul_argument (theta n b-theta n a)]
      ring
    · norm_num
  have hR := current_positive_weighted_average_tendsto (fun n => mu n a) (fun n => mu n b)
    (fun n => r n a) (fun n => r n b) 1 (fun n => hm n a) (fun n => hm n b) hrat hrbt
  have hB : Tendsto (fun n => mu n a/(r n a)^2+mu n b/(r n b)^2) atTop (nhds 0) := by
    simpa only [Pi.div_apply,Pi.pow_apply,Pi.add_apply,one_pow,zero_div,add_zero] using
      (hmat.div (hrat.pow 2) (by norm_num : (1 : ℝ)^2≠0)).add
        (hmbt.div (hrbt.pow 2) (by norm_num : (1 : ℝ)^2≠0))
  have hres := ((hHt.div hsine (by norm_num : (1 : ℝ)≠0)).add hB).div hR (by norm_num : (1 : ℝ)≠0)
  have hres' : Tendsto (fun n => (Hdiff n/d n/(Real.sin (theta n b-theta n a)/d n)+
      (mu n a/(r n a)^2+mu n b/(r n b)^2))/
      ((mu n a*r n a+mu n b*r n b)/(mu n a+mu n b))) atTop (nhds D) := by
    convert! hres using 1
    simp
  apply hres'.congr'
  exact Eventually.of_forall (fun n => by
    have hsin := Real.sin_pos_of_pos_of_lt_pi (horder n).1 (horder n).2
    have hnu : 0<mu n a+mu n b := add_pos (hm n a) (hm n b)
    have hnum : 0<mu n a*r n a+mu n b*r n b := add_pos (mul_pos (hm n a) (hr n a)) (mul_pos (hm n b) (hr n b))
    dsimp only
    rw [hQdiff n]
    field_simp [ne_of_gt hsin,ne_of_gt hnu,ne_of_gt hnum,ne_of_gt (hd n),
      ne_of_gt (hr n a),ne_of_gt (hr n b)]
    ring)

/-- The final positive cube-scale limit in source Proposition 4.2 is
derived from actual collision-free normalized equations. The limiting
coefficient is the genuine two-source probe derivative, including both
zero-mass endpoints; it is not supplied as an analytic hypothesis. -/
theorem normalized_complete_pair_mass_cube_limit
    (eps : ℕ → ℝ) (mu : ℕ → MassRatio) (x : ℕ → Configuration)
    (heps : ∀ n,0<eps n) (hepst : Tendsto eps atTop (nhds 0))
    (hm : ∀ n,PositiveRatio (mu n))
    (hx : ∀ n,NormalizedCentralConfiguration (masses (eps n) (mu n)) (x n))
    (hconv : ∀ n,StrictConvexInOrder ⟨Equiv.refl Label,rfl⟩ (x n))
    (r theta : ℕ → Satellite → ℝ) (hr : ∀ n,∀ i,0<r n i)
    (hpolar : ∀ n,satellitesRelative (x n)=polarSatellites (r n) (theta n))
    (horder : ∀ n,∀ i j,i<j → 0<theta n j-theta n i ∧ theta n j-theta n i<Real.pi)
    (muLimit : MassRatio) (hmt : Tendsto mu atTop (nhds muLimit))
    (qLimit : SatelliteConfiguration)
    (hqt : Tendsto (fun n => satellitesRelative (x n)) atTop (nhds qLimit))
    (a b : Satellite) (hab : a<b) (c : Plane)
    (hpair : CompleteLimitingSatellitePair qLimit a b c)
    (theta0 : Satellite → ℝ) (hthetat : Tendsto theta atTop (nhds theta0))
    (u w : Satellite) (huw : u<w)
    (hu : u∈pairExteriorLabels a b) (hw : w∈pairExteriorLabels a b) :
    0<muLimit u*Coorbital.kappa |theta0 a-theta0 u|+
      muLimit w*Coorbital.kappa |theta0 a-theta0 w| ∧
    Tendsto (fun n => (mu n a+mu n b)/satelliteDistance (satellitesRelative (x n)) a b^3)
      atTop (nhds (muLimit u*Coorbital.kappa |theta0 a-theta0 u|+
        muLimit w*Coorbital.kappa |theta0 a-theta0 w|)) := by
  obtain ⟨_,hma,hmb,_,_,_,hD⟩ := normalized_complete_pair_limiting_sources_and_probe eps mu x
    heps hepst hm hx hconv r theta hr hpolar horder muLimit hmt qLimit hqt a b hab c hpair theta0 hthetat u w huw hu hw
  refine ⟨hD,?_⟩
  obtain ⟨_,hgd,hrd,_,_,_⟩ := normalized_complete_pair_tangential_mass_scale eps mu x heps hepst hm hx hconv
    r theta hr hpolar horder muLimit hmt qLimit hqt a b hab c hpair theta0 hthetat
  have hrat (i : Satellite) : Tendsto (fun n => r n i) atTop (nhds 1) := by
    convert! dominant_satellite_radius_tendsto eps mu x heps hepst hm hx i using 1
    funext n
    rw [hpolar n]
    simp only [polarSatellites,polarPoint_norm,abs_of_pos (hr n i)]
  have htat (i : Satellite) : Tendsto (fun n => theta n i) atTop (nhds (theta0 i)) := by
    simpa only [Function.comp_def] using (continuous_apply i).tendsto theta0 |>.comp hthetat
  have hangroot : ∀ n i,angularResidual (eps n) (mu n) (r n) (theta n) i=0 :=
    fun n => (polarResiduals_zero_of_normalized (eps n) (mu n) (x n) (hx n)
      (hm n) (heps n) (r n) (theta n) (hr n) (hpolar n)).2
  have hspan : theta0 3-theta0 0<Real.pi :=
    ordered_full_angular_limit_span_lt_pi eps heps hepst mu r theta (fun n => (hm n).1)
      (fun n => (hm n).2) hr hangroot horder muLimit (fun _ => 1) theta0
        (fun _ => rfl) hmt (tendsto_pi_nhds.mpr hrat) hthetat
  have hunit (i : Satellite) : qLimit i=polarPoint 1 (theta0 i) := by
    have hqi : Tendsto (fun n => satellitesRelative (x n) i) atTop (nhds (qLimit i)) := by
      simpa only [Function.comp_def] using (continuous_apply i).tendsto qLimit |>.comp hqt
    have hp := (polarPoint_contDiff ∞).continuous.continuousAt.tendsto.comp
      ((hrat i).prodMk_nhds (htat i))
    apply tendsto_nhds_unique hqi
    simpa only [hpolar,polarSatellites,Function.comp_def] using hp
  have hmono : Monotone theta0 := by
    intro i j hij
    rcases hij.eq_or_lt with rfl|hlt
    · rfl
    · exact sub_nonneg.mp (ge_of_tendsto ((htat j).sub (htat i))
        (Eventually.of_forall (fun n => (horder n i j hlt).1.le)))
  have hbound (i j : Satellite) : |theta0 j-theta0 i|<Real.pi := by
    have hiLo := hmono (Fin.zero_le i)
    have hjLo := hmono (Fin.zero_le j)
    have hiHi := hmono (Fin.le_last i)
    have hjHi := hmono (Fin.le_last j)
    change theta0 i≤theta0 3 at hiHi
    change theta0 j≤theta0 3 at hjHi
    exact abs_lt.mpr ⟨by linarith,by linarith⟩
  have hpb := (complete_pair_ordered_angles_adjacent theta0 hmono hspan qLimit hunit a b hab c hpair).2
  have hne (j : Satellite) (hj : j∈pairExteriorLabels a b) : theta0 j≠theta0 a := by
    intro he
    have hc : qLimit j=c := by
      rw [hunit j,he,← hunit a]
      exact (hpair a).mpr (Or.inl rfl)
    rcases (hpair j).mp hc with hja|hjb
    · exact (Finset.mem_erase.mp (Finset.mem_erase.mp hj).2).1 hja
    · exact (Finset.mem_erase.mp hj).1 hjb
  let d := fun n => satelliteDistance (satellitesRelative (x n)) a b
  have hd (n : ℕ) : 0<d n := norm_pos_iff.mpr (sub_ne_zero.mpr
    ((satellitesRelative_collisionFree (x n) (hx n).1).2 a b (ne_of_lt hab)))
  have hH := complete_pair_exterior_difference_quotient_limit mu r theta muLimit theta0 hmt hrat hthetat
    a b (theta0 a) rfl hpb d hd hrd hgd hne (fun j _ => hbound a j)
  have hset := pairExteriorLabels_eq_two a b u w (ne_of_lt hab) hu hw (ne_of_lt huw)
  have hH' : Tendsto (fun n => (physicalPairExteriorAngularField (mu n) (r n) (theta n) a b (r n b) (theta n b)-
      physicalPairExteriorAngularField (mu n) (r n) (theta n) a b (r n a) (theta n a))/d n)
      atTop (nhds (muLimit u*Coorbital.kappa |theta0 a-theta0 u|+
        muLimit w*Coorbital.kappa |theta0 a-theta0 w|)) := by
    simpa [hset,ne_of_lt huw] using hH
  have hmat : Tendsto (fun n => mu n a) atTop (nhds 0) := by
    simpa only [hma,Function.comp_def] using (continuous_apply a).tendsto muLimit |>.comp hmt
  have hmbt : Tendsto (fun n => mu n b) atTop (nhds 0) := by
    simpa only [hmb,Function.comp_def] using (continuous_apply b).tendsto muLimit |>.comp hmt
  have hgap : Tendsto (fun n => theta n b-theta n a) atTop (nhds 0) := by
    simpa only [hpb,sub_self] using (htat b).sub (htat a)
  apply pair_mass_cube_tendsto_of_angular_difference mu r theta a b d (fun n => (hm n).1) hr hd
    (fun n => horder n a b hab) hmat hmbt (hrat a) (hrat b) hgap hgd _ _ hH'
  intro n
  simpa only [← hpolar n,d] using normalized_pair_tangential_difference (eps n) (mu n) (x n) (hx n)
    (ne_of_gt (heps n)) (r n) (theta n) (hr n) (hpolar n) a b (ne_of_lt hab)

/-- Complete source Proposition 4.2 on the selected fixed-label sequence.
The gauge places the two exterior limits at zero and h by subtracting the
first exterior angle only. The original orientation is preserved, and
current pair fractions are never required to converge. -/
theorem normalized_complete_pair_scale_complete
    (eps : ℕ → ℝ) (mu : ℕ → MassRatio) (x : ℕ → Configuration)
    (heps : ∀ n,0<eps n) (hepst : Tendsto eps atTop (nhds 0))
    (hm : ∀ n,PositiveRatio (mu n))
    (hx : ∀ n,NormalizedCentralConfiguration (masses (eps n) (mu n)) (x n))
    (hconv : ∀ n,StrictConvexInOrder ⟨Equiv.refl Label,rfl⟩ (x n))
    (r theta : ℕ → Satellite → ℝ) (hr : ∀ n,∀ i,0<r n i)
    (hpolar : ∀ n,satellitesRelative (x n)=polarSatellites (r n) (theta n))
    (horder : ∀ n,∀ i j,i<j → 0<theta n j-theta n i ∧ theta n j-theta n i<Real.pi)
    (muLimit : MassRatio) (hmt : Tendsto mu atTop (nhds muLimit))
    (qLimit : SatelliteConfiguration)
    (hqt : Tendsto (fun n => satellitesRelative (x n)) atTop (nhds qLimit))
    (a b : Satellite) (hab : a<b) (c : Plane)
    (hpair : CompleteLimitingSatellitePair qLimit a b c)
    (theta0 : Satellite → ℝ) (hthetat : Tendsto theta atTop (nhds theta0))
    (u w : Satellite) (huw : u<w)
    (hu : u∈pairExteriorLabels a b) (hw : w∈pairExteriorLabels a b) :
    b.val=a.val+1 ∧
    Tendsto (fun n => mu n a+mu n b) atTop (nhds 0) ∧
    Tendsto (fun n => (theta n b-theta n a)/satelliteDistance (satellitesRelative (x n)) a b)
      atTop (nhds 1) ∧
    (∃ C : ℝ,0<C ∧ ∀ᶠ n in atTop,|r n b-r n a|≤
      C*eps n*(1-(mu n a+mu n b))*satelliteDistance (satellitesRelative (x n)) a b) ∧
    qLimit u≠qLimit w ∧ theta0 w-theta0 u=Coorbital.h ∧
    0≤muLimit u ∧ muLimit u≤1 ∧
    muLimit u*coorbitalKernel (theta0 a-theta0 u)+
      (1-muLimit u)*coorbitalKernel ((theta0 a-theta0 u)-Coorbital.h)=0 ∧
    0<muLimit u*Coorbital.kappa |theta0 a-theta0 u|+
      (1-muLimit u)*Coorbital.kappa |(theta0 a-theta0 u)-Coorbital.h| ∧
    Tendsto (fun n => (mu n a+mu n b)/satelliteDistance (satellitesRelative (x n)) a b^3)
      atTop (nhds (muLimit u*Coorbital.kappa |theta0 a-theta0 u|+
        (1-muLimit u)*Coorbital.kappa |(theta0 a-theta0 u)-Coorbital.h|)) ∧
    (∀ (u' w' : Satellite),u'<w' → ∀ d : Plane,c≠d →
      CompleteLimitingSatellitePair qLimit u' w' d → False) := by
  obtain ⟨hadj,hgd,_,_,hnu,hR⟩ := normalized_complete_pair_tangential_mass_scale eps mu x heps hepst hm hx hconv
    r theta hr hpolar horder muLimit hmt qLimit hqt a b hab c hpair theta0 hthetat
  obtain ⟨hnonneg,_,_,hmusum,hh,hprobe,hD⟩ := normalized_complete_pair_limiting_sources_and_probe eps mu x
    heps hepst hm hx hconv r theta hr hpolar horder muLimit hmt qLimit hqt a b hab c hpair theta0 hthetat u w huw hu hw
  have hdist := normalized_complete_pair_exterior_limits_distinct eps mu x heps hepst hm hx hconv
    r theta hr hpolar horder muLimit hmt qLimit hqt a b hab c hpair theta0 hthetat u w huw hu hw
  have hcube := (normalized_complete_pair_mass_cube_limit eps mu x heps hepst hm hx hconv r theta hr
    hpolar horder muLimit hmt qLimit hqt a b hab c hpair theta0 hthetat u w huw hu hw).2
  have hmw : muLimit w=1-muLimit u := by linarith
  have hpmax : muLimit u≤1 := by linarith [hnonneg w]
  have hshift : theta0 a-theta0 w=(theta0 a-theta0 u)-Coorbital.h := by linarith
  have hcoeff : muLimit u*Coorbital.kappa |theta0 a-theta0 u|+
      muLimit w*Coorbital.kappa |theta0 a-theta0 w|=
      muLimit u*Coorbital.kappa |theta0 a-theta0 u|+
        (1-muLimit u)*Coorbital.kappa |(theta0 a-theta0 u)-Coorbital.h| := by rw [hmw,hshift]
  have hgauge : muLimit u*coorbitalKernel (theta0 a-theta0 u)+
      (1-muLimit u)*coorbitalKernel ((theta0 a-theta0 u)-Coorbital.h)=0 := by
    rw [show theta0 u-theta0 a= -(theta0 a-theta0 u) by ring,
      show theta0 w-theta0 a= -((theta0 a-theta0 u)-Coorbital.h) by linarith,
      coorbitalKernel_neg,coorbitalKernel_neg,hmw] at hprobe
    linarith
  rw [hcoeff] at hD hcube
  refine ⟨hadj,hnu,hgd,hR,hdist,hh,hnonneg u,hpmax,hgauge,hD,hcube,?_⟩
  intro u' w' huw' d hcd hpair2
  exact normalized_complete_pairs_cannot_coexist eps mu x heps hepst hm hx hconv r theta hr hpolar horder
    muLimit hmt qLimit hqt a b u' w' hab huw' c d hcd hpair hpair2 theta0 hthetat

end DominantFiveBody
