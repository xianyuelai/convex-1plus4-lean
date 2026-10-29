import DominantFiveBody.CollisionPairScales
import DominantFiveBody.PairSequenceCapture
import DominantFiveBody.FixedAngleRows
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity

/-! # Actual complete-pair scale limits in inverse chart coordinates

Every scale-limit input is derived from source Proposition 4.2 on the
actual sequence. The arbitrary current pair fraction may oscillate.
-/

noncomputable section
open scoped BigOperators ContDiff
open Filter Set Topology

namespace DominantFiveBody

theorem pair_cube_ratio_inverse_third (nu d : ℝ) (hnu : 0<nu) (hd : 0<d) :
    (nu/d^3)^(-(1 : ℝ)/3)=d/nu^((1 : ℝ)/3) := by
  rw [Real.div_rpow hnu.le (pow_nonneg hd.le 3),
    ← Real.rpow_natCast_mul hd.le 3]
  norm_num only [Nat.cast_ofNat,show (3 : ℝ)*(-(1 : ℝ)/3)= -1 by ring]
  rw [Real.rpow_neg_one,Real.rpow_neg hnu.le]
  simp only [div_inv_eq_mul]
  ring

theorem pair_positive_cube_scale_tendsto (nu d : ℕ → ℝ) (D : ℝ)
    (hnu : ∀ n,0<nu n) (hd : ∀ n,0<d n) (hD : 0<D)
    (hlim : Tendsto (fun n => nu n/d n^3) atTop (nhds D)) :
    Tendsto (fun n => d n/(nu n)^((1 : ℝ)/3)) atTop (nhds (pairBoundaryScale D)) := by
  have ht := hlim.rpow_const (Or.inl (ne_of_gt hD)) (p := -(1 : ℝ)/3)
  simpa only [pair_cube_ratio_inverse_third _ _ (hnu _) (hd _),pairBoundaryScale] using ht

theorem current_unit_interval_combination_tendsto (alpha A B : ℕ → ℝ) (L : ℝ)
    (ha : ∀ n,0<alpha n ∧ alpha n<1)
    (hA : Tendsto A atTop (nhds L)) (hB : Tendsto B atTop (nhds L)) :
    Tendsto (fun n => alpha n*A n+(1-alpha n)*B n) atTop (nhds L) := by
  have ht := current_positive_weighted_average_tendsto alpha (fun n => 1-alpha n) A B L
    (fun n => (ha n).1) (fun n => sub_pos.mpr (ha n).2) hA hB
  apply ht.congr'
  exact Eventually.of_forall (fun n => by
    dsimp only
    rw [show alpha n+(1-alpha n)=1 by ring,div_one])

/-- Every inverse-coordinate limit needed for pair capture follows from
the actual Proposition 4.2. Relabeling places the pair first and exterior
sources last; subtracting the current first exterior angle fixes the
chart gauge. No limit of the current alpha fraction is taken. -/
theorem normalized_complete_pair_actual_chart_limits
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
    (hu : u∈pairExteriorLabels a b) (hw : w∈pairExteriorLabels a b)
    (e : Equiv.Perm Satellite) (he0 : e 0=a) (he1 : e 1=b) (he2 : e 2=u) (he3 : e 3=w) :
    Tendsto (fun n => pairPhysicalScale (mu n ∘ e)) atTop (nhds 0) ∧
    Tendsto (fun n => pairExteriorFraction (mu n ∘ e)) atTop (nhds (muLimit u)) ∧
    Tendsto (fun n => pairVariablesFromPolar (pairPhysicalScale (mu n ∘ e))
      (pairPhysicalFraction (mu n ∘ e)) (r n ∘ e) (fun i => theta n (e i)-theta n u))
      atTop (nhds (pairUnitPoint Coorbital.h (theta0 a-theta0 u)
        (pairBoundaryScale (pairProbeDerivative (muLimit u) Coorbital.h (theta0 a-theta0 u))))) := by
  obtain ⟨_,hgd,hrd,_,hnu,_⟩ := normalized_complete_pair_tangential_mass_scale eps mu x heps hepst hm hx hconv
    r theta hr hpolar horder muLimit hmt qLimit hqt a b hab c hpair theta0 hthetat
  obtain ⟨_,_,_,hmusum,hh,_,_⟩ := normalized_complete_pair_limiting_sources_and_probe eps mu x
    heps hepst hm hx hconv r theta hr hpolar horder muLimit hmt qLimit hqt a b hab c hpair theta0 hthetat u w huw hu hw
  obtain ⟨hD,hcube⟩ := normalized_complete_pair_mass_cube_limit eps mu x heps hepst hm hx hconv r theta hr
    hpolar horder muLimit hmt qLimit hqt a b hab c hpair theta0 hthetat u w huw hu hw
  have hmw : muLimit w=1-muLimit u := by linarith
  have hshift : theta0 a-theta0 w=(theta0 a-theta0 u)-Coorbital.h := by linarith
  have hcoeff : muLimit u*Coorbital.kappa |theta0 a-theta0 u|+
      muLimit w*Coorbital.kappa |theta0 a-theta0 w|=
      pairProbeDerivative (muLimit u) Coorbital.h (theta0 a-theta0 u) := by
    rw [hmw,hshift]
    rfl
  rw [hcoeff] at hD hcube
  have hrat (i : Satellite) : Tendsto (fun n => r n i) atTop (nhds 1) := by
    convert! dominant_satellite_radius_tendsto eps mu x heps hepst hm hx i using 1
    funext n
    rw [hpolar n]
    simp only [polarSatellites,polarPoint_norm,abs_of_pos (hr n i)]
  have htat (i : Satellite) : Tendsto (fun n => theta n i) atTop (nhds (theta0 i)) := by
    simpa only [Function.comp_def] using (continuous_apply i).tendsto theta0 |>.comp hthetat
  have hmass (i : Satellite) : Tendsto (fun n => mu n i) atTop (nhds (muLimit i)) := by
    simpa only [Function.comp_def] using (continuous_apply i).tendsto muLimit |>.comp hmt
  have hme (n : ℕ) : PositiveRatio (mu n ∘ e) := positiveRatio_satellitePermutation _ (hm n) e
  have ht : Tendsto (fun n => pairPhysicalScale (mu n ∘ e)) atTop (nhds 0) := by
    simpa only [pairPhysicalScale,Function.comp_apply,he0,he1,Real.zero_rpow (by norm_num : (1 : ℝ)/3≠0)] using
      hnu.rpow_const (Or.inr (by norm_num : (0 : ℝ)≤1/3))
  have hp : Tendsto (fun n => pairExteriorFraction (mu n ∘ e)) atTop (nhds (muLimit u)) := by
    unfold pairExteriorFraction
    simp only [Function.comp_apply,he2,he3]
    convert! (hmass u).div ((hmass u).add (hmass w)) (by rw [hmusum]; norm_num) using 1
    rw [hmusum,div_one]
  refine ⟨ht,hp,?_⟩
  let d := fun n => satelliteDistance (satellitesRelative (x n)) a b
  have hd (n : ℕ) : 0<d n := norm_pos_iff.mpr (sub_ne_zero.mpr
    ((satellitesRelative_collisionFree (x n) (hx n).1).2 a b (ne_of_lt hab)))
  have hdt : Tendsto (fun n => d n/pairPhysicalScale (mu n ∘ e)) atTop
      (nhds (pairBoundaryScale (pairProbeDerivative (muLimit u) Coorbital.h (theta0 a-theta0 u)))) := by
    simpa only [pairPhysicalScale,Function.comp_apply,he0,he1] using
      pair_positive_cube_scale_tendsto (fun n => mu n a+mu n b) d _
        (fun n => add_pos ((hm n).1 a) ((hm n).1 b)) hd hD hcube
  have hd0 : Tendsto d atTop (nhds 0) := complete_pair_distance_tendsto_zero _ _ hqt a b c hpair
  have hgap0 : Tendsto (fun n => theta n b-theta n a) atTop (nhds 0) := by
    have ht' : Tendsto (fun n => (theta n b-theta n a)/d n*d n) atTop (nhds 0) := by
      simpa only [mul_zero] using hgd.mul hd0
    apply ht'.congr'
    exact Eventually.of_forall (fun n => by dsimp only; exact div_mul_cancel₀ _ (ne_of_gt (hd n)))
  have hpb : theta0 b=theta0 a := sub_eq_zero.mp (tendsto_nhds_unique ((htat b).sub (htat a)) hgap0)
  have hrt : Tendsto (fun n => (r n b-r n a)/pairPhysicalScale (mu n ∘ e)) atTop (nhds 0) := by
    convert! hrd.mul hdt using 1
    · funext n
      have hdn := ne_of_gt (hd n)
      dsimp only [d] at hdn
      dsimp only [d]
      field_simp [hdn,ne_of_gt (pairPhysicalParameters_bounds _ (hme n)).1]
    · simp
  have hzt : Tendsto (fun n => (theta n b-theta n a)/pairPhysicalScale (mu n ∘ e)) atTop
      (nhds (pairBoundaryScale (pairProbeDerivative (muLimit u) Coorbital.h (theta0 a-theta0 u)))) := by
    convert! hgd.mul hdt using 1
    · funext n
      have hdn := ne_of_gt (hd n)
      dsimp only [d] at hdn
      dsimp only [d]
      field_simp [hdn,ne_of_gt (pairPhysicalParameters_bounds _ (hme n)).1]
    · simp
  let alpha := fun n => pairPhysicalFraction (mu n ∘ e)
  have ha (n : ℕ) : 0<alpha n ∧ alpha n<1 :=
    ⟨(pairPhysicalParameters_bounds _ (hme n)).2.2.1,(pairPhysicalParameters_bounds _ (hme n)).2.2.2.1⟩
  have hradAvg := current_unit_interval_combination_tendsto alpha (fun n => r n a) (fun n => r n b) 1 ha (hrat a) (hrat b)
  have hpairat : Tendsto (fun n => theta n a-theta n u) atTop (nhds (theta0 a-theta0 u)) :=
    (htat a).sub (htat u)
  have hpairbt : Tendsto (fun n => theta n b-theta n u) atTop (nhds (theta0 a-theta0 u)) := by
    simpa only [hpb] using (htat b).sub (htat u)
  have hangleAvg := current_unit_interval_combination_tendsto alpha _ _ (theta0 a-theta0 u) ha hpairat hpairbt
  have homega : Tendsto (fun n => theta n w-theta n u) atTop (nhds Coorbital.h) := by
    simpa only [hh] using (htat w).sub (htat u)
  apply tendsto_pi_nhds.mpr
  intro i
  fin_cases i
  · simpa [pairVariablesFromPolar,pairUnitPoint,he2] using hrat u
  · simpa [pairVariablesFromPolar,pairUnitPoint,he3] using hrat w
  · simpa [pairVariablesFromPolar,pairUnitPoint,he0,he1,alpha] using hradAvg
  · simpa [pairVariablesFromPolar,pairUnitPoint,he0,he1] using hrt
  · simpa [pairVariablesFromPolar,pairUnitPoint,he3] using homega
  · simpa [pairVariablesFromPolar,pairUnitPoint,he0,he1,alpha] using hangleAvg
  · simpa [pairVariablesFromPolar,pairUnitPoint,he0,he1] using hzt

theorem satelliteDistance_polar_sub_constant (r theta : Satellite → ℝ) (s : ℝ) (i j : Satellite) :
    satelliteDistance (polarSatellites r (fun k => theta k-s)) i j=
      satelliteDistance (polarSatellites r theta) i j := by
  have h0 := polar_distance_sq (r j) (r i) (theta j) (theta i)
  have h1 := polar_distance_sq (r j) (r i) (theta j-s) (theta i-s)
  rw [show (theta i-s)-(theta j-s)=theta i-theta j by ring] at h1
  unfold satelliteDistance polarSatellites
  nlinarith [norm_nonneg (polarPoint (r i) (theta i-s)-polarPoint (r j) (theta j-s)),
    norm_nonneg (polarPoint (r i) (theta i)-polarPoint (r j) (theta j))]

theorem radialResidual_sub_constant (eps : ℝ) (mu r theta : Satellite → ℝ) (s : ℝ) (i : Satellite) :
    radialResidual eps mu r (fun j => theta j-s) i=radialResidual eps mu r theta i := by
  have hdiff (j : Satellite) : (theta j-s)-(theta i-s)=theta j-theta i := by ring
  have havg : inner ℝ (relativeAverage mu (polarSatellites r (fun j => theta j-s)))
      (polarPoint 1 (theta i-s))=inner ℝ (relativeAverage mu (polarSatellites r theta))
        (polarPoint 1 (theta i)) := by
    simp only [relativeAverage,sum_inner,real_inner_smul_left,polarSatellites,polarPoint_inner_radial]
    simp_rw [hdiff]
  unfold radialResidual
  simp_rw [satelliteDistance_polar_sub_constant,hdiff]
  rw [havg]

theorem angularResidual_sub_constant (eps : ℝ) (mu r theta : Satellite → ℝ) (s : ℝ) (i : Satellite) :
    angularResidual eps mu r (fun j => theta j-s) i=angularResidual eps mu r theta i := by
  have hdiff (j : Satellite) : (theta j-s)-(theta i-s)=theta j-theta i := by ring
  unfold angularResidual
  simp_rw [satelliteDistance_polar_sub_constant,hdiff]

theorem relativeCollisionFree_polar_sub_constant (r theta : Satellite → ℝ) (s : ℝ)
    (hr : ∀ i,0<r i) (hcf : RelativeCollisionFree (polarSatellites r theta)) :
    RelativeCollisionFree (polarSatellites r (fun i => theta i-s)) := by
  constructor
  · intro i
    apply norm_ne_zero_iff.mp
    simpa only [polarSatellites,polarPoint_norm,abs_of_pos (hr i)] using ne_of_gt (hr i)
  · intro i j hij
    have hd : 0<satelliteDistance (polarSatellites r theta) i j :=
      norm_pos_iff.mpr (sub_ne_zero.mpr (hcf.2 i j hij))
    rw [← satelliteDistance_polar_sub_constant r theta s i j] at hd
    exact sub_ne_zero.mp (norm_ne_zero_iff.mp (ne_of_gt hd))

/-- Exact reindexing and current-angle gauge fixing produce a real
normalized physical root, before any appeal to chart uniqueness. -/
theorem normalized_polar_reindex_sub_constant (eps : ℝ) (mu : MassRatio) (x : Configuration)
    (heps : 0<eps) (hm : PositiveRatio mu) (hx : NormalizedCentralConfiguration (masses eps mu) x)
    (r theta : Satellite → ℝ) (hr : ∀ i,0<r i) (hpolar : satellitesRelative x=polarSatellites r theta)
    (e : Equiv.Perm Satellite) (s : ℝ) :
    RelativeCollisionFree (polarSatellites (r ∘ e) (fun i => theta (e i)-s)) ∧
    NormalizedCentralConfiguration (masses eps (mu ∘ e))
      (centeredFromRelative eps (mu ∘ e) (polarSatellites (r ∘ e) (fun i => theta (e i)-s))) := by
  have hroots := polarResiduals_zero_of_normalized eps mu x hx hm heps r theta hr hpolar
  have hmu := positiveRatio_satellitePermutation mu hm e
  have hcf0 : RelativeCollisionFree (polarSatellites (r ∘ e) (theta ∘ e)) := by
    have hcf := satellitesRelative_collisionFree x hx.1
    rw [hpolar] at hcf
    exact ⟨fun i => hcf.1 (e i),fun i j hij => hcf.2 (e i) (e j) (e.injective.ne hij)⟩
  have hcf := relativeCollisionFree_polar_sub_constant (r ∘ e) (theta ∘ e) s (fun i => hr (e i)) hcf0
  refine ⟨hcf,?_⟩
  apply normalized_of_vectorResidual_zero eps (mu ∘ e) (by linarith) hmu _ hcf
  apply (polarResiduals_zero_iff_vectorRoot eps (mu ∘ e) ((r ∘ e),(fun i => theta (e i)-s)) heps hmu
    (fun i => hr (e i))).mp
  constructor
  · intro i
    change radialResidual eps (mu ∘ e) (r ∘ e) (fun j => (theta ∘ e) j-s) i=0
    rw [radialResidual_sub_constant eps (mu ∘ e) (r ∘ e) (theta ∘ e),radialResidual_permutation]
    exact hroots.1 (e i)
  · intro i
    change angularResidual eps (mu ∘ e) (r ∘ e) (fun j => (theta ∘ e) j-s) i=0
    rw [angularResidual_sub_constant eps (mu ∘ e) (r ∘ e) (theta ∘ e),angularResidual_permutation]
    exact hroots.2 (e i)

theorem ordered_twoSourceSpan_lt_pi (theta : Satellite → ℝ) (u w k : Satellite)
    (hmono : Monotone theta) (hspan : theta 3-theta 0<Real.pi)
    (hgap : theta w-theta u=Coorbital.h) : twoSourceSpan (theta k-theta u)<Real.pi := by
  have hU := hmono (Fin.zero_le u)
  have hW := hmono (Fin.le_last w)
  have hKlo := hmono (Fin.zero_le k)
  have hKhi := hmono (Fin.le_last k)
  change theta w≤theta 3 at hW
  change theta k≤theta 3 at hKhi
  have hmax : max Coorbital.h (theta k-theta u)≤theta 3-theta u := by
    apply max_le <;> linarith
  have hmin : theta 0-theta u≤min 0 (theta k-theta u) := by
    apply le_min <;> linarith
  unfold twoSourceSpan
  linarith

/-- Actual complete-pair capture, with no chart-root, scale-limit,
regularity, positive probe, or current-fraction convergence assumptions.
The fixed-label collision limits are those selected in Section 4; the
physical coordinate permutation and angle gauge are explicit in the type.
-/
theorem normalized_complete_pair_actual_capture
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
    (hu : u∈pairExteriorLabels a b) (hw : w∈pairExteriorLabels a b)
    (e : Equiv.Perm Satellite) (he0 : e 0=a) (he1 : e 1=b) (he2 : e 2=u) (he3 : e 3=w) :
    ∃ keepD : Bool,Nonempty (PairCapturedBranches eps
      (fun n => pairPhysicalScale (mu n ∘ e)) (fun n => pairExteriorFraction (mu n ∘ e))
      (fun n => pairPhysicalFraction (mu n ∘ e))
      (fun n => pairVariablesFromPolar (pairPhysicalScale (mu n ∘ e)) (pairPhysicalFraction (mu n ∘ e))
        (r n ∘ e) (fun i => theta n (e i)-theta n u)) (theta0 a-theta0 u) keepD) := by
  obtain ⟨_,_,_,_,_,hgap,hp0,hp1,hprobe,_,_,_⟩ := normalized_complete_pair_scale_complete eps mu x
    heps hepst hm hx hconv r theta hr hpolar horder muLimit hmt qLimit hqt a b hab c hpair theta0 hthetat u w huw hu hw
  have hrat (i : Satellite) : Tendsto (fun n => r n i) atTop (nhds 1) := by
    convert! dominant_satellite_radius_tendsto eps mu x heps hepst hm hx i using 1
    funext n
    rw [hpolar n]
    simp only [polarSatellites,polarPoint_norm,abs_of_pos (hr n i)]
  have htat (i : Satellite) : Tendsto (fun n => theta n i) atTop (nhds (theta0 i)) := by
    simpa only [Function.comp_def] using (continuous_apply i).tendsto theta0 |>.comp hthetat
  have hroots : ∀ n i,angularResidual (eps n) (mu n) (r n) (theta n) i=0 :=
    fun n => (polarResiduals_zero_of_normalized (eps n) (mu n) (x n) (hx n) (hm n) (heps n)
      (r n) (theta n) (hr n) (hpolar n)).2
  have hspan : theta0 3-theta0 0<Real.pi :=
    ordered_full_angular_limit_span_lt_pi eps heps hepst mu r theta (fun n => (hm n).1)
      (fun n => (hm n).2) hr hroots horder muLimit (fun _ => 1) theta0 (fun _ => rfl)
      hmt (tendsto_pi_nhds.mpr hrat) hthetat
  have hmono : Monotone theta0 := by
    intro i j hij
    rcases hij.eq_or_lt with rfl|hlt
    · rfl
    · exact sub_nonneg.mp (ge_of_tendsto ((htat j).sub (htat i))
        (Eventually.of_forall (fun n => (horder n i j hlt).1.le)))
  have hunit (i : Satellite) : qLimit i=polarPoint 1 (theta0 i) := by
    have hqi : Tendsto (fun n => satellitesRelative (x n) i) atTop (nhds (qLimit i)) := by
      simpa only [Function.comp_def] using (continuous_apply i).tendsto qLimit |>.comp hqt
    have hp := (polarPoint_contDiff ∞).continuous.continuousAt.tendsto.comp
      ((hrat i).prodMk_nhds (htat i))
    apply tendsto_nhds_unique hqi
    simpa only [hpolar,polarSatellites,Function.comp_def] using hp
  have hne (j : Satellite) (hj : j∈pairExteriorLabels a b) : theta0 a≠theta0 j := by
    intro he
    have hc : qLimit j=c := by
      rw [hunit j,← he,← hunit a]
      exact (hpair a).mpr (Or.inl rfl)
    rcases (hpair j).mp hc with hja|hjb
    · exact (Finset.mem_erase.mp (Finset.mem_erase.mp hj).2).1 hja
    · exact (Finset.mem_erase.mp hj).1 hjb
  have hpsi0 : theta0 a-theta0 u≠0 := sub_ne_zero.mpr (hne u hu)
  have hpsih : theta0 a-theta0 u≠Coorbital.h := by
    intro he
    exact hne w hw (by linarith)
  have hspanG := ordered_twoSourceSpan_lt_pi theta0 u w a hmono hspan hgap
  obtain ⟨ht,hp,hy⟩ := normalized_complete_pair_actual_chart_limits eps mu x heps hepst hm hx hconv
    r theta hr hpolar horder muLimit hmt qLimit hqt a b hab c hpair theta0 hthetat u w huw hu hw e he0 he1 he2 he3
  have hphys (n : ℕ) := normalized_polar_reindex_sub_constant (eps n) (mu n) (x n) (heps n) (hm n) (hx n)
    (r n) (theta n) (hr n) (hpolar n) e (theta n u)
  have hcapture (keepD : Bool) (hkeep : if keepD then 0<muLimit u else muLimit u<1) :
      Nonempty (PairCapturedBranches eps (fun n => pairPhysicalScale (mu n ∘ e))
        (fun n => pairExteriorFraction (mu n ∘ e)) (fun n => pairPhysicalFraction (mu n ∘ e))
        (fun n => pairVariablesFromPolar (pairPhysicalScale (mu n ∘ e)) (pairPhysicalFraction (mu n ∘ e))
          (r n ∘ e) (fun i => theta n (e i)-theta n u)) (theta0 a-theta0 u) keepD) := by
    exact pairPhysical_sequence_capture_of_scaled_limits (muLimit u) (theta0 a-theta0 u) keepD hp0 hp1 hkeep
      hpsi0 hpsih hspanG hprobe eps (fun n => mu n ∘ e) (fun n => r n ∘ e)
      (fun n i => theta n (e i)-theta n u) heps (fun n => positiveRatio_satellitePermutation _ (hm n) e)
      (fun n i => hr n (e i)) (fun n => by rw [he2,sub_self])
      (fun n => (hphys n).1) (fun n => (hphys n).2) hepst ht hp hy
  by_cases hpos : 0<muLimit u
  · exact ⟨true,hcapture true hpos⟩
  · exact ⟨false,hcapture false (by simp only [Bool.false_eq_true,if_false]; linarith)⟩

end DominantFiveBody
