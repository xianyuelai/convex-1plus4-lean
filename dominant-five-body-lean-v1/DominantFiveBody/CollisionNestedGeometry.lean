import DominantFiveBody.CollisionNestedScales
import DominantFiveBody.CollisionSubsequence

/-! # Actual current-weight grouping for a nested triple

Internal smaller-pair forces cancel before taking any limit. The grouping
does not select or assume convergence of the current internal mass share.
-/

noncomputable section
open scoped BigOperators ContDiff
open Filter Set Topology

namespace DominantFiveBody

theorem nested_diameter_cross_bounds (q : SatelliteConfiguration) (a b c : Satellite) :
    satelliteDistance q a c≤tripleLargestDistance q a b c ∧
    satelliteDistance q b c≤tripleLargestDistance q a b c ∧
    tripleLargestDistance q a b c≤satelliteDistance q a c+satelliteDistance q a b ∧
    tripleLargestDistance q a b c≤satelliteDistance q b c+satelliteDistance q a b := by
  have htriA : satelliteDistance q b c≤satelliteDistance q a c+satelliteDistance q a b := by
    unfold satelliteDistance
    calc
      ‖q b-q c‖=‖(q b-q a)+(q a-q c)‖ := by congr 1; abel
      _≤‖q b-q a‖+‖q a-q c‖ := norm_add_le _ _
      _=‖q a-q c‖+‖q a-q b‖ := by rw [norm_sub_rev (q b)]; ring
  have htriB : satelliteDistance q a c≤satelliteDistance q b c+satelliteDistance q a b := by
    unfold satelliteDistance
    calc
      ‖q a-q c‖=‖(q a-q b)+(q b-q c)‖ := by congr 1; abel
      _≤‖q a-q b‖+‖q b-q c‖ := norm_add_le _ _
      _=‖q b-q c‖+‖q a-q b‖ := by ring
  have hab0 : 0≤satelliteDistance q a b := norm_nonneg _
  have hac0 : 0≤satelliteDistance q a c := norm_nonneg _
  have hbc0 : 0≤satelliteDistance q b c := norm_nonneg _
  refine ⟨(le_max_left _ _).trans (le_max_right _ _),
    (le_max_right _ _).trans (le_max_right _ _),?_,?_⟩
  · exact max_le (by linarith) (max_le (by linarith) htriA)
  · exact max_le (by linarith) (max_le htriB (by linarith))

/-- Two cross distances both approach the actual diameter when the pair
distance is negligible; no selected direction or mass enters this fact. -/
theorem nested_cross_distance_diameter_ratios (q : ℕ → SatelliteConfiguration)
    (a b c : Satellite) (d : ℕ → ℝ) (hd : ∀ n,0<d n)
    (hdiam : ∀ n,d n=tripleLargestDistance (q n) a b c)
    (hpair : Tendsto (fun n => satelliteDistance (q n) a b/d n) atTop (nhds 0)) :
    Tendsto (fun n => satelliteDistance (q n) a c/d n) atTop (nhds 1) ∧
    Tendsto (fun n => satelliteDistance (q n) b c/d n) atTop (nhds 1) := by
  have ht := (tendsto_const_nhds : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (nhds 1)).sub hpair
  have hlow : Tendsto (fun n => 1-satelliteDistance (q n) a b/d n) atTop (nhds 1) := by
    convert! ht using 1
    ring
  constructor
  · apply tendsto_of_tendsto_of_tendsto_of_le_of_le' hlow tendsto_const_nhds
    · exact Eventually.of_forall (fun n => by
        have hb := (nested_diameter_cross_bounds (q n) a b c).2.2.1
        rw [← hdiam n] at hb
        apply (le_div_iff₀ (hd n)).mpr
        have hdn := ne_of_gt (hd n)
        field_simp [hdn]
        linarith)
    · exact Eventually.of_forall (fun n => (div_le_one (hd n)).mpr
        (by rw [hdiam n]; exact (nested_diameter_cross_bounds (q n) a b c).1))
  · apply tendsto_of_tendsto_of_tendsto_of_le_of_le' hlow tendsto_const_nhds
    · exact Eventually.of_forall (fun n => by
        have hb := (nested_diameter_cross_bounds (q n) a b c).2.2.2
        rw [← hdiam n] at hb
        apply (le_div_iff₀ (hd n)).mpr
        have hdn := ne_of_gt (hd n)
        field_simp [hdn]
        linarith)
    · exact Eventually.of_forall (fun n => (div_le_one (hd n)).mpr
        (by rw [hdiam n]; exact (nested_diameter_cross_bounds (q n) a b c).2.1))

theorem satelliteInteraction_projection_sum_newton (mu : MassRatio)
    (q : SatelliteConfiguration) (i : Satellite) (v : Plane) :
    inner ℝ (satelliteInteraction mu q i) v=
      ∑ j,mu j*inner ℝ (newtonTargetField (q j) (q i)) v := by
  rw [← Finset.sum_erase_add _ _ (Finset.mem_univ i)]
  simp only [newtonTargetField,sub_self,norm_zero,zero_pow (by decide : 3≠0),inv_zero,
    zero_smul,inner_zero_left,mul_zero,add_zero]
  simp only [satelliteInteraction,sum_inner,real_inner_smul_left,
    satelliteDistance,div_eq_mul_inv,norm_sub_rev (q i)]
  apply Finset.sum_congr rfl
  intro j _
  ring

@[simp] theorem newtonTargetField_self (q : Plane) : newtonTargetField q q=0 := by
  simp [newtonTargetField]

theorem newtonTargetField_projection_reverse (q p v : Plane) :
    inner ℝ (newtonTargetField q p) v= -inner ℝ (newtonTargetField p q) v := by
  simp only [newtonTargetField,real_inner_smul_left,inner_sub_left,norm_sub_rev q p]
  ring

/-- The original vector equations, projected on any fixed direction,
give the current pair-versus-third-body weighted macro identity. -/
theorem physical_nested_vector_projection_average (eps : ℝ) (mu : MassRatio)
    (q : SatelliteConfiguration) (a b c p : Satellite)
    (hab : a≠b) (hcp : c≠p) (hc : c∈pairExteriorLabels a b) (hp : p∈pairExteriorLabels a b)
    (hxi : mu a+mu b≠0) (hroot : ∀ i,vectorResidual eps mu q i=0) (v : Plane) :
    (mu a*inner ℝ (primaryRadialField (q a)) v+mu b*inner ℝ (primaryRadialField (q b)) v)/(mu a+mu b)-
      inner ℝ (primaryRadialField (q c)) v+
      eps*((mu a+mu b+mu c)*
        ((mu a*inner ℝ (newtonTargetField (q c) (q a)) v+
          mu b*inner ℝ (newtonTargetField (q c) (q b)) v)/(mu a+mu b))+
        mu p*((mu a*inner ℝ (newtonTargetField (q p) (q a)) v+
          mu b*inner ℝ (newtonTargetField (q p) (q b)) v)/(mu a+mu b)-
          inner ℝ (newtonTargetField (q p) (q c)) v))=0 := by
  have hrows (i : Satellite) : inner ℝ (primaryRadialField (q i)) v+
      eps*inner ℝ (satelliteInteraction mu q i) v-eps*inner ℝ (relativeField mu q) v=0 := by
    have hrow := hroot i
    change primaryRadialField (q i)+eps • satelliteInteraction mu q i-
      eps • relativeField mu q=0 at hrow
    simpa only [inner_sub_left,inner_add_left,real_inner_smul_left,inner_zero_left] using
      congrArg (fun z : Plane => inner ℝ z v) hrow
  have ha := hrows a
  have hb := hrows b
  have hcc := hrows c
  rw [satelliteInteraction_projection_sum_newton,sum_satellite_selected_four _ a b c p hab hcp hc hp] at ha hb hcc
  simp only [newtonTargetField_self,inner_zero_left,mul_zero,zero_add,add_zero] at ha hb hcc
  have hba := newtonTargetField_projection_reverse (q a) (q b) v
  have hca := newtonTargetField_projection_reverse (q a) (q c) v
  have hcb := newtonTargetField_projection_reverse (q b) (q c) v
  rw [hba] at hb
  rw [hca,hcb] at hcc
  field_simp [hxi]
  linear_combination mu a*ha+mu b*hb-(mu a+mu b)*hcc

theorem newtonTargetField_scaled_projection_limit
    (source qa qb : ℕ → Plane) (d : ℕ → ℝ) (source0 target0 direction v : Plane)
    (hs : Tendsto source atTop (nhds source0))
    (ha : Tendsto qa atTop (nhds target0)) (hb : Tendsto qb atTop (nhds target0))
    (hd : ∀ n,0<d n)
    (hdir : Tendsto (fun n => (d n)⁻¹ • (qb n-qa n)) atTop (nhds direction))
    (hsep : source0≠target0) (hsepa : ∀ n,source n≠qa n) (hsepb : ∀ n,source n≠qb n) :
    Tendsto (fun n => inner ℝ (newtonTargetField (source n) (qb n)-newtonTargetField (source n) (qa n)) v/d n)
      atTop (nhds (inner ℝ (dividedNewtonTargetField source0 target0 target0 direction) v)) := by
  have hc := (dividedNewtonTargetField_joint_contDiffAt ∞ ((source0,target0),(target0,direction)) hsep hsep).continuousAt.tendsto
  have ht := hc.comp ((hs.prodMk_nhds ha).prodMk_nhds (hb.prodMk_nhds hdir))
  have hi := ht.inner (𝕜 := ℝ) (tendsto_const_nhds : Tendsto (fun _ : ℕ => v) atTop (nhds v))
  convert! hi using 1
  funext n
  simp only [Function.comp_def]
  have hgap : qb n-qa n=d n • ((d n)⁻¹ • (qb n-qa n)) := by
    rw [smul_smul,mul_inv_cancel₀ (ne_of_gt (hd n)),one_smul]
  rw [dividedNewtonTargetField_eq (source n) (qa n) (qb n) _ (d n)
    (ne_of_gt (hd n)) (hsepa n) (hsepb n) hgap,real_inner_smul_left]
  simp only [div_eq_mul_inv,mul_comm]

theorem primaryRadialField_scaled_projection_limit
    (qa qb : ℕ → Plane) (d : ℕ → ℝ) (c direction : Plane)
    (ha : Tendsto qa atTop (nhds c)) (hb : Tendsto qb atTop (nhds c))
    (hd : ∀ n,0<d n) (hc : ‖c‖=1)
    (hqa : ∀ n,qa n≠0) (hqb : ∀ n,qb n≠0)
    (hdir : Tendsto (fun n => (d n)⁻¹ • (qb n-qa n)) atTop (nhds direction)) :
    Tendsto (fun n => inner ℝ (primaryRadialField (qb n)-primaryRadialField (qa n)) c/d n)
      atTop (nhds (3*inner ℝ direction c)) := by
  have hc0 : c≠0 := by intro heq; simp [heq] at hc
  have hN := newtonTargetField_scaled_projection_limit (fun _ => 0) qa qb d 0 c direction c
    tendsto_const_nhds ha hb hd hdir hc0.symm (fun n => (hqa n).symm) (fun n => (hqb n).symm)
  have hV := hdir.inner (𝕜 := ℝ) (tendsto_const_nhds : Tendsto (fun _ : ℕ => c) atTop (nhds c))
  have hsum := hV.add hN
  convert! hsum using 1
  · funext n
    rw [primaryRadialField_eq_newton,primaryRadialField_eq_newton]
    simp only [inner_add_left,inner_sub_left,real_inner_smul_left]
    ring
  · rw [← inner_add_left,dividedNewtonTargetField_unit_diagonal c direction hc,
      real_inner_smul_left,real_inner_self_eq_norm_sq,hc]
    ring

/-- Multiplication by the actual square scale removes the near source's
inverse-cube singularity in every fixed scalar projection. -/
theorem newtonTargetField_near_scaled_projection_limit
    (source target : ℕ → Plane) (d : ℕ → ℝ) (direction v : Plane)
    (hd : ∀ n,0<d n) (hdir : Tendsto (fun n => (d n)⁻¹ • (target n-source n)) atTop (nhds direction))
    (hunit : ‖direction‖=1) (hsep : ∀ n,source n≠target n) :
    Tendsto (fun n => d n^2*inner ℝ (newtonTargetField (source n) (target n)) v)
      atTop (nhds (-inner ℝ direction v)) := by
  have hD : Tendsto (fun n => ‖source n-target n‖/d n) atTop (nhds 1) := by
    convert! hdir.norm using 1
    · funext n
      rw [norm_smul,Real.norm_eq_abs,abs_inv,abs_of_pos (hd n),norm_sub_rev]
      ring
    · rw [hunit]
  have hi := hdir.inner (𝕜 := ℝ) (tendsto_const_nhds : Tendsto (fun _ : ℕ => v) atTop (nhds v))
  have ht := hi.neg.div (hD.pow 3) (by norm_num : (1 : ℝ)^3≠0)
  convert! ht using 1
  · funext n
    have hdn := ne_of_gt (hd n)
    have hDn := norm_ne_zero_iff.mpr (sub_ne_zero.mpr (hsep n))
    simp only [Pi.div_apply,newtonTargetField,real_inner_smul_left,inner_sub_left]
    field_simp [hdn,hDn]
    ring
  · simp

/-- The selected two-group limit of a real nested triple is tangential.
The two pair representatives have the same scaled limit; their current
positive normalized weights need not converge. The actual initial triple
cube bound is used only after the internal pair forces have cancelled. -/
theorem physical_nested_selected_group_radial
    (eps : ℕ → ℝ) (mu : ℕ → MassRatio) (q : ℕ → SatelliteConfiguration)
    (heps : Tendsto eps atTop (nhds 0)) (hm : ∀ n,PositiveRatio (mu n))
    (hroot : ∀ n i,vectorResidual (eps n) (mu n) (q n) i=0)
    (hcf : ∀ n,RelativeCollisionFree (q n))
    (mu0 : MassRatio) (hmu : Tendsto mu atTop (nhds mu0))
    (a b c p : Satellite) (hab : a≠b) (hcp : c≠p)
    (hc : c∈pairExteriorLabels a b) (hp : p∈pairExteriorLabels a b)
    (c0 p0 direction : Plane) (hcunit : ‖c0‖=1) (hdirunit : ‖direction‖=1) (hsep : p0≠c0)
    (hqa : Tendsto (fun n => q n a) atTop (nhds c0))
    (hqb : Tendsto (fun n => q n b) atTop (nhds c0))
    (hqc : Tendsto (fun n => q n c) atTop (nhds c0))
    (hqp : Tendsto (fun n => q n p) atTop (nhds p0))
    (d : ℕ → ℝ) (hd : ∀ n,0<d n)
    (hdirac : Tendsto (fun n => (d n)⁻¹ • (q n a-q n c)) atTop (nhds direction))
    (hdirbc : Tendsto (fun n => (d n)⁻¹ • (q n b-q n c)) atTop (nhds direction))
    (C : ℝ) (hbound : ∀ᶠ n in atTop,(mu n a+mu n b+mu n c)/d n^3≤C) :
    inner ℝ direction c0=0 := by
  have hca : c≠a := (Finset.mem_erase.mp (Finset.mem_erase.mp hc).2).1
  have hcb : c≠b := (Finset.mem_erase.mp hc).1
  have hpa : p≠a := (Finset.mem_erase.mp (Finset.mem_erase.mp hp).2).1
  have hpb : p≠b := (Finset.mem_erase.mp hp).1
  have hPhiA := primaryRadialField_scaled_projection_limit _ _ d c0 direction hqc hqa hd hcunit
    (fun n => (hcf n).1 c) (fun n => (hcf n).1 a) hdirac
  have hPhiB := primaryRadialField_scaled_projection_limit _ _ d c0 direction hqc hqb hd hcunit
    (fun n => (hcf n).1 c) (fun n => (hcf n).1 b) hdirbc
  have hPhi := current_positive_weighted_average_tendsto (fun n => mu n a) (fun n => mu n b)
    (fun n => inner ℝ (primaryRadialField (q n a)-primaryRadialField (q n c)) c0/d n)
    (fun n => inner ℝ (primaryRadialField (q n b)-primaryRadialField (q n c)) c0/d n)
    (3*inner ℝ direction c0) (fun n => (hm n).1 a) (fun n => (hm n).1 b) hPhiA hPhiB
  have hKA := newtonTargetField_near_scaled_projection_limit _ _ d direction c0 hd hdirac hdirunit
    (fun n => (hcf n).2 c a hca)
  have hKB := newtonTargetField_near_scaled_projection_limit _ _ d direction c0 hd hdirbc hdirunit
    (fun n => (hcf n).2 c b hcb)
  have hK := current_positive_weighted_average_tendsto (fun n => mu n a) (fun n => mu n b)
    (fun n => d n^2*inner ℝ (newtonTargetField (q n c) (q n a)) c0)
    (fun n => d n^2*inner ℝ (newtonTargetField (q n c) (q n b)) c0)
    (-inner ℝ direction c0) (fun n => (hm n).1 a) (fun n => (hm n).1 b) hKA hKB
  have hJA := newtonTargetField_scaled_projection_limit _ _ _ d p0 c0 direction c0 hqp hqc hqa hd hdirac hsep
    (fun n => (hcf n).2 p c hcp.symm) (fun n => (hcf n).2 p a hpa)
  have hJB := newtonTargetField_scaled_projection_limit _ _ _ d p0 c0 direction c0 hqp hqc hqb hd hdirbc hsep
    (fun n => (hcf n).2 p c hcp.symm) (fun n => (hcf n).2 p b hpb)
  have hJ := current_positive_weighted_average_tendsto (fun n => mu n a) (fun n => mu n b)
    (fun n => inner ℝ (newtonTargetField (q n p) (q n a)-newtonTargetField (q n p) (q n c)) c0/d n)
    (fun n => inner ℝ (newtonTargetField (q n p) (q n b)-newtonTargetField (q n p) (q n c)) c0/d n)
    (inner ℝ (dividedNewtonTargetField p0 c0 c0 direction) c0)
    (fun n => (hm n).1 a) (fun n => (hm n).1 b) hJA hJB
  have hmassBound : IsBoundedUnder (·≤·) atTop (norm ∘ fun n => (mu n a+mu n b+mu n c)/d n^3) := by
    refine ⟨C,?_⟩
    change ∀ᶠ n in atTop, ‖(mu n a+mu n b+mu n c)/d n^3‖≤C
    filter_upwards [hbound] with n hn
    simpa only [Function.comp_def,Real.norm_eq_abs,abs_of_pos
      (div_pos (add_pos (add_pos ((hm n).1 a) ((hm n).1 b)) ((hm n).1 c)) (pow_pos (hd n) 3))] using hn
  have henu : Tendsto (fun n => eps n*((mu n a+mu n b+mu n c)/d n^3)) atTop (nhds 0) := by
    convert! NormedField.tendsto_zero_smul_of_tendsto_zero_of_bounded heps hmassBound using 1
  have hmp : Tendsto (fun n => mu n p) atTop (nhds (mu0 p)) := by
    simpa only [Function.comp_def] using (continuous_apply p).tendsto mu0 |>.comp hmu
  have ht := hPhi.add ((henu.mul hK).add ((heps.mul hmp).mul hJ))
  have hz : Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (nhds (3*inner ℝ direction c0)) := by
    convert! ht using 1
    · funext n
      have hxi := ne_of_gt (add_pos ((hm n).1 a) ((hm n).1 b))
      have hdn := ne_of_gt (hd n)
      have havg := physical_nested_vector_projection_average (eps n) (mu n) (q n) a b c p
        hab hcp hc hp hxi (hroot n) c0
      simp only [inner_sub_left]
      field_simp [hxi,hdn]
      field_simp [hxi] at havg
      linear_combination -havg
    · ring
  have heq := tendsto_nhds_unique hz (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (nhds 0))
  nlinarith

/-- Compactness removes the selected direction premise from the actual
nested two-group radial estimate. The diameter and small pair are genuine
physical distances throughout this statement. -/
theorem physical_nested_group_radial_projections_tendsto
    (eps : ℕ → ℝ) (mu : ℕ → MassRatio) (q : ℕ → SatelliteConfiguration)
    (heps : Tendsto eps atTop (nhds 0)) (hm : ∀ n,PositiveRatio (mu n))
    (hroot : ∀ n i,vectorResidual (eps n) (mu n) (q n) i=0)
    (hcf : ∀ n,RelativeCollisionFree (q n))
    (mu0 : MassRatio) (hmu : Tendsto mu atTop (nhds mu0))
    (a b c p : Satellite) (hab : a≠b) (hcp : c≠p)
    (hc : c∈pairExteriorLabels a b) (hp : p∈pairExteriorLabels a b)
    (c0 p0 : Plane) (hcunit : ‖c0‖=1) (hsep : p0≠c0)
    (hqa : Tendsto (fun n => q n a) atTop (nhds c0))
    (hqb : Tendsto (fun n => q n b) atTop (nhds c0))
    (hqc : Tendsto (fun n => q n c) atTop (nhds c0))
    (hqp : Tendsto (fun n => q n p) atTop (nhds p0))
    (d : ℕ → ℝ) (hd : ∀ n,0<d n) (hdiam : ∀ n,d n=tripleLargestDistance (q n) a b c)
    (hpair : Tendsto (fun n => satelliteDistance (q n) a b/d n) atTop (nhds 0))
    (C : ℝ) (hbound : ∀ᶠ n in atTop,(mu n a+mu n b+mu n c)/d n^3≤C) :
    Tendsto (fun n => inner ℝ ((d n)⁻¹ • (q n a-q n c)) c0) atTop (nhds 0) ∧
    Tendsto (fun n => inner ℝ ((d n)⁻¹ • (q n b-q n c)) c0) atTop (nhds 0) := by
  let u : ℕ → Plane := fun n => (d n)⁻¹ • (q n a-q n c)
  let delta : ℕ → Plane := fun n => (d n)⁻¹ • (q n b-q n a)
  have hnorm (n : ℕ) : ‖u n‖=satelliteDistance (q n) a c/d n := by
    dsimp only [u]
    rw [norm_smul,Real.norm_eq_abs,abs_inv,abs_of_pos (hd n)]
    simp only [satelliteDistance,div_eq_mul_inv,mul_comm]
  have hnormle (n : ℕ) : ‖u n‖≤1 := by
    rw [hnorm]
    exact (div_le_one (hd n)).mpr (by rw [hdiam n]; exact (nested_diameter_cross_bounds (q n) a b c).1)
  have hcross := (nested_cross_distance_diameter_ratios q a b c d hd hdiam hpair).1
  have hnormt : Tendsto (fun n => ‖u n‖) atTop (nhds 1) := by
    simpa only [hnorm] using hcross
  have hdelta : Tendsto delta atTop (nhds 0) := by
    apply tendsto_zero_iff_norm_tendsto_zero.mpr
    convert! hpair using 1
    funext n
    dsimp only [delta]
    rw [norm_smul,Real.norm_eq_abs,abs_inv,abs_of_pos (hd n),norm_sub_rev]
    simp only [satelliteDistance,div_eq_mul_inv,mul_comm]
  have hu : Tendsto (fun n => inner ℝ (u n) c0) atTop (nhds 0) := by
    apply Metric.tendsto_atTop.mpr
    intro eta heta
    by_contra hbad
    push Not at hbad
    have hfreq : ∃ᶠ n in atTop,eta≤dist (inner ℝ (u n) c0) 0 := frequently_atTop.mpr hbad
    let S : Set Plane := Metric.closedBall 0 1 ∩ {z | eta≤|inner ℝ z c0|}
    have hcont : Continuous (fun z : Plane => |inner ℝ z c0|) := by fun_prop
    have hS : IsCompact S := (isCompact_closedBall (0 : Plane) 1).inter_right
      (isClosed_le continuous_const hcont)
    have hfreqS : ∃ᶠ n in atTop,u n∈S := hfreq.mono (fun n hn =>
      ⟨by simpa only [Metric.mem_closedBall,dist_zero_right] using hnormle n,
        by simpa only [Real.dist_eq,sub_zero,Set.mem_ofPred_eq] using hn⟩)
    obtain ⟨v,hv,phi,hphi,hvt⟩ := hS.tendsto_subseq' hfreqS
    have hphiTop := hphi.tendsto_atTop
    have hvunit : ‖v‖=1 := tendsto_nhds_unique hvt.norm (hnormt.comp hphiTop)
    have hvb : Tendsto (fun n => (d (phi n))⁻¹ • (q (phi n) b-q (phi n) c)) atTop (nhds v) := by
      convert! hvt.add (hdelta.comp hphiTop) using 1
      · funext n
        dsimp only [u,delta,Function.comp_def]
        module
      · rw [add_zero]
    have hbound' := hphiTop.eventually hbound
    have hzero := physical_nested_selected_group_radial (eps ∘ phi) (mu ∘ phi) (q ∘ phi)
      (heps.comp hphiTop) (fun n => hm (phi n)) (fun n => hroot (phi n)) (fun n => hcf (phi n))
      mu0 (hmu.comp hphiTop) a b c p hab hcp hc hp c0 p0 v hcunit hvunit hsep
      (hqa.comp hphiTop) (hqb.comp hphiTop) (hqc.comp hphiTop) (hqp.comp hphiTop)
      (d ∘ phi) (fun n => hd (phi n)) hvt hvb C hbound'
    have he : eta≤0 := by simpa only [Set.mem_ofPred_eq,hzero,abs_zero] using hv.2
    linarith
  refine ⟨hu,?_⟩
  have ht := hu.add (hdelta.inner (𝕜 := ℝ) (tendsto_const_nhds : Tendsto (fun _ : ℕ => c0) atTop (nhds c0)))
  convert! ht using 1
  · funext n
    dsimp only [u,delta]
    rw [← inner_add_left]
    congr 1
    module
  · simp

/-- A bounded real scaled polar displacement has negligible radial
coordinate exactly when its limiting radial projection does. The moving
midpoint radial basis is retained in the proof. -/
theorem polar_scaled_radius_difference_tendsto_zero
    (ra va rb vb d : ℕ → ℝ) (psi : ℝ)
    (hva : Tendsto va atTop (nhds psi)) (hvb : Tendsto vb atTop (nhds psi))
    (hd : ∀ n,0<d n)
    (hbound : ∀ n,‖(d n)⁻¹ • (polarPoint (rb n) (vb n)-polarPoint (ra n) (va n))‖≤1)
    (hproj : Tendsto (fun n => inner ℝ ((d n)⁻¹ •
      (polarPoint (rb n) (vb n)-polarPoint (ra n) (va n))) (polarPoint 1 psi)) atTop (nhds 0)) :
    Tendsto (fun n => (rb n-ra n)/d n) atTop (nhds 0) := by
  let u : ℕ → Plane := fun n => (d n)⁻¹ • (polarPoint (rb n) (vb n)-polarPoint (ra n) (va n))
  let e : ℕ → Plane := fun n => polarPoint 1 ((va n+vb n)/2)
  have hmid : Tendsto (fun n => (va n+vb n)/2) atTop (nhds psi) := by
    convert! (hva.add hvb).div_const 2 using 1
    ring
  have het : Tendsto e atTop (nhds (polarPoint 1 psi)) := by
    exact ((polarPoint_contDiff ∞).continuous.tendsto (1,psi)).comp (tendsto_const_nhds.prodMk_nhds hmid)
  have hdiff : Tendsto (fun n => ‖e n-polarPoint 1 psi‖) atTop (nhds 0) := by
    simpa only [sub_self,norm_zero] using (het.sub
      (tendsto_const_nhds : Tendsto (fun _ : ℕ => polarPoint 1 psi) atTop (nhds (polarPoint 1 psi)))).norm
  have herr : Tendsto (fun n => inner ℝ (u n) (e n-polarPoint 1 psi)) atTop (nhds 0) := by
    apply squeeze_zero_norm _ hdiff
    intro n
    rw [Real.norm_eq_abs]
    exact (abs_real_inner_le_norm _ _).trans
      ((mul_le_mul_of_nonneg_right (hbound n) (norm_nonneg _)).trans_eq (one_mul _))
  have hinner : Tendsto (fun n => inner ℝ (u n) (e n)) atTop (nhds 0) := by
    convert! hproj.add herr using 1
    · funext n
      simp only [inner_sub_right]
      ring
    · ring
  have hgap : Tendsto (fun n => (vb n-va n)/2) atTop (nhds 0) := by
    simpa only [sub_self,zero_div] using (hvb.sub hva).div_const 2
  have hcos : Tendsto (fun n => Real.cos ((vb n-va n)/2)) atTop (nhds 1) := by
    simpa only [Function.comp_def,Real.cos_zero] using Real.continuous_cos.continuousAt.tendsto.comp hgap
  have hquot : Tendsto (fun n => inner ℝ (u n) (e n)/Real.cos ((vb n-va n)/2)) atTop (nhds 0) := by
    convert! hinner.div hcos (by norm_num : (1 : ℝ)≠0) using 1
    simp
  apply hquot.congr'
  filter_upwards [hcos.eventually_ne (by norm_num : (1 : ℝ)≠0)] with n hn
  dsimp only [u,e]
  simp only [real_inner_smul_left,inner_sub_left,polarPoint_inner_radial]
  rw [show vb n-(va n+vb n)/2=(vb n-va n)/2 by ring,
    show va n-(va n+vb n)/2= -((vb n-va n)/2) by ring,Real.cos_neg]
  field_simp [hn,ne_of_gt (hd n)]

end DominantFiveBody
