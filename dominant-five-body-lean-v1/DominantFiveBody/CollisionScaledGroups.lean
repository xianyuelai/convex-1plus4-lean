import DominantFiveBody.CollisionNestedGeometry
import DominantFiveBody.CollisionTripleRegularScale

/-! # Arbitrary current-mass scaled groups in the source triple argument

Every average uses the current positive weights. Internal forces cancel
before division by the group mass, which may tend to zero.
-/

noncomputable section
open scoped BigOperators ContDiff
open Filter Set Topology
namespace DominantFiveBody
set_option maxHeartbeats 1500000

def satelliteGroupScalarAverage (mu : MassRatio) (S : Finset Satellite)
    (A : Satellite → ℝ) : ℝ := (∑ i∈S,mu i*A i)/(∑ i∈S,mu i)

theorem satelliteGroupScalarAverage_sub (mu : MassRatio) (S : Finset Satellite)
    (A B : Satellite → ℝ) :
    satelliteGroupScalarAverage mu S (fun i => A i-B i)=
      satelliteGroupScalarAverage mu S A-satelliteGroupScalarAverage mu S B := by
  unfold satelliteGroupScalarAverage
  simp only [mul_sub,Finset.sum_sub_distrib]
  ring

theorem satelliteGroupScalarAverage_const (mu : MassRatio) (S : Finset Satellite)
    (hm : ∀ i∈S,0<mu i) (hS : S.Nonempty) (c : ℝ) :
    satelliteGroupScalarAverage mu S (fun _ => c)=c := by
  have hn : (∑ i∈S,mu i)≠0 := ne_of_gt (Finset.sum_pos hm hS)
  unfold satelliteGroupScalarAverage
  rw [← Finset.sum_mul]
  field_simp

theorem satelliteGroupScalarAverage_abs_le (mu : MassRatio) (S : Finset Satellite)
    (hm : ∀ i∈S,0<mu i) (hS : S.Nonempty) (A : Satellite → ℝ) (C : ℝ)
    (hA : ∀ i∈S,|A i|≤C) : |satelliteGroupScalarAverage mu S A|≤C := by
  have hn := Finset.sum_pos hm hS
  unfold satelliteGroupScalarAverage
  rw [abs_div,abs_of_pos hn]
  apply (div_le_iff₀ hn).mpr
  calc
    |∑ i∈S,mu i*A i|≤∑ i∈S,|mu i*A i| := Finset.abs_sum_le_sum_abs _ _
    _≤∑ i∈S,mu i*C := Finset.sum_le_sum (fun i hi => by
      rw [abs_mul,abs_of_pos (hm i hi)]
      exact mul_le_mul_of_nonneg_left (hA i hi) (hm i hi).le)
    _=C*(∑ i∈S,mu i) := by rw [← Finset.sum_mul];ring

theorem satelliteGroupScalarAverage_difference_div (mu : MassRatio) (S : Finset Satellite)
    (hm : ∀ i∈S,0<mu i) (hS : S.Nonempty) (A : Satellite → ℝ) (c d : ℝ) :
    satelliteGroupScalarAverage mu S (fun i => (A i-c)/d)=
      (satelliteGroupScalarAverage mu S A-c)/d := by
  have hc := satelliteGroupScalarAverage_const mu S hm hS c
  have hs := satelliteGroupScalarAverage_sub mu S A (fun _ => c)
  unfold satelliteGroupScalarAverage at hc hs ⊢
  simp only [← mul_div_assoc]
  rw [← Finset.sum_div]
  rw [div_right_comm]
  rw [hs,hc]

theorem satellite_group_internal_projection_zero (mu : MassRatio)
    (q : SatelliteConfiguration) (S : Finset Satellite) (v : Plane) :
    (∑ i∈S,∑ j∈S,mu i*mu j*inner ℝ (newtonTargetField (q j) (q i)) v)=0 := by
  let A := ∑ i∈S,∑ j∈S,mu i*mu j*inner ℝ (newtonTargetField (q j) (q i)) v
  have he : A= -A := by
    dsimp only [A]
    calc
      _=∑ j∈S,∑ i∈S,mu i*mu j*inner ℝ (newtonTargetField (q j) (q i)) v := Finset.sum_comm
      _= -(∑ j∈S,∑ i∈S,mu j*mu i*inner ℝ (newtonTargetField (q i) (q j)) v) := by
        rw [← Finset.sum_neg_distrib]
        apply Finset.sum_congr rfl
        intro j _
        rw [← Finset.sum_neg_distrib]
        apply Finset.sum_congr rfl
        intro i _
        have hh := newtonTargetField_projection_reverse (q j) (q i) v
        linear_combination (mu i*mu j)*hh
  dsimp only [A] at he
  linarith

def satelliteGroupExteriorProjection (mu : MassRatio) (q : SatelliteConfiguration)
    (S : Finset Satellite) (v : Plane) : ℝ :=
  satelliteGroupScalarAverage mu S (fun i =>
    ∑ j∈Sᶜ,mu j*inner ℝ (newtonTargetField (q j) (q i)) v)

theorem physical_current_group_projection_average (eps : ℝ) (mu : MassRatio)
    (q : SatelliteConfiguration) (S : Finset Satellite) (hS : S.Nonempty)
    (hm : ∀ i,0<mu i) (hroot : ∀ i,vectorResidual eps mu q i=0) (v : Plane) :
    satelliteGroupScalarAverage mu S (fun i => inner ℝ (primaryRadialField (q i)) v)+
      eps*satelliteGroupExteriorProjection mu q S v-eps*inner ℝ (relativeField mu q) v=0 := by
  have hrows (i : Satellite) : inner ℝ (primaryRadialField (q i)) v+
      eps*inner ℝ (satelliteInteraction mu q i) v-eps*inner ℝ (relativeField mu q) v=0 := by
    have he := congrArg (fun z : Plane => inner ℝ z v) (hroot i)
    change inner ℝ (primaryRadialField (q i)+eps • satelliteInteraction mu q i-
      eps • relativeField mu q) v=inner ℝ 0 v at he
    simpa only [inner_add_left,inner_sub_left,real_inner_smul_left,inner_zero_left] using he
  have he : (∑ i∈S,mu i*(inner ℝ (primaryRadialField (q i)) v+
      eps*inner ℝ (satelliteInteraction mu q i) v-eps*inner ℝ (relativeField mu q) v))=0 := by
    simp only [hrows,mul_zero,Finset.sum_const_zero]
  simp_rw [satelliteInteraction_projection_sum_newton,
    ← Finset.sum_add_sum_compl S (fun j => mu j*inner ℝ (newtonTargetField (q j) (q _)) v)] at he
  simp only [mul_sub,mul_add,Finset.sum_sub_distrib,Finset.sum_add_distrib] at he
  have hinside : (∑ i∈S,mu i*(∑ j∈S,mu j*inner ℝ (newtonTargetField (q j) (q i)) v))=0 := by
    simp_rw [Finset.mul_sum,← mul_assoc]
    exact satellite_group_internal_projection_zero mu q S v
  have he' : (∑ i∈S,mu i*inner ℝ (primaryRadialField (q i)) v)+
      eps*(∑ i∈S,mu i*(∑ j∈Sᶜ,mu j*inner ℝ (newtonTargetField (q j) (q i)) v))-
      eps*(∑ i∈S,mu i)*inner ℝ (relativeField mu q) v=0 := by
    simp_rw [show ∀ i,mu i*(eps*(∑ j∈S,mu j*inner ℝ (newtonTargetField (q j) (q i)) v))=
      eps*(mu i*(∑ j∈S,mu j*inner ℝ (newtonTargetField (q j) (q i)) v)) by intro i;ring,
      show ∀ i,mu i*(eps*(∑ j∈Sᶜ,mu j*inner ℝ (newtonTargetField (q j) (q i)) v))=
      eps*(mu i*(∑ j∈Sᶜ,mu j*inner ℝ (newtonTargetField (q j) (q i)) v)) by intro i;ring,
      ← Finset.mul_sum] at he
    rw [hinside,mul_zero,zero_add] at he
    convert he using 1
    rw [← Finset.sum_mul]
    congr 1
    ring
  have hn := ne_of_gt (Finset.sum_pos (fun i (_ : i∈S) => hm i) hS)
  unfold satelliteGroupExteriorProjection satelliteGroupScalarAverage
  field_simp [hn]
  linear_combination he'

theorem physical_two_current_groups_projection_difference (eps : ℝ) (mu : MassRatio)
    (q : SatelliteConfiguration) (S T : Finset Satellite) (hS : S.Nonempty) (hT : T.Nonempty)
    (hm : ∀ i,0<mu i) (hroot : ∀ i,vectorResidual eps mu q i=0) (v : Plane) :
    satelliteGroupScalarAverage mu S (fun i => inner ℝ (primaryRadialField (q i)) v)-
      satelliteGroupScalarAverage mu T (fun i => inner ℝ (primaryRadialField (q i)) v)+
      eps*(satelliteGroupExteriorProjection mu q S v-satelliteGroupExteriorProjection mu q T v)=0 := by
  have h1 := physical_current_group_projection_average eps mu q S hS hm hroot v
  have h2 := physical_current_group_projection_average eps mu q T hT hm hroot v
  linarith

theorem primaryRadialField_small_scaled_projection
    (qa qb : ℕ → Plane) (d : ℕ → ℝ) (c v : Plane)
    (ha : Tendsto qa atTop (nhds c)) (hb : Tendsto qb atTop (nhds c))
    (hd : ∀ n,0<d n) (hc : ‖c‖=1)
    (hqa : ∀ n,qa n≠0) (hqb : ∀ n,qb n≠0)
    (hdir : Tendsto (fun n => (d n)⁻¹ • (qb n-qa n)) atTop (nhds 0)) :
    Tendsto (fun n => inner ℝ (primaryRadialField (qb n)-primaryRadialField (qa n)) v/d n)
      atTop (nhds 0) := by
  have hc0 : c≠0 := by intro he; simp [he] at hc
  have hN := newtonTargetField_scaled_projection_limit (fun _ => 0) qa qb d 0 c 0 v
    tendsto_const_nhds ha hb hd hdir hc0.symm (fun n => (hqa n).symm) (fun n => (hqb n).symm)
  have hV := hdir.inner (𝕜 := ℝ) (tendsto_const_nhds : Tendsto (fun _ : ℕ => v) atTop (nhds v))
  have ht := hV.add hN
  convert! ht using 1
  · funext n
    rw [primaryRadialField_eq_newton,primaryRadialField_eq_newton]
    simp only [inner_add_left,inner_sub_left,real_inner_smul_left]
    ring
  · simp [dividedNewtonTargetField,dividedInverseCube]

theorem physical_equal_scaled_groups_primary_projection_limit
    (eps : ℕ → ℝ) (mu : ℕ → MassRatio) (q : ℕ → SatelliteConfiguration)
    (heps : Tendsto eps atTop (nhds 0)) (hm : ∀ n,PositiveRatio (mu n))
    (hroot : ∀ n i,vectorResidual (eps n) (mu n) (q n) i=0)
    (hcf : ∀ n,RelativeCollisionFree (q n))
    (S T : Finset Satellite) (hS : S.Nonempty) (hT : T.Nonempty)
    (a b : Satellite) (ha : a∈S) (hb : b∈T)
    (c v : Plane) (hc : ‖c‖=1) (d : ℕ → ℝ) (hd : ∀ n,0<d n)
    (hqt : ∀ i∈S∪T,Tendsto (fun n => q n i) atTop (nhds c))
    (hscaledS : ∀ i∈S,Tendsto (fun n => (d n)⁻¹ • (q n i-q n a)) atTop (nhds 0))
    (hscaledT : ∀ i∈T,Tendsto (fun n => (d n)⁻¹ • (q n i-q n b)) atTop (nhds 0))
    (hbound : ∃ C : ℝ,∀ᶠ n in atTop,
      |(satelliteGroupExteriorProjection (mu n) (q n) S v-
        satelliteGroupExteriorProjection (mu n) (q n) T v)/d n|≤C) :
    Tendsto (fun n => inner ℝ (primaryRadialField (q n a)-primaryRadialField (q n b)) v/d n)
      atTop (nhds 0) := by
  have hbaseS := hqt a (Finset.mem_union_left T ha)
  have hbaseT := hqt b (Finset.mem_union_right S hb)
  have hsmallS : ∀ i∈S,Tendsto (fun n =>
      inner ℝ (primaryRadialField (q n i)-primaryRadialField (q n a)) v/d n) atTop (nhds 0) := by
    intro i hi
    exact primaryRadialField_small_scaled_projection (fun n => q n a) (fun n => q n i) d c v
      hbaseS (hqt i (Finset.mem_union_left T hi)) hd hc
      (fun n => (hcf n).1 a) (fun n => (hcf n).1 i) (hscaledS i hi)
  have hsmallT : ∀ i∈T,Tendsto (fun n =>
      inner ℝ (primaryRadialField (q n i)-primaryRadialField (q n b)) v/d n) atTop (nhds 0) := by
    intro i hi
    exact primaryRadialField_small_scaled_projection (fun n => q n b) (fun n => q n i) d c v
      hbaseT (hqt i (Finset.mem_union_right S hi)) hd hc
      (fun n => (hcf n).1 b) (fun n => (hcf n).1 i) (hscaledT i hi)
  have hES := current_positive_finset_weighted_average_tendsto S hS mu
    (fun n i => inner ℝ (primaryRadialField (q n i)-primaryRadialField (q n a)) v/d n) 0
    (fun n i _ => (hm n).1 i) hsmallS
  have hET := current_positive_finset_weighted_average_tendsto T hT mu
    (fun n i => inner ℝ (primaryRadialField (q n i)-primaryRadialField (q n b)) v/d n) 0
    (fun n i _ => (hm n).1 i) hsmallT
  obtain ⟨C,hC⟩ := hbound
  have hB : IsBoundedUnder (·≤·) atTop (norm ∘ fun n =>
      (satelliteGroupExteriorProjection (mu n) (q n) S v-
        satelliteGroupExteriorProjection (mu n) (q n) T v)/d n) := by
    refine ⟨C,?_⟩
    change ∀ᶠ n in atTop,‖(satelliteGroupExteriorProjection (mu n) (q n) S v-
      satelliteGroupExteriorProjection (mu n) (q n) T v)/d n‖≤C
    simpa only [Function.comp_def,Real.norm_eq_abs] using hC
  have hzero := NormedField.tendsto_zero_smul_of_tendsto_zero_of_bounded heps hB
  have ht := (hES.neg.add hET).sub hzero
  convert! ht using 1
  · funext n
    change inner ℝ (primaryRadialField (q n a)-primaryRadialField (q n b)) v/d n=
      -satelliteGroupScalarAverage (mu n) S
        (fun i => inner ℝ (primaryRadialField (q n i)-primaryRadialField (q n a)) v/d n)+
      satelliteGroupScalarAverage (mu n) T
        (fun i => inner ℝ (primaryRadialField (q n i)-primaryRadialField (q n b)) v/d n)-
      eps n*((satelliteGroupExteriorProjection (mu n) (q n) S v-
        satelliteGroupExteriorProjection (mu n) (q n) T v)/d n)
    simp only [inner_sub_left]
    rw [satelliteGroupScalarAverage_difference_div _ _ (fun i _ => (hm n).1 i) hS,
      satelliteGroupScalarAverage_difference_div _ _ (fun i _ => (hm n).1 i) hT]
    have he := physical_two_current_groups_projection_difference (eps n) (mu n) (q n) S T hS hT
      (hm n).1 (hroot n) v
    field_simp [ne_of_gt (hd n)]
    linear_combination he
  · simp

theorem plane_tendsto_zero_of_unit_projections (f : ℕ → Plane)
    (h : ∀ v : Plane,‖v‖=1 → Tendsto (fun n => inner ℝ (f n) v) atTop (nhds 0)) :
    Tendsto f atTop (nhds 0) := by
  let e : Fin 2 → Plane := fun i => if i=0 then point 1 0 else point 0 1
  have hnorm (i : Fin 2) : ‖e i‖=1 := by
    have hs : ‖e i‖^2=1 := by
      rw [EuclideanSpace.real_norm_sq_eq,Fin.sum_univ_two]
      fin_cases i <;> simp [e,point]
    nlinarith [norm_nonneg (e i)]
  have hinner (i : Fin 2) (z : Plane) : inner ℝ z (e i)=z i := by
    fin_cases i <;> simp [e,plane_inner_coordinates,point]
  have hpi : Tendsto (fun n i => f n i) atTop (nhds (0 : Fin 2 → ℝ)) := by
    apply tendsto_pi_nhds.mpr
    intro i
    simpa only [hinner,Pi.zero_apply] using h (e i) (hnorm i)
  have ht := (PiLp.continuous_toLp (p := 2) (β := fun _ : Fin 2 => ℝ)).continuousAt.tendsto.comp hpi
  exact ht

end DominantFiveBody
