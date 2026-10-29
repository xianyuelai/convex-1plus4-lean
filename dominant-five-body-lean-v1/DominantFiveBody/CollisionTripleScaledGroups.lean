import DominantFiveBody.CollisionScaledGroupGeometry

/-! # The original arbitrary equal-limit groups of a complete triple

The common cubic upper bound comes from the earlier source estimate.
Distinct scaled limiting groups give the cross-group distance lower bound;
neither it nor a lower bound for a current group mass is assumed.
-/

noncomputable section
open scoped BigOperators ContDiff
open Filter Set Topology
namespace DominantFiveBody
set_option maxHeartbeats 1500000

theorem physical_triple_equal_scaled_groups_primary_projection_limit
    (eps : ℕ → ℝ) (mu : ℕ → MassRatio) (q : ℕ → SatelliteConfiguration)
    (heps : Tendsto eps atTop (nhds 0)) (hm : ∀ n,PositiveRatio (mu n))
    (hroot : ∀ n i,vectorResidual (eps n) (mu n) (q n) i=0)
    (hcf : ∀ n,RelativeCollisionFree (q n))
    (q0 : SatelliteConfiguration) (hqt : Tendsto q atTop (nhds q0))
    (p : Satellite) (c : Plane) (hc : ‖c‖=1)
    (hcenter : ∀ i∈Finset.univ.erase p,q0 i=c) (hsep : q0 p≠c)
    (d : ℕ → ℝ) (hd : ∀ n,0<d n)
    (hdiam : ∀ n,∀ i∈Finset.univ.erase p,∀ j∈Finset.univ.erase p,satelliteDistance (q n) i j≤d n)
    (hbound : ∃ C : ℝ,0<C ∧ ∀ᶠ n in atTop,(∑ i∈Finset.univ.erase p,mu n i)/d n^3≤C)
    (ref : Satellite) (z : Satellite → Plane)
    (hzt : ∀ i∈Finset.univ.erase p,Tendsto (fun n => (d n)⁻¹ • (q n i-q n ref)) atTop (nhds (z i)))
    (S T : Finset Satellite) (hS : S⊆Finset.univ.erase p) (hT : T⊆Finset.univ.erase p)
    (a b : Satellite) (ha : a∈S) (hb : b∈T)
    (hclassS : ∀ i∈Finset.univ.erase p,i∈S ↔ z i=z a)
    (hclassT : ∀ i∈Finset.univ.erase p,i∈T ↔ z i=z b)
    (v : Plane) (hv : ‖v‖=1) :
    Tendsto (fun n => inner ℝ (primaryRadialField (q n a)-primaryRadialField (q n b)) v/d n)
      atTop (nhds 0) ∧
    ∃ R B : ℕ → ℝ,
      (∀ n,inner ℝ (primaryRadialField (q n a)-primaryRadialField (q n b)) v=R n+eps n*B n) ∧
      Tendsto (fun n => R n/d n) atTop (nhds 0) ∧
      ∃ C : ℝ,∀ᶠ n in atTop,|B n/d n|≤C := by
  classical
  let E : Finset Satellite := Finset.univ.erase p
  have hSnon : S.Nonempty := ⟨a,ha⟩
  have hTnon : T.Nonempty := ⟨b,hb⟩
  have hEa : a∈E := hS ha
  have hEb : b∈E := hT hb
  have hclassesS : ∀ i∈S,∀ j∈E\S,z i≠z j := by
    intro i hi j hj he
    have hiEq := (hclassS i (hS hi)).mp hi
    have hjEq : z j=z a := he.symm.trans hiEq
    exact (Finset.mem_sdiff.mp hj).2 ((hclassS j (Finset.mem_sdiff.mp hj).1).mpr hjEq)
  have hclassesT : ∀ i∈T,∀ j∈E\T,z i≠z j := by
    intro i hi j hj he
    have hiEq := (hclassT i (hT hi)).mp hi
    have hjEq : z j=z b := he.symm.trans hiEq
    exact (Finset.mem_sdiff.mp hj).2 ((hclassT j (Finset.mem_sdiff.mp hj).1).mpr hjEq)
  obtain ⟨etaS,hetaS,hcrossS⟩ := equal_scaled_class_cross_separation q d hd E S hS ref z hzt hclassesS
  obtain ⟨etaT,hetaT,hcrossT⟩ := equal_scaled_class_cross_separation q d hd E T hT ref z hzt hclassesT
  let eta := min etaS etaT
  have heta : 0<eta := lt_min hetaS hetaT
  have hnearS : Sᶜ.erase p=E\S := by
    ext i
    simp only [E,Finset.mem_erase,Finset.mem_compl,Finset.mem_sdiff,Finset.mem_univ,and_true]
  have hnearT : Tᶜ.erase p=E\T := by
    ext i
    simp only [E,Finset.mem_erase,Finset.mem_compl,Finset.mem_sdiff,Finset.mem_univ,and_true]
  have hpS : p∉S := fun hp => (Finset.mem_erase.mp (hS hp)).1 rfl
  have hpT : p∉T := fun hp => (Finset.mem_erase.mp (hT hp)).1 rfl
  obtain ⟨K,hK,hfar⟩ := finite_exterior_scaled_difference_bound q q0 hqt E ⟨a,hEa⟩ a p c
    (hcenter a hEa) hcenter hsep d hd (fun n i hi => hdiam n a hEa i hi) v hv
  obtain ⟨C,hC,hcube⟩ := hbound
  have hforceBound : ∃ B : ℝ,∀ᶠ n in atTop,
      |(satelliteGroupExteriorProjection (mu n) (q n) S v-
        satelliteGroupExteriorProjection (mu n) (q n) T v)/d n|≤B := by
    refine ⟨2*C/eta^2+2*K,?_⟩
    filter_upwards [hcrossS,hcrossT,hfar,hcube] with n hnS hnT hnFar hnCube
    apply satelliteGroupsExteriorProjection_scaled_bound (mu n) (hm n) (q n) (hcf n)
      S T hSnon hTnon p a hpS hpT v hv (d n) eta C K (hd n) heta hC hK.le
    · intro i hi j hj
      rw [hnearS] at hj
      exact (mul_le_mul_of_nonneg_right (min_le_left etaS etaT) (hd n).le).trans (hnS i hi j hj)
    · intro i hi j hj
      rw [hnearT] at hj
      exact (mul_le_mul_of_nonneg_right (min_le_right etaS etaT) (hd n).le).trans (hnT i hi j hj)
    · exact hnCube
    · intro i hi
      exact hnFar i (by rcases Finset.mem_union.mp hi with hi|hi;exact hS hi;exact hT hi)
  have hscaledS : ∀ i∈S,Tendsto (fun n => (d n)⁻¹ • (q n i-q n a)) atTop (nhds 0) := by
    intro i hi
    have ht := (hzt i (hS hi)).sub (hzt a hEa)
    rw [(hclassS i (hS hi)).mp hi,sub_self] at ht
    convert! ht using 1
    funext n
    module
  have hscaledT : ∀ i∈T,Tendsto (fun n => (d n)⁻¹ • (q n i-q n b)) atTop (nhds 0) := by
    intro i hi
    have ht := (hzt i (hT hi)).sub (hzt b hEb)
    rw [(hclassT i (hT hi)).mp hi,sub_self] at ht
    convert! ht using 1
    funext n
    module
  have hlimits : ∀ i∈S∪T,Tendsto (fun n => q n i) atTop (nhds c) := by
    intro i hi
    have hiE : i∈E := by rcases Finset.mem_union.mp hi with hi|hi;exact hS hi;exact hT hi
    simpa only [Function.comp_def,hcenter i hiE] using (continuous_apply i).continuousAt.tendsto.comp hqt
  have hlim := physical_equal_scaled_groups_primary_projection_limit eps mu q heps hm hroot hcf
    S T hSnon hTnon a b ha hb c v hc d hd hlimits hscaledS hscaledT hforceBound
  let B : ℕ → ℝ := fun n => -(satelliteGroupExteriorProjection (mu n) (q n) S v-
      satelliteGroupExteriorProjection (mu n) (q n) T v)
  let R : ℕ → ℝ := fun n => inner ℝ (primaryRadialField (q n a)-primaryRadialField (q n b)) v-eps n*B n
  obtain ⟨Cforce,hforce⟩ := hforceBound
  have hBb : IsBoundedUnder (·≤·) atTop (norm ∘ fun n => B n/d n) := by
    refine ⟨Cforce,?_⟩
    change ∀ᶠ n in atTop,‖B n/d n‖≤Cforce
    simpa only [B,Real.norm_eq_abs,neg_div,abs_neg] using hforce
  have hzero := NormedField.tendsto_zero_smul_of_tendsto_zero_of_bounded heps hBb
  refine ⟨hlim,R,B,?_,?_,Cforce,?_⟩
  · intro n;dsimp only [R];ring
  · convert! hlim.sub hzero using 1
    · funext n;dsimp only [R];simp only [smul_eq_mul,Pi.mul_apply];ring
    · simp
  · simpa only [B,neg_div,abs_neg] using hforce

theorem physical_triple_equal_scaled_groups_primary_vector_limit
    (eps : ℕ → ℝ) (mu : ℕ → MassRatio) (q : ℕ → SatelliteConfiguration)
    (heps : Tendsto eps atTop (nhds 0)) (hm : ∀ n,PositiveRatio (mu n))
    (hroot : ∀ n i,vectorResidual (eps n) (mu n) (q n) i=0)
    (hcf : ∀ n,RelativeCollisionFree (q n))
    (q0 : SatelliteConfiguration) (hqt : Tendsto q atTop (nhds q0))
    (p : Satellite) (c : Plane) (hc : ‖c‖=1)
    (hcenter : ∀ i∈Finset.univ.erase p,q0 i=c) (hsep : q0 p≠c)
    (d : ℕ → ℝ) (hd : ∀ n,0<d n)
    (hdiam : ∀ n,∀ i∈Finset.univ.erase p,∀ j∈Finset.univ.erase p,satelliteDistance (q n) i j≤d n)
    (hbound : ∃ C : ℝ,0<C ∧ ∀ᶠ n in atTop,(∑ i∈Finset.univ.erase p,mu n i)/d n^3≤C)
    (ref : Satellite) (z : Satellite → Plane)
    (hzt : ∀ i∈Finset.univ.erase p,Tendsto (fun n => (d n)⁻¹ • (q n i-q n ref)) atTop (nhds (z i)))
    (S T : Finset Satellite) (hS : S⊆Finset.univ.erase p) (hT : T⊆Finset.univ.erase p)
    (a b : Satellite) (ha : a∈S) (hb : b∈T)
    (hclassS : ∀ i∈Finset.univ.erase p,i∈S ↔ z i=z a)
    (hclassT : ∀ i∈Finset.univ.erase p,i∈T ↔ z i=z b) :
    Tendsto (fun n => (d n)⁻¹ • (primaryRadialField (q n a)-primaryRadialField (q n b)))
      atTop (nhds 0) := by
  apply plane_tendsto_zero_of_unit_projections
  intro v hv
  have ht := (physical_triple_equal_scaled_groups_primary_projection_limit eps mu q heps hm hroot hcf
    q0 hqt p c hc hcenter hsep d hd hdiam hbound ref z hzt S T hS hT a b ha hb hclassS hclassT v hv).1
  simpa only [real_inner_smul_left,div_eq_mul_inv,mul_comm] using ht

theorem physical_triple_scaled_groups_radial_projection_limit
    (eps : ℕ → ℝ) (mu : ℕ → MassRatio) (q : ℕ → SatelliteConfiguration)
    (heps : Tendsto eps atTop (nhds 0)) (hm : ∀ n,PositiveRatio (mu n))
    (hroot : ∀ n i,vectorResidual (eps n) (mu n) (q n) i=0)
    (hcf : ∀ n,RelativeCollisionFree (q n))
    (q0 : SatelliteConfiguration) (hqt : Tendsto q atTop (nhds q0))
    (p : Satellite) (c : Plane) (hc : ‖c‖=1)
    (hcenter : ∀ i∈Finset.univ.erase p,q0 i=c) (hsep : q0 p≠c)
    (d : ℕ → ℝ) (hd : ∀ n,0<d n)
    (hdiam : ∀ n,∀ i∈Finset.univ.erase p,∀ j∈Finset.univ.erase p,satelliteDistance (q n) i j≤d n)
    (hbound : ∃ C : ℝ,0<C ∧ ∀ᶠ n in atTop,(∑ i∈Finset.univ.erase p,mu n i)/d n^3≤C)
    (ref : Satellite) (z : Satellite → Plane)
    (hzt : ∀ i∈Finset.univ.erase p,Tendsto (fun n => (d n)⁻¹ • (q n i-q n ref)) atTop (nhds (z i)))
    (a b : Satellite) (ha : a∈Finset.univ.erase p) (hb : b∈Finset.univ.erase p) :
    Tendsto (fun n => inner ℝ ((d n)⁻¹ • (q n b-q n a)) c) atTop (nhds 0) := by
  classical
  let E : Finset Satellite := Finset.univ.erase p
  let S := E.filter (fun i => z i=z a)
  let T := E.filter (fun i => z i=z b)
  have hS : S⊆E := Finset.filter_subset _ _
  have hT : T⊆E := Finset.filter_subset _ _
  have haS : a∈S := Finset.mem_filter.mpr ⟨ha,rfl⟩
  have hbT : b∈T := Finset.mem_filter.mpr ⟨hb,rfl⟩
  have hclassS : ∀ i∈E,i∈S ↔ z i=z a := by intro i hi;simp only [S,Finset.mem_filter,hi,true_and]
  have hclassT : ∀ i∈E,i∈T ↔ z i=z b := by intro i hi;simp only [T,Finset.mem_filter,hi,true_and]
  have hPhi := physical_triple_equal_scaled_groups_primary_vector_limit eps mu q heps hm hroot hcf
    q0 hqt p c hc hcenter hsep d hd hdiam hbound ref z hzt S T hS hT a b haS hbT hclassS hclassT
  have hdir : Tendsto (fun n => (d n)⁻¹ • (q n b-q n a)) atTop (nhds (z b-z a)) := by
    convert! (hzt b hb).sub (hzt a ha) using 1
    funext n;module
  have hqa : Tendsto (fun n => q n a) atTop (nhds c) := by
    simpa only [Function.comp_def,hcenter a ha] using (continuous_apply a).continuousAt.tendsto.comp hqt
  have hqb : Tendsto (fun n => q n b) atTop (nhds c) := by
    simpa only [Function.comp_def,hcenter b hb] using (continuous_apply b).continuousAt.tendsto.comp hqt
  have hderiv := primaryRadialField_scaled_projection_limit (fun n => q n a) (fun n => q n b)
    d c (z b-z a) hqa hqb hd hc (fun n => (hcf n).1 a) (fun n => (hcf n).1 b) hdir
  have hzero : Tendsto (fun n => inner ℝ (primaryRadialField (q n b)-primaryRadialField (q n a)) c/d n)
      atTop (nhds 0) := by
    have ht := (hPhi.inner (𝕜 := ℝ) (tendsto_const_nhds : Tendsto (fun _ : ℕ => c) atTop (nhds c))).neg
    convert! ht using 1
    · funext n;simp only [inner_sub_left,real_inner_smul_left];ring
    · simp
  have he := tendsto_nhds_unique hderiv hzero
  have hinner : inner ℝ (z b-z a) c=0 := by linarith
  simpa only [hinner] using hdir.inner (𝕜 := ℝ)
    (tendsto_const_nhds : Tendsto (fun _ : ℕ => c) atTop (nhds c))

end DominantFiveBody
