import DominantFiveBody.CollisionScaledGroups

/-! # Current-mass cross-group forces: the original O(nu / d^2) bound -/

noncomputable section
open scoped BigOperators ContDiff
open Filter Set Topology
namespace DominantFiveBody
set_option maxHeartbeats 1500000

theorem satelliteGroupExteriorProjection_split (mu : MassRatio) (q : SatelliteConfiguration)
    (S : Finset Satellite) (p : Satellite) (hp : p∉S) (v : Plane) :
    satelliteGroupExteriorProjection mu q S v=
      satelliteGroupScalarAverage mu S (fun i => ∑ j∈Sᶜ.erase p,
        mu j*inner ℝ (newtonTargetField (q j) (q i)) v)+
      mu p*satelliteGroupScalarAverage mu S (fun i => inner ℝ (newtonTargetField (q p) (q i)) v) := by
  have hpin : p∈Sᶜ := Finset.mem_compl.mpr hp
  unfold satelliteGroupExteriorProjection satelliteGroupScalarAverage
  simp_rw [← Finset.sum_erase_add _ _ hpin,mul_add,Finset.sum_add_distrib]
  simp_rw [show ∀ i,mu i*(mu p*inner ℝ (newtonTargetField (q p) (q i)) v)=
    mu p*(mu i*inner ℝ (newtonTargetField (q p) (q i)) v) by intro i;ring,
    ← Finset.mul_sum]
  ring

theorem satelliteGroupNearProjection_abs_bound (mu : MassRatio) (hm : PositiveRatio mu)
    (q : SatelliteConfiguration) (hcf : RelativeCollisionFree q)
    (S : Finset Satellite) (hS : S.Nonempty) (p : Satellite) (v : Plane) (hv : ‖v‖=1)
    (d eta C : ℝ) (hd : 0<d) (heta : 0<eta) (hC : 0<C)
    (hsep : ∀ i∈S,∀ j∈Sᶜ.erase p,eta*d≤satelliteDistance q j i)
    (hnu : (∑ j∈Finset.univ.erase p,mu j)/d^3≤C) :
    |satelliteGroupScalarAverage mu S (fun i => ∑ j∈Sᶜ.erase p,
      mu j*inner ℝ (newtonTargetField (q j) (q i)) v)|≤(C/eta^2)*d := by
  apply satelliteGroupScalarAverage_abs_le mu S (fun i _ => hm.1 i) hS
  intro i hi
  have hEach (j : Satellite) (hj : j∈Sᶜ.erase p) :
      |inner ℝ (newtonTargetField (q j) (q i)) v|≤1/(eta*d)^2 := by
    have hji : j≠i := by
      intro he
      have hnot : j∉S := Finset.mem_compl.mp (Finset.mem_erase.mp hj).2
      exact hnot (he.symm ▸ hi)
    calc
      |inner ℝ (newtonTargetField (q j) (q i)) v|≤‖newtonTargetField (q j) (q i)‖*‖v‖ := abs_real_inner_le_norm _ _
      _=1/(satelliteDistance q j i)^2 := by rw [hv,mul_one,newtonTargetField_norm _ _ (hcf.2 j i hji)];rfl
      _≤1/(eta*d)^2 := one_div_le_one_div_of_le (sq_pos_of_pos (mul_pos heta hd))
        (pow_le_pow_left₀ (mul_pos heta hd).le (hsep i hi j hj) 2)
  have hsub : Sᶜ.erase p⊆Finset.univ.erase p := by
    intro j hj
    exact Finset.mem_erase.mpr ⟨(Finset.mem_erase.mp hj).1,Finset.mem_univ j⟩
  have hmass : (∑ j∈Sᶜ.erase p,mu j)≤∑ j∈Finset.univ.erase p,mu j :=
    Finset.sum_le_sum_of_subset_of_nonneg hsub (fun j _ _ => (hm.1 j).le)
  have htotal : (∑ j∈Finset.univ.erase p,mu j)≤C*d^3 :=
    (div_le_iff₀ (pow_pos hd 3)).mp hnu
  calc
    |∑ j∈Sᶜ.erase p,mu j*inner ℝ (newtonTargetField (q j) (q i)) v|
        ≤∑ j∈Sᶜ.erase p,|mu j*inner ℝ (newtonTargetField (q j) (q i)) v| := Finset.abs_sum_le_sum_abs _ _
    _≤∑ j∈Sᶜ.erase p,mu j*(1/(eta*d)^2) := Finset.sum_le_sum (fun j hj => by
      rw [abs_mul,abs_of_pos (hm.1 j)]
      exact mul_le_mul_of_nonneg_left (hEach j hj) (hm.1 j).le)
    _=(∑ j∈Sᶜ.erase p,mu j)*(1/(eta*d)^2) := (Finset.sum_mul ..).symm
    _≤(C*d^3)*(1/(eta*d)^2) := mul_le_mul_of_nonneg_right (hmass.trans htotal) (by positivity)
    _=(C/eta^2)*d := by field_simp

theorem satelliteGroupsExteriorProjection_scaled_bound (mu : MassRatio) (hm : PositiveRatio mu)
    (q : SatelliteConfiguration) (hcf : RelativeCollisionFree q)
    (S T : Finset Satellite) (hS : S.Nonempty) (hT : T.Nonempty)
    (p ref : Satellite) (hpS : p∉S) (hpT : p∉T) (v : Plane) (hv : ‖v‖=1)
    (d eta C K : ℝ) (hd : 0<d) (heta : 0<eta) (hC : 0<C) (hK : 0≤K)
    (hsepS : ∀ i∈S,∀ j∈Sᶜ.erase p,eta*d≤satelliteDistance q j i)
    (hsepT : ∀ i∈T,∀ j∈Tᶜ.erase p,eta*d≤satelliteDistance q j i)
    (hnu : (∑ j∈Finset.univ.erase p,mu j)/d^3≤C)
    (hfar : ∀ i∈S∪T,|inner ℝ (newtonTargetField (q p) (q i)-newtonTargetField (q p) (q ref)) v|≤K*d) :
    |(satelliteGroupExteriorProjection mu q S v-satelliteGroupExteriorProjection mu q T v)/d|
      ≤2*C/eta^2+2*K := by
  have hnearS := satelliteGroupNearProjection_abs_bound mu hm q hcf S hS p v hv d eta C hd heta hC hsepS hnu
  have hnearT := satelliteGroupNearProjection_abs_bound mu hm q hcf T hT p v hv d eta C hd heta hC hsepT hnu
  let A := fun i => inner ℝ (newtonTargetField (q p) (q i)) v
  have hfarS : |satelliteGroupScalarAverage mu S A-A ref|≤K*d := by
    rw [← satelliteGroupScalarAverage_const mu S (fun i _ => hm.1 i) hS (A ref),
      ← satelliteGroupScalarAverage_sub]
    apply satelliteGroupScalarAverage_abs_le mu S (fun i _ => hm.1 i) hS
    intro i hi
    simpa only [A,inner_sub_left] using hfar i (Finset.mem_union_left T hi)
  have hfarT : |satelliteGroupScalarAverage mu T A-A ref|≤K*d := by
    rw [← satelliteGroupScalarAverage_const mu T (fun i _ => hm.1 i) hT (A ref),
      ← satelliteGroupScalarAverage_sub]
    apply satelliteGroupScalarAverage_abs_le mu T (fun i _ => hm.1 i) hT
    intro i hi
    simpa only [A,inner_sub_left] using hfar i (Finset.mem_union_right S hi)
  have hfarDiff : |satelliteGroupScalarAverage mu S A-satelliteGroupScalarAverage mu T A|≤2*K*d := by
    have ht := abs_add_le (satelliteGroupScalarAverage mu S A-A ref)
      (A ref-satelliteGroupScalarAverage mu T A)
    rw [abs_sub_comm (A ref)] at ht
    have he : satelliteGroupScalarAverage mu S A-A ref+
      (A ref-satelliteGroupScalarAverage mu T A)=
      satelliteGroupScalarAverage mu S A-satelliteGroupScalarAverage mu T A := by ring
    rw [he] at ht
    linarith
  rw [satelliteGroupExteriorProjection_split _ _ _ p hpS,
    satelliteGroupExteriorProjection_split _ _ _ p hpT,abs_div,abs_of_pos hd]
  apply (div_le_iff₀ hd).mpr
  have hmp := PositiveRatio.coordinate_le_one mu hm p
  have hpnonneg := (hm.1 p).le
  have htriangle := abs_add_le
    (satelliteGroupScalarAverage mu S (fun i => ∑ j∈Sᶜ.erase p,mu j*inner ℝ (newtonTargetField (q j) (q i)) v)-
      satelliteGroupScalarAverage mu T (fun i => ∑ j∈Tᶜ.erase p,mu j*inner ℝ (newtonTargetField (q j) (q i)) v))
    (mu p*(satelliteGroupScalarAverage mu S A-satelliteGroupScalarAverage mu T A))
  have hnearDiff := abs_sub
    (satelliteGroupScalarAverage mu S (fun i => ∑ j∈Sᶜ.erase p,mu j*inner ℝ (newtonTargetField (q j) (q i)) v))
    (satelliteGroupScalarAverage mu T (fun i => ∑ j∈Tᶜ.erase p,mu j*inner ℝ (newtonTargetField (q j) (q i)) v))
  have hweighted := mul_le_mul_of_nonneg_left hfarDiff hpnonneg
  have hweighted2 := mul_le_mul_of_nonneg_right hmp (by positivity : 0≤2*K*d)
  rw [abs_mul,abs_of_pos (hm.1 p)] at htriangle
  have halgebra : ∀ X Y Z W : ℝ,X+mu p*Z-(Y+mu p*W)=(X-Y)+mu p*(Z-W) := by intros;ring
  rw [halgebra]
  change _≤(2*C/eta^2+2*K)*d
  dsimp only [A] at htriangle hweighted
  rw [show (2*C/eta^2+2*K)*d=2*(C/eta^2*d)+2*K*d by ring]
  linarith [htriangle,hnearDiff,hweighted,hweighted2]

end DominantFiveBody
