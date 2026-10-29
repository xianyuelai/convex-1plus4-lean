import DominantFiveBody.CollisionTripleOriginalGroups
import DominantFiveBody.CollisionTripleRectangle

/-! # The original current-mass angular group averages in Proposition 4.3 -/
noncomputable section
open scoped BigOperators ContDiff
open Filter Set Topology
namespace DominantFiveBody
set_option maxHeartbeats 1800000

theorem physical_current_group_full_angular_average
    (eps : ℝ) (mu r theta : Satellite → ℝ) (hm : PositiveRatio mu)
    (hroot : ∀ i,angularResidual eps mu r theta i=0)
    (S : Finset Satellite) (hS : S.Nonempty) (p : Satellite) (hp : p∉S) :
    satelliteGroupScalarAverage mu S (fun i => ∑ j∈Sᶜ.erase p,mu j*fullAngularMatrix eps r theta i j)+
      mu p*satelliteGroupScalarAverage mu S
        (fun i => physicalSourceFullAngularField eps (r p) (theta p) (r i) (theta i))=0 := by
  have hpin : p∈Sᶜ := Finset.mem_compl.mpr hp
  have hcut := full_angular_cut eps mu r theta hroot S
  have hsum (i : Satellite) : (∑ j∈Sᶜ,fullAngularPair eps mu r theta i j)=
      mu i*(∑ j∈Sᶜ.erase p,mu j*fullAngularMatrix eps r theta i j)+
      mu p*(mu i*physicalSourceFullAngularField eps (r p) (theta p) (r i) (theta i)) := by
    rw [← Finset.sum_erase_add _ _ hpin]
    unfold fullAngularPair
    rw [Finset.mul_sum,fullAngularMatrix_eq_physicalSourceFullAngularField]
    ring
  simp_rw [hsum] at hcut
  rw [Finset.sum_add_distrib,← Finset.mul_sum] at hcut
  have hn : (∑ i∈S,mu i)≠0 := ne_of_gt (Finset.sum_pos (fun i _ => hm.1 i) hS)
  unfold satelliteGroupScalarAverage
  field_simp [hn]
  simpa only [mul_zero] using hcut

theorem fullAngularMatrix_cross_distance_abs_bound
    (eps : ℝ) (r theta : Satellite → ℝ) (i j : Satellite)
    (heps : 0≤eps) (hri : 0<r i) (hrj : 0<r j) (hri2 : r i≤2) (hrj2 : r j≤2)
    (d eta : ℝ) (hd : 0<d) (heta : 0<eta)
    (hgap : |theta j-theta i|≤2*d)
    (hsep : eta*d≤satelliteDistance (polarSatellites r theta) i j) :
    |fullAngularMatrix eps r theta i j|≤((8/eta^3)+8*d^3)/d^2 := by
  have hdist : 0<satelliteDistance (polarSatellites r theta) i j := (mul_pos heta hd).trans_le hsep
  have hinv : (satelliteDistance (polarSatellites r theta) i j^3)⁻¹≤((eta*d)^3)⁻¹ :=
    inv_anti₀ (pow_pos (mul_pos heta hd) 3)
      (pow_le_pow_left₀ (mul_pos heta hd).le hsep 3)
  have hc0 : 0≤(1+eps)⁻¹ := by positivity
  have hc1 : (1+eps)⁻¹≤1 := by
    have h := inv_anti₀ (by norm_num : (0 : ℝ)<1) (by linarith : (1 : ℝ)≤1+eps)
    simpa only [inv_one] using h
  have hprod : r i*r j≤4 := by
    have hb := mul_le_mul hri2 hrj2 hrj.le (by norm_num : (0 : ℝ)≤2)
    norm_num at hb
    exact hb
  have hsin : |Real.sin (theta j-theta i)|≤2*d :=
    Real.abs_sin_le_abs.trans hgap
  have hpre : |r i*r j*Real.sin (theta j-theta i)|≤8*d := by
    rw [abs_mul,abs_mul,abs_of_pos hri,abs_of_pos hrj]
    have h := mul_le_mul hprod hsin (abs_nonneg _) (by norm_num : (0 : ℝ)≤4)
    convert! h using 1
    ring
  have hcoef : |(satelliteDistance (polarSatellites r theta) i j^3)⁻¹-(1+eps)⁻¹|≤((eta*d)^3)⁻¹+1 := by
    have ht := abs_sub (satelliteDistance (polarSatellites r theta) i j^3)⁻¹ (1+eps)⁻¹
    rw [abs_of_pos (inv_pos.mpr (pow_pos hdist 3)),abs_of_nonneg hc0] at ht
    linarith
  unfold fullAngularMatrix
  rw [abs_mul]
  calc
    _≤(8*d)*(((eta*d)^3)⁻¹+1) := mul_le_mul hpre hcoef (abs_nonneg _) (by positivity)
    _=((8/eta^3)+8*d^3)/d^2 := by field_simp

theorem current_group_near_angular_scaled_abs_bound
    (mu : MassRatio) (hm : PositiveRatio mu) (F : Satellite → Satellite → ℝ)
    (S : Finset Satellite) (hS : S.Nonempty) (p : Satellite)
    (d K : ℝ) (hd : 0<d) (hK : 0≤K)
    (hF : ∀ i∈S,∀ j∈Sᶜ.erase p,|F i j|≤K/d^2) :
    |satelliteGroupScalarAverage mu S (fun i => ∑ j∈Sᶜ.erase p,mu j*F i j)/d|
      ≤K*((∑ j∈Finset.univ.erase p,mu j)/d^3) := by
  have hsub : Sᶜ.erase p⊆Finset.univ.erase p := by
    intro j hj
    exact Finset.mem_erase.mpr ⟨(Finset.mem_erase.mp hj).1,Finset.mem_univ _⟩
  have hmass : (∑ j∈Sᶜ.erase p,mu j)≤∑ j∈Finset.univ.erase p,mu j :=
    Finset.sum_le_sum_of_subset_of_nonneg hsub (fun j _ _ => (hm.1 j).le)
  have havg : |satelliteGroupScalarAverage mu S (fun i => ∑ j∈Sᶜ.erase p,mu j*F i j)|≤
      (K/d^2)*(∑ j∈Finset.univ.erase p,mu j) := by
    apply satelliteGroupScalarAverage_abs_le mu S (fun i _ => hm.1 i) hS
    intro i hi
    calc
      |∑ j∈Sᶜ.erase p,mu j*F i j|≤∑ j∈Sᶜ.erase p,|mu j*F i j| := Finset.abs_sum_le_sum_abs _ _
      _≤∑ j∈Sᶜ.erase p,mu j*(K/d^2) := Finset.sum_le_sum (fun j hj => by
        rw [abs_mul,abs_of_pos (hm.1 j)]
        exact mul_le_mul_of_nonneg_left (hF i hi j hj) (hm.1 j).le)
      _=(K/d^2)*(∑ j∈Sᶜ.erase p,mu j) := by rw [← Finset.sum_mul];ring
      _≤(K/d^2)*(∑ j∈Finset.univ.erase p,mu j) := mul_le_mul_of_nonneg_left hmass (by positivity)
  rw [abs_div,abs_of_pos hd]
  have h := (div_le_div_iff_of_pos_right hd).mpr havg
  convert! h using 1
  field_simp

end DominantFiveBody
