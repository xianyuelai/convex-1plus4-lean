import DominantFiveBody.CollisionNestedRectangleGeometry

/-! # Genuine operator-norm bounds for the physical pair exterior field -/
noncomputable section
open scoped BigOperators ContDiff
open Filter Set Topology
namespace DominantFiveBody
set_option maxHeartbeats 1500000

theorem newtonTargetDerivative_operator_norm_bound (source target : Plane) (hsep : source≠target) :
    ‖newtonTargetDerivative source target‖≤4/‖source-target‖^3 := by
  let R := ‖source-target‖
  have hR : 0<R := norm_pos_iff.mpr (sub_ne_zero.mpr hsep)
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  intro v
  rw [newtonTargetDerivative_apply]
  calc
    _≤‖(3/‖source-target‖^5*inner ℝ (source-target) v) • (source-target)‖+
      ‖(‖source-target‖^3)⁻¹ • v‖ := norm_sub_le _ _
    _=(3/R^5)*|inner ℝ (source-target) v| *R+(R^3)⁻¹*‖v‖ := by
      rw [norm_smul,norm_smul,Real.norm_eq_abs,Real.norm_eq_abs,abs_mul,
        abs_of_pos (div_pos (by norm_num : (0 : ℝ)<3) (pow_pos hR 5)),
        abs_of_pos (inv_pos.mpr (pow_pos hR 3))]
    _≤(3/R^5)*(R*‖v‖)*R+(R^3)⁻¹*‖v‖ := by
      have hi : |inner ℝ (source-target) v|≤R*‖v‖ := abs_real_inner_le_norm (source-target) v
      have hp : 0≤3/R^5 := by positivity
      exact add_le_add (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hi hp) hR.le) le_rfl
    _=(4/‖source-target‖^3)*‖v‖ := by change _=(4/R^3)*‖v‖;field_simp;norm_num

theorem pairExteriorField_hasFDerivAt (mu : MassRatio) (q : SatelliteConfiguration)
    (a b : Satellite) (y : Plane) (hsep : ∀ j∈pairExteriorLabels a b,q j≠y) :
    HasFDerivAt (pairExteriorField mu q a b)
      (∑ j∈pairExteriorLabels a b,mu j • newtonTargetDerivative (q j) y) y := by
  have ht := HasFDerivAt.fun_sum (u := pairExteriorLabels a b) (fun j hj =>
    (newtonTargetField_hasFDerivAt (q j) y (hsep j hj)).const_smul (mu j))
  convert! ht using 1
  funext t
  exact pairExteriorField_eq_newton_sum mu q a b t

theorem pairExteriorField_fderiv_norm_bound (mu : MassRatio) (q : SatelliteConfiguration)
    (a b : Satellite) (y : Plane) (hm : ∀ j∈pairExteriorLabels a b,0≤mu j)
    (hsep : ∀ j∈pairExteriorLabels a b,q j≠y) :
    ‖fderiv ℝ (pairExteriorField mu q a b) y‖≤
      ∑ j∈pairExteriorLabels a b,mu j*(4/‖q j-y‖^3) := by
  rw [(pairExteriorField_hasFDerivAt mu q a b y hsep).fderiv]
  calc
    _≤∑ j∈pairExteriorLabels a b,‖mu j • newtonTargetDerivative (q j) y‖ := norm_sum_le _ _
    _≤∑ j∈pairExteriorLabels a b,mu j*(4/‖q j-y‖^3) := Finset.sum_le_sum (fun j hj => by
      rw [norm_smul,Real.norm_eq_abs,abs_of_nonneg (hm j hj)]
      exact mul_le_mul_of_nonneg_left (newtonTargetDerivative_operator_norm_bound _ _ (hsep j hj)) (hm j hj))

theorem pairExteriorField_fderiv_norm_bound_two_sources
    (mu : MassRatio) (hm : PositiveRatio mu) (q : SatelliteConfiguration)
    (a b c p : Satellite) (hab : a≠b) (hcp : c≠p)
    (hc : c∈pairExteriorLabels a b) (hp : p∈pairExteriorLabels a b)
    (y : Plane) (d C : ℝ) (hd : 0<d) (_hC : 0<C)
    (hnear : d/2≤‖q c-y‖) (hfar : (1/2 : ℝ)≤‖q p-y‖)
    (hmc : mu c/d^3≤C) :
    ‖fderiv ℝ (pairExteriorField mu q a b) y‖≤32*(C+1) := by
  have hnearPos : 0<‖q c-y‖ := (half_pos hd).trans_le hnear
  have hfarPos : 0<‖q p-y‖ := lt_of_lt_of_le (by norm_num : (0 : ℝ)<1/2) hfar
  have hsep : ∀ j∈pairExteriorLabels a b,q j≠y := by
    rw [pairExteriorLabels_eq_two a b c p hab hc hp hcp]
    intro j hj
    have hj' : j=c ∨ j=p := by simpa only [Finset.mem_insert,Finset.mem_singleton] using hj
    rcases hj' with rfl|rfl
    · exact sub_ne_zero.mp (norm_pos_iff.mp hnearPos)
    · exact sub_ne_zero.mp (norm_pos_iff.mp hfarPos)
  have hb := pairExteriorField_fderiv_norm_bound mu q a b y (fun j _ => (hm.1 j).le) hsep
  rw [pairExteriorLabels_eq_two a b c p hab hc hp hcp,Finset.sum_pair hcp] at hb
  have hn : 4/‖q c-y‖^3≤4/(d/2)^3 :=
    div_le_div_of_nonneg_left (by norm_num) (pow_pos (half_pos hd) 3)
      (pow_le_pow_left₀ (half_pos hd).le hnear 3)
  have hf : 4/‖q p-y‖^3≤32 := by
    have ht := div_le_div_of_nonneg_left (by norm_num : (0 : ℝ)≤4)
      (by norm_num : (0 : ℝ)<(1/2)^3) (pow_le_pow_left₀ (by norm_num : (0 : ℝ)≤1/2) hfar 3)
    norm_num at ht
    exact ht
  have hnearBound : mu c*(4/‖q c-y‖^3)≤32*C := by
    have hh := mul_le_mul_of_nonneg_left hn (hm.1 c).le
    have he : mu c*(4/(d/2)^3)=32*(mu c/d^3) := by field_simp;ring
    rw [he] at hh
    exact hh.trans (mul_le_mul_of_nonneg_left hmc (by norm_num))
  have hfarBound : mu p*(4/‖q p-y‖^3)≤32 := by
    have h1 := mul_le_mul_of_nonneg_left hf (hm.1 p).le
    have h2 := mul_le_mul_of_nonneg_right (PositiveRatio.coordinate_le_one mu hm p) (by norm_num : (0 : ℝ)≤32)
    exact h1.trans (by simpa only [one_mul] using h2)
  linarith

end DominantFiveBody
