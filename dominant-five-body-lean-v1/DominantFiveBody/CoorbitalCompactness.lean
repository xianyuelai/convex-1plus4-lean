import DominantFiveBody.CoorbitalHessian
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Topology.Algebra.Order.Field

/-! # Actual root bounds for the mass projection in Theorem 2.2

The collision blowup and weighted virial identity below are derived from the
physical kernel and root equations. No properness or no-collision conclusion
is used as an input.
-/

noncomputable section
open scoped BigOperators
open Filter Set Topology

namespace DominantFiveBody
set_option maxHeartbeats 800000
open Coorbital

theorem sin_div_tendsto_one_right :
    Tendsto (fun t : ℝ => Real.sin t/t) (𝓝[>] 0) (𝓝 1) := by
  simpa only [zero_add, Real.sin_zero, sub_zero, Real.cos_zero, smul_eq_mul,
    inv_mul_eq_div] using (Real.hasDerivAt_sin 0).tendsto_slope_zero_right

theorem chord_div_tendsto_one_right :
    Tendsto (fun t : ℝ => (2*Real.sin (t/2))/t) (𝓝[>] 0) (𝓝 1) := by
  have hd : HasDerivAt (fun t : ℝ => 2*Real.sin (t/2)) 1 0 := by
    convert! ((Real.hasDerivAt_sin (0/2 : ℝ)).comp (0 : ℝ) ((hasDerivAt_id (0 : ℝ)).div_const (2 : ℝ))).const_mul (2 : ℝ)
      using 1; norm_num
  simpa only [zero_add, zero_div, Real.sin_zero, mul_zero, sub_zero,
    smul_eq_mul, inv_mul_eq_div] using hd.tendsto_slope_zero_right

/-- The leading coefficient of the singular physical kernel is one. -/
theorem kernelF_scaled_tendsto_one :
    Tendsto (fun t : ℝ => t^2*kernelF t) (𝓝[>] 0) (𝓝 1) := by
  have hid : Tendsto (fun t : ℝ => t) (𝓝[>] 0) (𝓝 0) := tendsto_nhdsWithin_of_tendsto_nhds
    (by exact tendsto_id)
  have hsin : Tendsto Real.sin (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    simpa only [Real.sin_zero] using (Real.continuous_sin.tendsto (0 : ℝ)).mono_left nhdsWithin_le_nhds
  have H := (sin_div_tendsto_one_right.mul
    ((chord_div_tendsto_one_right.inv₀ (by norm_num : (1 : ℝ) ≠ 0)).pow 3)).sub
      ((hid.pow 2).mul hsin)
  norm_num at H
  apply H.congr'
  filter_upwards [self_mem_nhdsWithin] with t ht
  have hne : t ≠ 0 := ne_of_gt (show 0<t from ht)
  unfold kernelF
  simp only [div_eq_mul_inv]
  field_simp [hne]

/-- The collision exclusion input `t f(t) → +∞` used in Theorem 2.2. -/
theorem kernelF_angle_mul_tendsto_atTop :
    Tendsto (fun t : ℝ => t*kernelF t) (𝓝[>] 0) atTop := by
  have H := tendsto_inv_nhdsGT_zero.atTop_mul_pos (by norm_num : (0 : ℝ)<1)
    kernelF_scaled_tendsto_one
  apply H.congr'
  filter_upwards [self_mem_nhdsWithin] with t ht
  have hne : t ≠ 0 := ne_of_gt (show 0<t from ht)
  field_simp [hne]

def coorbitalVirial (mass theta : Satellite → ℝ) : ℝ :=
  ∑ i, ∑ j, if i<j then mass i*mass j*(theta j-theta i)*kernelF (theta j-theta i) else 0

theorem coorbitalVirial_zero (mass theta : Satellite → ℝ)
    (harc : OrderedSemicircle theta) (hroot : ∀ i, angularEquation mass theta i=0) :
    coorbitalVirial mass theta=0 := by
  obtain ⟨h0,h1,h2⟩ := four_flow_balance mass theta hroot
  have heq :
      angularFlow mass theta 0 1*(theta 1-theta 0) +
      angularFlow mass theta 0 2*(theta 2-theta 0) +
      angularFlow mass theta 0 3*(theta 3-theta 0) +
      angularFlow mass theta 1 2*(theta 2-theta 1) +
      angularFlow mass theta 1 3*(theta 3-theta 1) +
      angularFlow mass theta 2 3*(theta 3-theta 2)=0 := by
    linear_combination (theta 3-theta 0)*h0 + (theta 3-theta 1)*h1 + (theta 3-theta 2)*h2
  simp only [coorbitalVirial, Fin.sum_univ_four, Fin.reduceLT, if_true, if_false,
    zero_add, add_zero]
  rw [angularFlow_positive_formula mass theta 0 1 (harc 0 1 (by decide)).1,
    angularFlow_positive_formula mass theta 0 2 (harc 0 2 (by decide)).1,
    angularFlow_positive_formula mass theta 0 3 (harc 0 3 (by decide)).1,
    angularFlow_positive_formula mass theta 1 2 (harc 1 2 (by decide)).1,
    angularFlow_positive_formula mass theta 1 3 (harc 1 3 (by decide)).1,
    angularFlow_positive_formula mass theta 2 3 (harc 2 3 (by decide)).1] at heq
  convert heq using 1; ring

def satelliteMassPairSum (mass : Satellite → ℝ) : ℝ :=
  ∑ i, ∑ j, if i<j then mass i*mass j else 0

theorem satelliteMassPairSum_le_half (mass : Satellite → ℝ) (hsum : ∑ i, mass i=1) :
    satelliteMassPairSum mass ≤ 1/2 := by
  simp only [satelliteMassPairSum, Fin.sum_univ_four, Fin.reduceLT, if_true, if_false,
    zero_add, add_zero]
  simp only [Fin.sum_univ_four] at hsum
  nlinarith [sq_nonneg (mass 0), sq_nonneg (mass 1), sq_nonneg (mass 2), sq_nonneg (mass 3)]

/-- The manuscript's precise bound on each weighted pair term, rather than
an assumed compactness of the zero set. -/
theorem coorbitalVirial_pair_le_pi_div_two (mass theta : Satellite → ℝ)
    (hm : PositiveRatio mass) (harc : OrderedSemicircle theta)
    (hroot : ∀ i, angularEquation mass theta i=0)
    (i j : Satellite) (hij : i<j) :
    mass i*mass j*((theta j-theta i)*kernelF (theta j-theta i)) ≤ Real.pi/2 := by
  let g : Satellite → Satellite → ℝ := fun a b => if a<b then
    mass a*mass b*((theta b-theta a)*kernelF (theta b-theta a)+Real.pi) else 0
  have hg : ∀ a b, 0 ≤ g a b := by
    intro a b
    dsimp [g]
    split_ifs with hab
    · obtain ⟨ht,htpi⟩ := harc a b hab
      have hk := mul_le_mul_of_nonneg_left (kernelF_ge_neg_one ht htpi) ht.le
      apply mul_nonneg (mul_pos (hm.1 a) (hm.1 b)).le
      linarith
    · exact le_refl 0
  have heq : (∑ a, ∑ b, g a b) = coorbitalVirial mass theta +
      Real.pi*satelliteMassPairSum mass := by
    unfold coorbitalVirial satelliteMassPairSum
    simp_rw [Finset.mul_sum]
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro a _
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro b _
    dsimp [g]
    split_ifs <;> ring
  have hsum : (∑ a, ∑ b, g a b) ≤ Real.pi/2 := by
    rw [heq, coorbitalVirial_zero mass theta harc hroot, zero_add]
    simpa only [mul_one_div] using mul_le_mul_of_nonneg_left
      (satelliteMassPairSum_le_half mass hm.2) Real.pi_pos.le
  have hrow : (∑ b, g i b) ≤ ∑ a, ∑ b, g a b :=
    Finset.single_le_sum (fun a _ => Finset.sum_nonneg (fun b _ => hg a b))
    (Finset.mem_univ i)
  have hentry : g i j ≤ ∑ b, g i b :=
    Finset.single_le_sum (fun b _ => hg i b) (Finset.mem_univ j)
  have hterm := le_trans hentry (le_trans hrow hsum)
  simp only [g, if_pos hij] at hterm
  have hmasspi : 0 ≤ mass i*mass j*Real.pi := mul_nonneg (mul_pos (hm.1 i) (hm.1 j)).le Real.pi_pos.le
  nlinarith

theorem coorbitalVirial_pair_with_mass_floor (alpha : ℝ) (halpha : 0<alpha)
    (mass theta : Satellite → ℝ) (hm : PositiveRatio mass) (hfloor : ∀ i, alpha ≤ mass i)
    (harc : OrderedSemicircle theta) (hroot : ∀ i, angularEquation mass theta i=0)
    (i j : Satellite) (hij : i<j) (ht : theta j-theta i<h) :
    alpha^2*((theta j-theta i)*kernelF (theta j-theta i)) ≤ Real.pi/2 := by
  have hf : 0 ≤ (theta j-theta i)*kernelF (theta j-theta i) :=
    (mul_pos (harc i j hij).1 (kernelF_pos_on_short_arc (harc i j hij).1 ht)).le
  have hmass : alpha^2 ≤ mass i*mass j := by
    simpa only [pow_two] using mul_le_mul (hfloor i) (hfloor j) halpha.le (hm.1 i).le
  exact le_trans (mul_le_mul_of_nonneg_right hmass hf)
    (coorbitalVirial_pair_le_pi_div_two mass theta hm harc hroot i j hij)

/-- For a fixed positive mass floor, an actual root cannot approach any
satellite collision. This is the collision half of the properness argument. -/
theorem coorbital_roots_uniform_pair_separation (alpha : ℝ) (halpha : 0<alpha) :
    ∃ d : ℝ, 0<d ∧ ∀ mass theta : Satellite → ℝ,
      PositiveRatio mass → (∀ i, alpha ≤ mass i) → OrderedSemicircle theta →
      (∀ i, angularEquation mass theta i=0) → ∀ i j, i<j → d ≤ theta j-theta i := by
  have H : Tendsto (fun t : ℝ => alpha^2*(t*kernelF t)) (𝓝[>] 0) atTop := by
    simpa only [mul_comm] using kernelF_angle_mul_tendsto_atTop.atTop_mul_pos
      (sq_pos_of_pos halpha) tendsto_const_nhds
  have hevent : ∀ᶠ t in 𝓝[>] (0 : ℝ), Real.pi/2 < alpha^2*(t*kernelF t) :=
    H.eventually (eventually_gt_atTop (Real.pi/2))
  obtain ⟨d,hd,hdsmall⟩ := mem_nhdsGT_iff_exists_Ioo_subset.mp hevent
  refine ⟨min d h, lt_min hd (by unfold h; positivity), ?_⟩
  intro mass theta hm hfloor harc hroot i j hij
  by_contra hbad
  have ht : theta j-theta i < min d h := lt_of_not_ge hbad
  have hgt := hdsmall ⟨(harc i j hij).1, lt_of_lt_of_le ht (min_le_left _ _)⟩
  have hle := coorbitalVirial_pair_with_mass_floor alpha halpha mass theta hm hfloor
    harc hroot i j hij (lt_of_lt_of_le ht (min_le_right _ _))
  exact (not_lt_of_ge hle) hgt

end DominantFiveBody



