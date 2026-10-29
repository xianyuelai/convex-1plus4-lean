import DominantFiveBody.BackgroundSpectrum
import DominantFiveBody.NewtonTargetDerivative

/-! # The actual equilateral probe field and its slow vector balance

Source §6.1.  The background operator is proved to be the derivative of
the original Newton probe field before the scalar-to-vector reduction.
-/

noncomputable section
open scoped BigOperators ContDiff

namespace DominantFiveBody

local instance backgroundPlaneAddCommGroup : AddCommGroup Plane :=
  (inferInstance : NormedAddCommGroup Plane).toAddCommGroup
local instance backgroundPlaneModule : Module ℝ Plane :=
  (inferInstance : NormedSpace ℝ Plane).toModule

def backgroundE0 (tau : ℝ) : Plane := polarPoint 1 (tau * Coorbital.h)
def backgroundW0 (tau : ℝ) : Plane := polarPoint 1 0 - backgroundE0 tau
def backgroundProbeCenter (eps tau : ℝ) : Plane := backgroundRadius eps • backgroundE0 tau
def backgroundExterior (eps : ℝ) : Plane := backgroundRadius eps • polarPoint 1 0
def backgroundProbeField (eps : ℝ) (q : Plane) : Plane :=
  q + newtonTargetField 0 q + eps • newtonTargetField (backgroundExterior eps) q -
    (eps / backgroundRadius eps ^ 3) • backgroundExterior eps
def backgroundOperator (eps tau : ℝ) : Plane →L[ℝ] Plane :=
  (3 / (1 + eps)) •
    (((innerSL ℝ (backgroundE0 tau)).smulRight (backgroundE0 tau)) +
      eps • ((innerSL ℝ (backgroundW0 tau)).smulRight (backgroundW0 tau)))
def backgroundSlowDirection (eps tau : ℝ) : Plane :=
  (Real.sqrt (1 + backgroundSlowK eps tau ^ 2))⁻¹ •
    (backgroundSlowK eps tau • backgroundE0 tau + quarterTurn (backgroundE0 tau))
def backgroundScalarLift (eps tau s : ℝ) : Plane :=
  (backgroundSlowLength eps * s) • backgroundSlowDirection eps tau

theorem backgroundE0_coordinates (tau : ℝ) (ht : tau = 1 ∨ tau = -1) :
    backgroundE0 tau = point (1 / 2) (tau * Real.sqrt 3 / 2) := by
  rcases ht with rfl | rfl
  all_goals ext i; fin_cases i
  all_goals simp [backgroundE0, polarPoint, Coorbital.h, point, Real.cos_pi_div_three,
    Real.sin_pi_div_three]
  all_goals ring

theorem backgroundE0_norm (tau : ℝ) : ‖backgroundE0 tau‖ = 1 := by
  simp [backgroundE0, polarPoint_norm]

theorem backgroundE0_inner_self (tau : ℝ) : inner ℝ (backgroundE0 tau) (backgroundE0 tau) = 1 := by
  rw [real_inner_self_eq_norm_sq, backgroundE0_norm]
  norm_num

theorem backgroundW0_decomposition (tau : ℝ) (ht : tau = 1 ∨ tau = -1) :
    backgroundW0 tau = (-1 / 2 : ℝ) • backgroundE0 tau -
      (tau * Real.sqrt 3 / 2) • quarterTurn (backgroundE0 tau) := by
  have hs : Real.sqrt 3 ^ 2 = (3 : ℝ) := Real.sq_sqrt (by norm_num)
  have ht2 : tau ^ 2 = 1 := by rcases ht with rfl | rfl <;> norm_num
  rw [backgroundW0, backgroundE0_coordinates tau ht]
  ext i
  fin_cases i
  all_goals simp [polarPoint, quarterTurn, point]
  · nlinarith [hs]
  · ring

theorem backgroundW0_norm (tau : ℝ) (ht : tau = 1 ∨ tau = -1) :
    ‖backgroundW0 tau‖ = 1 := by
  apply (sq_eq_sq₀ (norm_nonneg _) (by norm_num : 0 ≤ (1 : ℝ))).mp
  rw [EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_two, backgroundW0,
    backgroundE0_coordinates tau ht]
  simp only [PiLp.sub_apply, polarPoint, point, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_fin_one, Real.cos_zero, Real.sin_zero]
  have hs : Real.sqrt 3 ^ 2 = (3 : ℝ) := Real.sq_sqrt (by norm_num)
  have ht2 : tau ^ 2 = 1 := by rcases ht with rfl | rfl <;> norm_num
  ring_nf
  rw [ht2, hs]
  norm_num

theorem backgroundOperator_apply (eps tau : ℝ) (v : Plane) :
    backgroundOperator eps tau v = (3 / (1 + eps)) •
      (inner ℝ (backgroundE0 tau) v • backgroundE0 tau +
        eps • (inner ℝ (backgroundW0 tau) v • backgroundW0 tau)) := by
  rfl

theorem backgroundOperator_coordinates (eps tau x y : ℝ) (ht : tau = 1 ∨ tau = -1) :
    backgroundOperator eps tau (x • backgroundE0 tau + y • quarterTurn (backgroundE0 tau)) =
      (backgroundMatrix eps tau 0 0 * x + backgroundMatrix eps tau 0 1 * y) •
        backgroundE0 tau +
      (backgroundMatrix eps tau 1 0 * x + backgroundMatrix eps tau 1 1 * y) •
        quarterTurn (backgroundE0 tau) := by
  have hself := backgroundE0_inner_self tau
  have horth := quarterTurn_inner_self (backgroundE0 tau)
  have horth' : inner ℝ (quarterTurn (backgroundE0 tau)) (backgroundE0 tau) = 0 := by
    rw [real_inner_comm, horth]
  have hrot : inner ℝ (quarterTurn (backgroundE0 tau)) (quarterTurn (backgroundE0 tau)) = 1 := by
    rw [quarterTurn_inner_quarterTurn, hself]
  have hwe : inner ℝ (backgroundW0 tau) (backgroundE0 tau) = -1 / 2 := by
    rw [backgroundW0_decomposition tau ht]
    simp only [inner_sub_left, real_inner_smul_left, hself, horth', mul_one, mul_zero, sub_zero]
  have hwt : inner ℝ (backgroundW0 tau) (quarterTurn (backgroundE0 tau)) =
      -tau * Real.sqrt 3 / 2 := by
    rw [backgroundW0_decomposition tau ht]
    simp only [inner_sub_left, real_inner_smul_left, horth, hrot, mul_zero, mul_one, zero_sub]
    ring
  rw [backgroundOperator_apply]
  simp only [inner_add_right, real_inner_smul_right, hself, horth, hwe, hwt, mul_one,
    mul_zero, add_zero]
  rw [backgroundW0_decomposition tau ht]
  have hs : Real.sqrt 3 ^ 2 = (3 : ℝ) := Real.sq_sqrt (by norm_num)
  have ht2 : tau ^ 2 = 1 := by rcases ht with rfl | rfl <;> norm_num
  simp only [backgroundMatrix, Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_fin_one, smul_add, smul_sub, smul_smul]
  have hc : (3 / (1 + eps)) * (eps * ((x * (-1 / 2) + y * (-tau * Real.sqrt 3 / 2)) *
      (tau * Real.sqrt 3 / 2))) = -(3 / (1 + eps) * (tau * Real.sqrt 3 * eps / 4) * x +
      3 / (1 + eps) * (3 * eps / 4) * y) := by
    ring_nf
    rw [ht2, hs]
    ring
  rw [hc]
  module

theorem newtonTargetDerivative_scaled_unit (source target u : Plane) (a : ℝ)
    (ha : 0 < a) (hu : ‖u‖ = 1) (hdiff : source - target = a • u) :
    newtonTargetDerivative source target = (a ^ 3)⁻¹ •
      ((3 : ℝ) • ((innerSL ℝ u).smulRight u) - ContinuousLinearMap.id ℝ Plane) := by
  have hn : ‖source - target‖ = a := by rw [hdiff, norm_smul, Real.norm_eq_abs, abs_of_pos ha, hu, mul_one]
  ext v i
  rw [newtonTargetDerivative_apply, hn, hdiff]
  simp only [real_inner_smul_left,
    smul_smul, sub_apply, smul_apply, ContinuousLinearMap.smulRight_apply,
    innerSL_apply_apply, ContinuousLinearMap.id_apply, PiLp.sub_apply, PiLp.smul_apply, smul_eq_mul]
  field_simp

theorem backgroundProbeField_zero (eps tau : ℝ) (he : 0 < 1 + eps)
    (ht : tau = 1 ∨ tau = -1) :
    backgroundProbeField eps (backgroundProbeCenter eps tau) = 0 := by
  have ha := backgroundRadius_pos eps he
  have ha3 := backgroundRadius_cube eps he.le
  have hn0 : ‖(0 : Plane) - backgroundProbeCenter eps tau‖ = backgroundRadius eps := by
    simp [backgroundProbeCenter, norm_smul, abs_of_pos ha, backgroundE0_norm]
  have hdiff : backgroundExterior eps - backgroundProbeCenter eps tau =
      backgroundRadius eps • backgroundW0 tau := by
    simp only [backgroundExterior, backgroundProbeCenter, backgroundW0, smul_sub]
  have hnp : ‖backgroundExterior eps - backgroundProbeCenter eps tau‖ = backgroundRadius eps := by
    rw [hdiff, norm_smul, Real.norm_eq_abs, abs_of_pos ha, backgroundW0_norm tau ht, mul_one]
  unfold backgroundProbeField newtonTargetField
  rw [hn0, hnp]
  rw [backgroundProbeCenter, backgroundExterior, backgroundW0] at hdiff
  ext i
  simp only [PiLp.add_apply, PiLp.sub_apply, PiLp.smul_apply, PiLp.zero_apply, smul_eq_mul,
    backgroundProbeCenter, backgroundExterior]
  field_simp
  nlinarith [congrArg (fun x => x * (backgroundE0 tau i)) ha3]

theorem backgroundProbeField_hasFDerivAt (eps tau : ℝ) (he : 0 < 1 + eps)
    (ht : tau = 1 ∨ tau = -1) :
    HasFDerivAt (backgroundProbeField eps) (backgroundOperator eps tau)
      (backgroundProbeCenter eps tau) := by
  have ha := backgroundRadius_pos eps he
  have ha3 := backgroundRadius_cube eps he.le
  have h0 : (0 : Plane) ≠ backgroundProbeCenter eps tau := by
    have hn : ‖backgroundProbeCenter eps tau‖ = backgroundRadius eps := by
      simp [backgroundProbeCenter, norm_smul, abs_of_pos ha, backgroundE0_norm]
    intro hz
    rw [← hz, norm_zero] at hn
    linarith
  have hdiff : backgroundExterior eps - backgroundProbeCenter eps tau =
      backgroundRadius eps • backgroundW0 tau := by
    simp only [backgroundExterior, backgroundProbeCenter, backgroundW0, smul_sub]
  have hp : backgroundExterior eps ≠ backgroundProbeCenter eps tau := by
    intro hz
    have hn : ‖backgroundExterior eps - backgroundProbeCenter eps tau‖ = backgroundRadius eps := by
      rw [hdiff, norm_smul, Real.norm_eq_abs, abs_of_pos ha, backgroundW0_norm tau ht, mul_one]
    rw [hz, sub_self, norm_zero] at hn
    linarith
  have hneg : (0 : Plane) - backgroundProbeCenter eps tau =
      backgroundRadius eps • (-backgroundE0 tau) := by simp [backgroundProbeCenter]
  have hd0 := newtonTargetDerivative_scaled_unit 0 (backgroundProbeCenter eps tau)
    (-backgroundE0 tau) (backgroundRadius eps) ha (by simp [backgroundE0_norm]) hneg
  have hdp := newtonTargetDerivative_scaled_unit (backgroundExterior eps)
    (backgroundProbeCenter eps tau) (backgroundW0 tau) (backgroundRadius eps) ha
    (backgroundW0_norm tau ht) hdiff
  have hd := (((hasFDerivAt_id (backgroundProbeCenter eps tau)).add
    (newtonTargetField_hasFDerivAt 0 _ h0)).add
    ((newtonTargetField_hasFDerivAt (backgroundExterior eps) _ hp).const_smul eps)).sub_const
      ((eps / backgroundRadius eps ^ 3) • backgroundExterior eps)
  apply hd.congr_fderiv
  rw [hd0, hdp, ha3]
  ext v i
  simp only [add_apply, sub_apply, smul_apply, ContinuousLinearMap.id_apply,
    ContinuousLinearMap.smulRight_apply, innerSL_apply_apply, inner_neg_left, smul_smul,
    backgroundOperator, PiLp.add_apply, PiLp.sub_apply, PiLp.smul_apply, PiLp.neg_apply, smul_eq_mul]
  field_simp
  ring

theorem backgroundSlowDirection_norm (eps tau : ℝ) :
    ‖backgroundSlowDirection eps tau‖ = 1 := by
  have hs : 0 < 1 + backgroundSlowK eps tau ^ 2 := by positivity
  have hn : ‖backgroundSlowK eps tau • backgroundE0 tau + quarterTurn (backgroundE0 tau)‖ ^ 2 =
      1 + backgroundSlowK eps tau ^ 2 := by
    rw [norm_add_sq_real, norm_smul, Real.norm_eq_abs]
    have hrot : ‖quarterTurn (backgroundE0 tau)‖ ^ 2 = 1 := by
      rw [← real_inner_self_eq_norm_sq, quarterTurn_inner_quarterTurn, backgroundE0_inner_self]
    rw [backgroundE0_norm, mul_one, sq_abs, hrot, real_inner_smul_left, quarterTurn_inner_self]
    ring
  have hnorm : ‖backgroundSlowK eps tau • backgroundE0 tau + quarterTurn (backgroundE0 tau)‖ =
      Real.sqrt (1 + backgroundSlowK eps tau ^ 2) := by
    apply (sq_eq_sq₀ (norm_nonneg _) (Real.sqrt_nonneg _)).mp
    rw [hn, Real.sq_sqrt hs.le]
  rw [backgroundSlowDirection, norm_smul, hnorm, Real.norm_eq_abs,
    abs_of_pos (inv_pos.mpr (Real.sqrt_pos.mpr hs)), inv_mul_cancel₀ (ne_of_gt (Real.sqrt_pos.mpr hs))]

theorem backgroundSlowDirection_eigen (eps tau : ℝ) (he : |eps| < 1 / 4)
    (ht : tau = 1 ∨ tau = -1) :
    backgroundOperator eps tau (backgroundSlowDirection eps tau) =
      backgroundSlowLambda eps • backgroundSlowDirection eps tau := by
  have ht2 : tau ^ 2 = 1 := by rcases ht with rfl | rfl <;> norm_num
  have hv := backgroundSlowK_eigenvector eps tau he ht2
  have h0 := congrFun hv 0
  have h1 := congrFun hv 1
  simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two] at h0 h1
  have hc := backgroundOperator_coordinates eps tau (backgroundSlowK eps tau) 1 ht
  simp only [one_smul, mul_one] at hc
  rw [backgroundSlowDirection, map_smul, hc]
  simp only [h0, h1, smul_add, smul_smul]
  module

theorem backgroundSlowDirection_contDiffAt (n : ℕ∞ω) (eps tau : ℝ) (he : |eps| < 1 / 4) :
    ContDiffAt ℝ n (fun e => backgroundSlowDirection e tau) eps := by
  have hk := backgroundSlowK_contDiffAt n eps tau he
  have hs : 0 < 1 + backgroundSlowK eps tau ^ 2 := by positivity
  exact (((contDiffAt_const.add (hk.pow 2)).sqrt (ne_of_gt hs)).inv
    (ne_of_gt (Real.sqrt_pos.mpr hs))).smul
    ((hk.smul contDiffAt_const).add contDiffAt_const)

@[simp] theorem backgroundSlowDirection_zero (tau : ℝ) :
    backgroundSlowDirection 0 tau = quarterTurn (backgroundE0 tau) := by
  simp [backgroundSlowDirection]

theorem backgroundAngularScale_pos (eps tau : ℝ) (he : 0 < 1 + eps) :
    0 < backgroundAngularScale eps tau := by
  exact div_pos (backgroundSlowLength_pos eps (ne_of_gt he))
    (mul_pos (backgroundRadius_pos eps he)
      (Real.sqrt_pos.mpr (by positivity)))

/-- The factor `b` converts the vector slow displacement to the actual
radial/angular differential, including the factor `a` on angular rows. -/
theorem backgroundSlow_polar_displacement (eps tau s : ℝ) (he : 0 < 1 + eps) :
    (backgroundRadius eps * backgroundSlowK eps tau *
        (backgroundAngularScale eps tau * s)) • backgroundE0 tau +
      (backgroundRadius eps * (backgroundAngularScale eps tau * s)) •
        quarterTurn (backgroundE0 tau) = backgroundScalarLift eps tau s := by
  have ha := ne_of_gt (backgroundRadius_pos eps he)
  have hn : Real.sqrt (1 + backgroundSlowK eps tau ^ 2) ≠ 0 :=
    ne_of_gt (Real.sqrt_pos.mpr (by positivity))
  ext i
  simp only [backgroundAngularScale, backgroundScalarLift, backgroundSlowDirection,
    PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]
  field_simp

theorem backgroundProbeField_fderiv (eps tau : ℝ) (he : 0 < 1 + eps)
    (ht : tau = 1 ∨ tau = -1) :
    fderiv ℝ (backgroundProbeField eps) (backgroundProbeCenter eps tau) =
      backgroundOperator eps tau :=
  (backgroundProbeField_hasFDerivAt eps tau he ht).fderiv

theorem backgroundScalarLift_injective (eps tau : ℝ) (he : 1 + eps ≠ 0) :
    Function.Injective (backgroundScalarLift eps tau) := by
  intro s r hsr
  have hp := congrArg (fun v => inner ℝ v (backgroundSlowDirection eps tau)) hsr
  simp only [backgroundScalarLift, real_inner_smul_left,
    real_inner_self_eq_norm_sq, backgroundSlowDirection_norm, one_pow, mul_one] at hp
  exact mul_left_cancel₀ (ne_of_gt (backgroundSlowLength_pos eps he)) hp

theorem backgroundScalarLift_difference (eps tau s r : ℝ) :
    backgroundScalarLift eps tau s - backgroundScalarLift eps tau r =
      (backgroundSlowLength eps * (s - r)) • backgroundSlowDirection eps tau := by
  unfold backgroundScalarLift
  module

theorem backgroundScalarLift_newtonTargetField (eps tau s r : ℝ)
    (he : 1 + eps ≠ 0) :
    newtonTargetField (backgroundScalarLift eps tau s) (backgroundScalarLift eps tau r) =
      ((backgroundSlowLength eps ^ 2)⁻¹ * tripleScalarForce (s - r)) •
        backgroundSlowDirection eps tau := by
  have hl := backgroundSlowLength_pos eps he
  unfold newtonTargetField
  rw [backgroundScalarLift_difference, norm_smul, backgroundSlowDirection_norm,
    Real.norm_eq_abs, abs_mul, abs_of_pos hl, mul_one, smul_smul]
  congr 1
  by_cases hsr : s - r = 0
  · simp [hsr, tripleScalarForce]
  · unfold tripleScalarForce
    have hab := abs_ne_zero.mpr hsr
    field_simp

theorem backgroundScalarLift_weighted_center (eps tau : ℝ) (omega s : TripleVector)
    (hcenter : ∑ i, omega i * s i = 0) :
    ∑ i, omega i • backgroundScalarLift eps tau (s i) = 0 := by
  unfold backgroundScalarLift
  simp only [smul_smul]
  rw [← Finset.sum_smul]
  have hs : ∑ i, omega i * (backgroundSlowLength eps * s i) = 0 := by
    calc
      _ = backgroundSlowLength eps * ∑ i, omega i * s i := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i _
        ring
      _ = 0 := by rw [hcenter, mul_zero]
  rw [hs, zero_smul]

/-- `eq:vector-slow`, proved for the actual Newton forces, including all
zero scalar weights.  The scalar rows are the original `TripleScalar`
equations, and the linear operator is the actual probe-field derivative. -/
theorem backgroundScalarLift_vector_balance (eps tau : ℝ) (omega s : TripleVector)
    (he : |eps| < 1 / 4) (ht : tau = 1 ∨ tau = -1)
    (hroot : ∀ i, tripleScalarResidual omega s i = 0) (i : TripleLabel) :
    backgroundOperator eps tau (backgroundScalarLift eps tau (s i)) -
      eps • (∑ j ∈ Finset.univ.erase i,
        omega j • newtonTargetField (backgroundScalarLift eps tau (s i))
          (backgroundScalarLift eps tau (s j))) = 0 := by
  have hn := ne_of_gt (backgroundSmall_one_add_pos eps he)
  have hs : ∑ j ∈ Finset.univ.erase i, omega j * tripleScalarForce (s i - s j) =
      tripleD0 * s i := by
    have hr := hroot i
    unfold tripleScalarResidual at hr
    linarith
  have hsum : ∑ j ∈ Finset.univ.erase i,
      omega j • newtonTargetField (backgroundScalarLift eps tau (s i))
        (backgroundScalarLift eps tau (s j)) =
      ((backgroundSlowLength eps ^ 2)⁻¹ * (tripleD0 * s i)) •
        backgroundSlowDirection eps tau := by
    simp_rw [backgroundScalarLift_newtonTargetField eps tau _ _ hn, smul_smul]
    rw [← Finset.sum_smul]
    congr 1
    calc
      _ = (backgroundSlowLength eps ^ 2)⁻¹ *
          ∑ j ∈ Finset.univ.erase i, omega j * tripleScalarForce (s i - s j) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro j _
        ring
      _ = _ := by rw [hs]
  rw [hsum, backgroundScalarLift, map_smul, backgroundSlowDirection_eigen eps tau he ht,
    smul_smul, smul_smul]
  have hc : (backgroundSlowLength eps * s i) * backgroundSlowLambda eps =
      eps * ((backgroundSlowLength eps ^ 2)⁻¹ * (tripleD0 * s i)) := by
    calc
      _ = eps * (backgroundSlowD eps * backgroundSlowLength eps) * s i := by
        unfold backgroundSlowLambda
        ring
      _ = _ := by rw [backgroundSlow_scaling eps hn]; ring
  rw [hc, sub_self]

end DominantFiveBody
