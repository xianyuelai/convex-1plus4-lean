import DominantFiveBody.TripleScalar
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-! Original §5.3 proof by integrating the actual divided Jacobian on an
ordered segment. The integral retains the same strict dominance margin. -/

noncomputable section
open scoped BigOperators Matrix
open Set
namespace DominantFiveBody
set_option maxHeartbeats 1000000

def tripleOrderedSegment (x y : TripleVector) (s : ℝ) : TripleVector :=
  x + s • (y - x)

theorem tripleOrderedSegment_ordered (x y : TripleVector)
    (hx : TripleOrdered x) (hy : TripleOrdered y)
    (s : ℝ) (hs : s ∈ Icc (0 : ℝ) 1) : TripleOrdered (tripleOrderedSegment x y s) := by
  intro i j hij
  have hxi := hx i j hij
  have hyi := hy i j hij
  have hdiff : 0 < (1 - s) * (x j - x i) + s * (y j - y i) := by
    rcases eq_or_lt_of_le hs.1 with hzero | hpos
    · rw [← hzero]; simpa using sub_pos.mpr hxi
    · exact add_pos_of_nonneg_of_pos
        (mul_nonneg (sub_nonneg.mpr hs.2) (sub_pos.mpr hxi).le)
        (mul_pos hpos (sub_pos.mpr hyi))
  change x i + s * (y i - x i) < x j + s * (y j - x j)
  nlinarith

def tripleIntegratedJacobian (alpha x y : TripleVector) : Matrix TripleLabel TripleLabel ℝ :=
  fun i j => ∫ s in (0 : ℝ)..1,
    tripleScalarJacobian alpha (tripleOrderedSegment x y s) i j

def tripleIntegratedCoefficient (alpha x y : TripleVector) (i j : TripleLabel) : ℝ :=
  ∫ s in (0 : ℝ)..1,
    2 * alpha j / |tripleOrderedSegment x y s i - tripleOrderedSegment x y s j| ^ 3

theorem tripleOrderedSegment_coefficient_continuousOn (alpha x y : TripleVector)
    (hx : TripleOrdered x) (hy : TripleOrdered y) (i j : TripleLabel) (hij : i ≠ j) :
    ContinuousOn (fun s : ℝ =>
      2 * alpha j / |tripleOrderedSegment x y s i - tripleOrderedSegment x y s j| ^ 3)
      (Icc (0 : ℝ) 1) := by
  apply ContinuousOn.div continuousOn_const
    ((by unfold tripleOrderedSegment; fun_prop : Continuous (fun s : ℝ =>
      tripleOrderedSegment x y s i - tripleOrderedSegment x y s j)).abs.pow 3).continuousOn
  intro s hs
  exact pow_ne_zero 3 (abs_ne_zero.mpr (sub_ne_zero.mpr
    (tripleOrdered_distinct (tripleOrderedSegment_ordered x y hx hy s hs) i j hij)))

theorem tripleIntegratedCoefficient_nonneg (alpha x y : TripleVector)
    (ha : ∀ i, 0 ≤ alpha i) (i j : TripleLabel) :
    0 ≤ tripleIntegratedCoefficient alpha x y i j := by
  apply intervalIntegral.integral_nonneg_of_forall (by norm_num)
  intro s
  exact div_nonneg (mul_nonneg (by norm_num) (ha j)) (pow_nonneg (abs_nonneg _) 3)

theorem tripleIntegratedJacobian_entries (alpha x y : TripleVector)
    (hx : TripleOrdered x) (hy : TripleOrdered y) (i j : TripleLabel) :
    tripleIntegratedJacobian alpha x y i j =
      if i = j then tripleD0 + ∑ k ∈ Finset.univ.erase i,
          tripleIntegratedCoefficient alpha x y i k
      else -tripleIntegratedCoefficient alpha x y i j := by
  classical
  have hc (k : TripleLabel) (hk : k ∈ Finset.univ.erase i) :
      IntervalIntegrable (fun s : ℝ =>
        2 * alpha k / |tripleOrderedSegment x y s i - tripleOrderedSegment x y s k| ^ 3)
        MeasureTheory.volume 0 1 :=
    (tripleOrderedSegment_coefficient_continuousOn alpha x y hx hy i k
      (Ne.symm (Finset.mem_erase.mp hk).1)).intervalIntegrable_of_Icc (by norm_num)
  by_cases hij : i = j
  · subst j
    unfold tripleIntegratedJacobian tripleScalarJacobian
    simp only [ite_true]
    simp_rw [Finset.mul_sum, ← mul_div_assoc]
    have hsumInt : IntervalIntegrable (fun s : ℝ => ∑ k ∈ Finset.univ.erase i,
        2 * alpha k / |tripleOrderedSegment x y s i - tripleOrderedSegment x y s k| ^ 3)
        MeasureTheory.volume 0 1 := by
      convert! IntervalIntegrable.sum _ hc using 1
      ext s
      simp
    rw [intervalIntegral.integral_add (f := fun _ => tripleD0) intervalIntegrable_const hsumInt,
      intervalIntegral.integral_finsetSum (f := fun k s =>
        2 * alpha k / |tripleOrderedSegment x y s i - tripleOrderedSegment x y s k| ^ 3) hc]
    simp [tripleIntegratedCoefficient]
  · unfold tripleIntegratedJacobian tripleScalarJacobian
    simp only [if_neg hij]
    simp_rw [neg_mul, neg_div]
    exact intervalIntegral.integral_neg

theorem matrix_dominance_margin_lower_norm (M : Matrix TripleLabel TripleLabel ℝ)
    (hdiag : ∀ i, 0 ≤ M i i)
    (hmargin : ∀ i, (∑ j ∈ Finset.univ.erase i, ‖M i j‖) = M i i - tripleD0)
    (v : TripleVector) : tripleD0 * ‖v‖ ≤ ‖M *ᵥ v‖ := by
  obtain ⟨i, hi⟩ := (IsGreatest.pi_norm v).1
  have hiv : ‖v i‖ = ‖v‖ := hi
  have hmax (j : TripleLabel) : ‖v j‖ ≤ ‖v i‖ := by
    rw [hiv]; exact norm_le_pi_norm v j
  have hrow : M i i * v i = (M *ᵥ v) i - ∑ j ∈ Finset.univ.erase i, M i j * v j := by
    have hs := Finset.sum_erase_add Finset.univ (fun j => M i j * v j) (Finset.mem_univ i)
    change _ = (M *ᵥ v) i at hs
    linarith
  have hsum : ‖∑ j ∈ Finset.univ.erase i, M i j * v j‖ ≤
      (M i i - tripleD0) * ‖v i‖ := by
    calc
      _ ≤ ∑ j ∈ Finset.univ.erase i, ‖M i j * v j‖ := norm_sum_le _ _
      _ = ∑ j ∈ Finset.univ.erase i, ‖M i j‖ * ‖v j‖ := by simp_rw [norm_mul]
      _ ≤ ∑ j ∈ Finset.univ.erase i, ‖M i j‖ * ‖v i‖ :=
        Finset.sum_le_sum (fun j _ => mul_le_mul_of_nonneg_left (hmax j) (norm_nonneg _))
      _ = (M i i - tripleD0) * ‖v i‖ := by rw [← Finset.sum_mul, hmargin i]
  have hnorm : M i i * ‖v i‖ ≤ ‖M *ᵥ v‖ + (M i i - tripleD0) * ‖v i‖ := by
    calc
      _ = ‖M i i * v i‖ := by rw [norm_mul, Real.norm_of_nonneg (hdiag i)]
      _ ≤ ‖(M *ᵥ v) i‖ + ‖∑ j ∈ Finset.univ.erase i, M i j * v j‖ := by
        rw [hrow]; exact norm_sub_le _ _
      _ ≤ ‖M *ᵥ v‖ + (M i i - tripleD0) * ‖v i‖ :=
        add_le_add (norm_le_pi_norm _ i) hsum
  rw [hiv] at hnorm
  nlinarith

theorem tripleIntegratedJacobian_lower_norm_bound (alpha x y v : TripleVector)
    (ha : ∀ i, 0 ≤ alpha i) (hx : TripleOrdered x) (hy : TripleOrdered y) :
    tripleD0 * ‖v‖ ≤ ‖tripleIntegratedJacobian alpha x y *ᵥ v‖ := by
  classical
  apply matrix_dominance_margin_lower_norm
  · intro i
    rw [tripleIntegratedJacobian_entries alpha x y hx hy i i, if_pos rfl]
    exact add_nonneg tripleD0_pos.le (Finset.sum_nonneg (fun j _ =>
      tripleIntegratedCoefficient_nonneg alpha x y ha i j))
  · intro i
    rw [tripleIntegratedJacobian_entries alpha x y hx hy i i, if_pos rfl]
    simp only [add_sub_cancel_left]
    apply Finset.sum_congr rfl
    intro j hj
    rw [tripleIntegratedJacobian_entries alpha x y hx hy i j,
      if_neg (Ne.symm (Finset.mem_erase.mp hj).1), norm_neg,
      Real.norm_of_nonneg (tripleIntegratedCoefficient_nonneg alpha x y ha i j)]

theorem tripleOrderedSegment_jacobian_continuousOn (alpha x y : TripleVector)
    (hx : TripleOrdered x) (hy : TripleOrdered y) (i j : TripleLabel) :
    ContinuousOn (fun s : ℝ =>
      tripleScalarJacobian alpha (tripleOrderedSegment x y s) i j) (Icc (0 : ℝ) 1) := by
  classical
  by_cases hij : i = j
  · subst j
    simp only [tripleScalarJacobian, ite_true]
    simp_rw [Finset.mul_sum, ← mul_div_assoc]
    exact continuousOn_const.add (continuousOn_finsetSum _ (fun k hk =>
      tripleOrderedSegment_coefficient_continuousOn alpha x y hx hy i k
        (Ne.symm (Finset.mem_erase.mp hk).1)))
  · simp only [tripleScalarJacobian, if_neg hij, neg_mul, neg_div]
    exact (tripleOrderedSegment_coefficient_continuousOn alpha x y hx hy i j hij).neg

theorem tripleScalarResidual_ordered_segment_integral (alpha x y : TripleVector)
    (hx : TripleOrdered x) (hy : TripleOrdered y) :
    (fun i => tripleScalarResidual alpha y i - tripleScalarResidual alpha x i) =
      tripleIntegratedJacobian alpha x y *ᵥ (y - x) := by
  classical
  funext i
  let f : ℝ → ℝ := fun s => tripleScalarResidual alpha (tripleOrderedSegment x y s) i
  let g : ℝ → ℝ := fun s =>
    (tripleScalarJacobian alpha (tripleOrderedSegment x y s) *ᵥ (y - x)) i
  have hc : ContinuousOn g (Icc (0 : ℝ) 1) := by
    unfold g Matrix.mulVec dotProduct
    exact continuousOn_finsetSum _ (fun j _ =>
      (tripleOrderedSegment_jacobian_continuousOn alpha x y hx hy i j).mul continuousOn_const)
  have hd (s : ℝ) (hs : s ∈ Icc (0 : ℝ) 1) : HasDerivAt f (g s) s := by
    have hp : HasDerivAt (tripleOrderedSegment x y) (y - x) s := by
      unfold tripleOrderedSegment
      simpa using ((hasDerivAt_id s).smul_const (y - x)).const_add x
    have hF := (tripleScalarResidual_hasFDerivAt alpha (tripleOrderedSegment x y s)
      (tripleOrdered_distinct (tripleOrderedSegment_ordered x y hx hy s hs))).comp_hasDerivAt s hp
    have hproj := (ContinuousLinearMap.proj i : TripleVector →L[ℝ] ℝ).hasFDerivAt.comp_hasDerivAt s hF
    simpa only [f, g, Function.comp_def, tripleScalarJacobian_mulVec,
      ContinuousLinearMap.proj_apply] using hproj
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun s hs => hd s (by simpa only [uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] using hs))
    (hc.intervalIntegrable_of_Icc (by norm_num))
  have hintegral : (∫ s in (0 : ℝ)..1, g s) =
      (tripleIntegratedJacobian alpha x y *ᵥ (y - x)) i := by
    change (∫ s in (0 : ℝ)..1,
      ∑ j, tripleScalarJacobian alpha (tripleOrderedSegment x y s) i j * (y - x) j) =
      ∑ j, tripleIntegratedJacobian alpha x y i j * (y - x) j
    rw [intervalIntegral.integral_finsetSum (f := fun j s =>
      tripleScalarJacobian alpha (tripleOrderedSegment x y s) i j * (y - x) j)
      (fun j _ => ((tripleOrderedSegment_jacobian_continuousOn alpha x y hx hy i j).mul
        continuousOn_const).intervalIntegrable_of_Icc (by norm_num))]
    simp_rw [intervalIntegral.integral_mul_const]
    rfl
  rw [hintegral] at hFTC
  simpa [f, tripleOrderedSegment] using hFTC.symm

theorem tripleScalar_root_unique_by_integratedJacobian (alpha x y : TripleVector)
    (ha : ∀ i, 0 ≤ alpha i) (hx : TripleOrdered x) (hy : TripleOrdered y)
    (hxr : ∀ i, tripleScalarResidual alpha x i = 0)
    (hyr : ∀ i, tripleScalarResidual alpha y i = 0) : x = y := by
  have hidentity := tripleScalarResidual_ordered_segment_integral alpha x y hx hy
  have hzero : tripleIntegratedJacobian alpha x y *ᵥ (y - x) = 0 := by
    rw [← hidentity]
    ext i
    simp [hxr i, hyr i]
  have hbound := tripleIntegratedJacobian_lower_norm_bound alpha x y (y - x) ha hx hy
  rw [hzero, norm_zero] at hbound
  have hnorm : ‖y - x‖ = 0 := by nlinarith [norm_nonneg (y - x), tripleD0_pos]
  exact (sub_eq_zero.mp (norm_eq_zero.mp hnorm)).symm

end DominantFiveBody
