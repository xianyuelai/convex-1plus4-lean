import DominantFiveBody.TripleInternal
import DominantFiveBody.PairInternal

/-! Original weighted single-scale cancellations, before choosing a chart. -/

noncomputable section
open scoped BigOperators
namespace DominantFiveBody
set_option maxHeartbeats 1000000

theorem singleScaleChi_neg (t b : ℝ) : singleScaleChi t (-b) = singleScaleChi t b := by
  unfold singleScaleChi
  rw [show t * -b / 2 = -(t * b / 2) by ring, Real.sinc_neg]
  ring

theorem singleScaleW_reverse (R t wi wj zi zj : ℝ) :
    singleScaleW R t wi wj zi zj = singleScaleW R t wj wi zj zi := by
  unfold singleScaleW
  congr 1
  unfold singleScaleWSq
  rw [show t * (zi - zj) / 2 = -(t * (zj - zi) / 2) by ring, Real.sinc_neg]
  ring

def singleScaleWeightedRadialPair {n : ℕ} (eps t R : ℝ) (alpha w z : Fin n → ℝ)
    (i j : Fin n) : ℝ :=
  -eps * t * alpha i * alpha j *
    (w i - w j + singleScaleRadius R t (w j) * singleScaleChi t (z i - z j)) *
      (singleScaleW R t (w i) (w j) (z i) (z j) ^ 3)⁻¹

def singleScaleWeightedAngularPair {n : ℕ} (eps t R : ℝ) (alpha w z : Fin n → ℝ)
    (i j : Fin n) : ℝ :=
  -t * alpha i * alpha j * singleScaleRadius R t (w i) * singleScaleRadius R t (w j) *
    (z i - z j) * Real.sinc (t * (z i - z j)) *
      ((singleScaleW R t (w i) (w j) (z i) (z j) ^ 3)⁻¹ - t ^ 3 / (1 + eps))

theorem singleScaleWeightedAngularPair_reverse {n : ℕ} (eps t R : ℝ)
    (alpha w z : Fin n → ℝ) (i j : Fin n) :
    singleScaleWeightedAngularPair eps t R alpha w z i j =
      -singleScaleWeightedAngularPair eps t R alpha w z j i := by
  unfold singleScaleWeightedAngularPair
  rw [singleScaleW_reverse R t (w i) (w j) (z i) (z j)]
  rw [show t * (z i - z j) = -(t * (z j - z i)) by ring, Real.sinc_neg]
  ring

theorem singleScaleWeightedRadialPair_diagonal {n : ℕ} (eps t R : ℝ)
    (alpha w z : Fin n → ℝ) (i : Fin n) :
    singleScaleWeightedRadialPair eps t R alpha w z i i = 0 := by
  simp [singleScaleWeightedRadialPair, singleScaleChi]

theorem singleScaleWeightedRadialPair_pair_sum {n : ℕ} (eps t R : ℝ)
    (alpha w z : Fin n → ℝ) (i j : Fin n) :
    singleScaleWeightedRadialPair eps t R alpha w z i j +
      singleScaleWeightedRadialPair eps t R alpha w z j i =
        -eps * alpha i * alpha j *
          (singleScaleRadius R t (w i) + singleScaleRadius R t (w j)) *
            (1 - Real.cos (t * (z i - z j))) *
              (singleScaleW R t (w i) (w j) (z i) (z j) ^ 3)⁻¹ := by
  unfold singleScaleWeightedRadialPair
  rw [singleScaleW_reverse R t (w j) (w i) (z j) (z i)]
  rw [show z j - z i = -(z i - z j) by ring, singleScaleChi_neg]
  rw [singleScaleChi_identity]
  ring

theorem singleScale_internal_weighted_angular_sum {n : ℕ} (eps t R : ℝ)
    (alpha w z : Fin n → ℝ) :
    (∑ i, ∑ j ∈ Finset.univ.erase i, singleScaleWeightedAngularPair eps t R alpha w z i j) = 0 := by
  classical
  have hd (i : Fin n) : singleScaleWeightedAngularPair eps t R alpha w z i i = 0 := by
    simp [singleScaleWeightedAngularPair]
  simp_rw [Finset.sum_erase_eq_sub (Finset.mem_univ _), hd, sub_zero]
  have hneg : (∑ i, ∑ j, singleScaleWeightedAngularPair eps t R alpha w z i j) =
      -(∑ i, ∑ j, singleScaleWeightedAngularPair eps t R alpha w z i j) := by
    calc
      _ = ∑ j, ∑ i, singleScaleWeightedAngularPair eps t R alpha w z i j := Finset.sum_comm
      _ = _ := by
        rw [← Finset.sum_neg_distrib]
        apply Finset.sum_congr rfl
        intro j _
        rw [← Finset.sum_neg_distrib]
        apply Finset.sum_congr rfl
        intro i _
        exact singleScaleWeightedAngularPair_reverse eps t R alpha w z i j
  linarith

theorem singleScale_three_weighted_radial_sum (eps t R : ℝ) (alpha w z : Fin 3 → ℝ) :
    (∑ i, ∑ j ∈ Finset.univ.erase i, singleScaleWeightedRadialPair eps t R alpha w z i j) =
      ∑ i, ∑ j ∈ Finset.univ.filter (fun j => i < j),
        -eps * alpha i * alpha j *
          (singleScaleRadius R t (w i) + singleScaleRadius R t (w j)) *
            (1 - Real.cos (t * (z i - z j))) *
              (singleScaleW R t (w i) (w j) (z i) (z j) ^ 3)⁻¹ := by
  have h01 := singleScaleWeightedRadialPair_pair_sum eps t R alpha w z 0 1
  have h02 := singleScaleWeightedRadialPair_pair_sum eps t R alpha w z 0 2
  have h12 := singleScaleWeightedRadialPair_pair_sum eps t R alpha w z 1 2
  simp only [Finset.sum_erase_eq_sub (Finset.mem_univ _), singleScaleWeightedRadialPair_diagonal,
    sub_zero, Fin.sum_univ_three]
  simp only [Finset.sum_filter, Fin.sum_univ_three]
  norm_num
  simp only [show (0 : Fin 3) < 2 from by decide, show (1 : Fin 3) < 2 from by decide,
    show (2 : Fin 3) ≠ 0 from by decide, ite_true, ite_false]
  linear_combination h01 + h02 + h12

theorem singleScale_pair_weighted_radial_sum (eps t R : ℝ) (alpha w z : Fin 2 → ℝ) :
    (∑ i, ∑ j ∈ Finset.univ.erase i, singleScaleWeightedRadialPair eps t R alpha w z i j) =
      -eps * alpha 0 * alpha 1 *
        (singleScaleRadius R t (w 0) + singleScaleRadius R t (w 1)) *
          (1 - Real.cos (t * (z 0 - z 1))) *
            (singleScaleW R t (w 0) (w 1) (z 0) (z 1) ^ 3)⁻¹ := by
  have h01 := singleScaleWeightedRadialPair_pair_sum eps t R alpha w z 0 1
  simp only [Finset.sum_erase_eq_sub (Finset.mem_univ _), singleScaleWeightedRadialPair_diagonal,
    sub_zero, Fin.sum_univ_two]
  linear_combination h01

theorem tripleInternalRadial_source_formula (eps t : ℝ) (alpha : TripleVector)
    (y : TripleChartVariables) (i : TripleLabel) :
    tripleInternalRadial eps t alpha y i =
      -eps * t * ∑ j ∈ Finset.univ.erase i, alpha j *
        (tripleChartRadialPositions alpha y i - tripleChartRadialPositions alpha y j +
          tripleChartRadii t alpha y j.castSucc * singleScaleChi t
            (tripleChartAngularPositions alpha y i - tripleChartAngularPositions alpha y j)) *
        (tripleChartW t alpha y i j ^ 3)⁻¹ := by
  unfold tripleInternalRadial tripleInternalRadialReduced
  ring

theorem tripleInternalAngular_source_formula (eps t : ℝ) (alpha : TripleVector)
    (y : TripleChartVariables) (i : TripleLabel) :
    tripleInternalAngular eps t alpha y i =
      -t * ∑ j ∈ Finset.univ.erase i, alpha j * tripleChartRadii t alpha y i.castSucc *
        tripleChartRadii t alpha y j.castSucc *
        (tripleChartAngularPositions alpha y i - tripleChartAngularPositions alpha y j) *
        Real.sinc (t * (tripleChartAngularPositions alpha y i - tripleChartAngularPositions alpha y j)) *
        ((tripleChartW t alpha y i j ^ 3)⁻¹ - t ^ 3 / (1 + eps)) := by
  unfold tripleInternalAngular tripleInternalAngularReduced
  ring

theorem tripleInternal_weighted_angular_zero (eps t : ℝ) (alpha : TripleVector)
    (y : TripleChartVariables) :
    (∑ i, alpha i * tripleInternalAngular eps t alpha y i) = 0 := by
  have h := singleScale_internal_weighted_angular_sum eps t (y 1) alpha
    (tripleChartRadialPositions alpha y) (tripleChartAngularPositions alpha y)
  rw [← h]
  apply Finset.sum_congr rfl
  intro i _
  rw [tripleInternalAngular_source_formula, Finset.mul_sum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  rw [tripleChartRadii_cluster, tripleChartRadii_cluster]
  dsimp [singleScaleWeightedAngularPair, singleScaleRadius, tripleChartW, tripleChartWSq, singleScaleW]
  ring

theorem tripleInternal_weighted_radial_upper_sum (eps t : ℝ) (alpha : TripleVector)
    (y : TripleChartVariables) :
    (∑ i, alpha i * tripleInternalRadial eps t alpha y i) =
      ∑ i, ∑ j ∈ Finset.univ.filter (fun j => i < j),
        -eps * alpha i * alpha j *
          (tripleChartRadii t alpha y i.castSucc + tripleChartRadii t alpha y j.castSucc) *
          (1 - Real.cos (t * (tripleChartAngularPositions alpha y i -
            tripleChartAngularPositions alpha y j))) * (tripleChartW t alpha y i j ^ 3)⁻¹ := by
  have h := singleScale_three_weighted_radial_sum eps t (y 1) alpha
    (tripleChartRadialPositions alpha y) (tripleChartAngularPositions alpha y)
  calc
    _ = ∑ i, ∑ j ∈ Finset.univ.erase i,
        singleScaleWeightedRadialPair eps t (y 1) alpha
          (tripleChartRadialPositions alpha y) (tripleChartAngularPositions alpha y) i j := by
      apply Finset.sum_congr rfl
      intro i _
      rw [tripleInternalRadial_source_formula, Finset.mul_sum, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j _
      rw [tripleChartRadii_cluster]
      dsimp [singleScaleWeightedRadialPair, singleScaleRadius, tripleChartW, tripleChartWSq, singleScaleW]
      ring
    _ = _ := h
    _ = _ := by
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      rw [tripleChartRadii_cluster, tripleChartRadii_cluster]
      rfl

theorem pairInternal_weighted_radial_source (eps t alpha : ℝ) (y : PairChartVariables) :
    alpha * pairInternalRadialA eps t alpha y + (1 - alpha) * pairInternalRadialB eps t alpha y =
      -eps * alpha * (1 - alpha) *
        (pairChartRadii t alpha y 0 + pairChartRadii t alpha y 1) *
          (1 - Real.cos (t * y 6)) * (pairChartW t alpha y ^ 3)⁻¹ := by
  rw [pairInternalRadial_mean_identity]
  unfold pairInternalRadialMean
  rw [singleScaleChi_identity]
  ring

end DominantFiveBody
