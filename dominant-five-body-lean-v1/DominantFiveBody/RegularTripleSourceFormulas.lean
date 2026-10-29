import DominantFiveBody.TripleBoundary

/-! Literal one-source scalar field and the complete regular-triple
boundary vector M from `eq:Hzero` and the display immediately following it.
The derivatives are the actual Fréchet derivative of the scalar field. -/

noncomputable section
open scoped BigOperators Matrix
namespace DominantFiveBody
set_option maxHeartbeats 800000

def regularTripleScalarH (r : ℝ) (x : ℝ × ℝ) : ℝ :=
  twoSourcePolarAngular 1 r r 0 x

theorem polar_distance_sq_cos (rho r v : ℝ) :
    ‖polarPoint rho v - polarPoint r 0‖ ^ 2 =
      rho ^ 2 + r ^ 2 - 2 * rho * r * Real.cos v := by
  rw [EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_two]
  simp only [PiLp.sub_apply, polarPoint, point, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_fin_one, Real.cos_zero, Real.sin_zero,
    mul_one, mul_zero, sub_zero]
  nlinarith [Real.sin_sq_add_cos_sq v]

theorem sqrt_cube_inverse_eq_negative_three_halves (x : ℝ) (hx : 0 ≤ x) :
    ((Real.sqrt x) ^ 3)⁻¹ = x ^ (-(3 : ℝ) / 2) := by
  have hn : -(3 : ℝ) / 2 = -(3 / 2 : ℝ) := by ring
  rw [hn, Real.rpow_neg hx, Real.rpow_div_two_eq_sqrt 3 hx]
  norm_num

/-- The exact original exponent `-3/2`, with no unnamed distance term. -/
theorem regularTripleScalarH_source_formula (rho v r : ℝ) :
    regularTripleScalarH r (rho, v) = -rho * r * Real.sin v *
      ((rho ^ 2 + r ^ 2 - 2 * rho * r * Real.cos v) ^ (-(3 : ℝ) / 2) - 1) := by
  have he : twoSourceTargetField 1 r r 0 (polarPoint rho v) =
      newtonTargetField (polarPoint r 0) (polarPoint rho v) - polarPoint r 0 := by
    simp [twoSourceTargetField]
  have hs : Real.sqrt (rho ^ 2 + r ^ 2 - 2 * rho * r * Real.cos v) =
      ‖polarPoint rho v - polarPoint r 0‖ := by
    rw [← polar_distance_sq_cos, Real.sqrt_sq (norm_nonneg _)]
  have hnonneg : 0 ≤ rho ^ 2 + r ^ 2 - 2 * rho * r * Real.cos v := by
    rw [← polar_distance_sq_cos]
    positivity
  unfold regularTripleScalarH twoSourcePolarAngular
  rw [he]
  conv_lhs => arg 2; arg 2; rw [← one_smul ℝ (polarPoint r 0)]
  rw [newtonTargetField_angular]
  rw [← hs, sqrt_cube_inverse_eq_negative_three_halves _ hnonneg]
  simp only [zero_sub, Real.sin_neg]
  ring

def regularTripleScalarH_rho (r : ℝ) (x : ℝ × ℝ) : ℝ :=
  (fderiv ℝ (regularTripleScalarH r) x) (1, 0)

def regularTripleScalarH_v (r : ℝ) (x : ℝ × ℝ) : ℝ :=
  (fderiv ℝ (regularTripleScalarH r) x) (0, 1)

theorem regularTripleScalarH_differentiableAt (r : ℝ) (x : ℝ × ℝ)
    (hsep : polarPoint r 0 ≠ polarPoint x.1 x.2) :
    DifferentiableAt ℝ (regularTripleScalarH r) x :=
  twoSourcePolarAngular_differentiableAt 1 r r 0 x hsep hsep

theorem regularTripleScalarH_fderiv_apply (r : ℝ) (x : ℝ × ℝ) (w z : ℝ) :
    (fderiv ℝ (regularTripleScalarH r) x) (w, z) =
      regularTripleScalarH_rho r x * w + regularTripleScalarH_v r x * z := by
  have hv : (w, z) = w • (1, 0) + z • (0, 1) := by ext <;> simp
  rw [hv, map_add, map_smul, map_smul]
  simp only [regularTripleScalarH_rho, regularTripleScalarH_v, smul_eq_mul]
  ring

def regularTripleBoundaryM (alpha : TripleVector) (y : TripleChartVariables)
    (i : TripleLabel) : ℝ :=
  (fderiv ℝ (regularTripleScalarH (y 0)) (y 1, y 4))
      (tripleChartRadialPositions alpha y i, tripleChartAngularPositions alpha y i) +
    tripleInternalAngularReduced 0 0 alpha y i

/-- A complete literal M_i formula, including its Newton denominator. -/
theorem regularTripleBoundaryM_source_formula (alpha : TripleVector)
    (y : TripleChartVariables) (i : TripleLabel) :
    regularTripleBoundaryM alpha y i =
      regularTripleScalarH_rho (y 0) (y 1, y 4) * tripleChartRadialPositions alpha y i +
      regularTripleScalarH_v (y 0) (y 1, y 4) * tripleChartAngularPositions alpha y i -
      ∑ j ∈ Finset.univ.erase i,
        alpha j * y 1 ^ 2 *
          (tripleChartAngularPositions alpha y i - tripleChartAngularPositions alpha y j) /
        (((tripleChartRadialPositions alpha y i - tripleChartRadialPositions alpha y j) ^ 2 +
          y 1 ^ 2 * (tripleChartAngularPositions alpha y i -
            tripleChartAngularPositions alpha y j) ^ 2) ^ ((3 : ℝ) / 2)) := by
  rw [regularTripleBoundaryM, regularTripleScalarH_fderiv_apply,
    tripleInternalAngularReduced_at_boundary]
  simp only [sub_eq_add_neg, div_eq_mul_inv]
  congr 2
  apply Finset.sum_congr rfl
  intro j _
  simp only [← sub_eq_add_neg]
  have hx : 0 ≤
      (tripleChartRadialPositions alpha y i - tripleChartRadialPositions alpha y j) ^ 2 +
      y 1 ^ 2 * (tripleChartAngularPositions alpha y i -
        tripleChartAngularPositions alpha y j) ^ 2 := by positivity
  rw [← div_eq_mul_inv (3 : ℝ) 2, Real.rpow_div_two_eq_sqrt 3 hx]
  norm_num

/-- The actual zero-scale angular difference rows are precisely L M. -/
theorem tripleAngularDifference_boundary_eq_LM (alpha : TripleVector)
    (y : TripleChartVariables)
    (hsep : polarPoint (y 0) 0 ≠ polarPoint (y 1) (y 4)) :
    tripleAngularDifference 0 0 alpha y = tripleGapMatrix *ᵥ regularTripleBoundaryM alpha y := by
  ext k
  rw [tripleAngularDifference, tripleAngularExteriorDifference_at_boundary alpha y _ _ hsep,
    tripleInternalAngularDifference, tripleGapMatrix_mulVec_entry,
    tripleGapMatrix_mulVec_entry]
  simp only [regularTripleBoundaryM]
  unfold regularTripleScalarH
  rw [show (tripleChartRadialPositions alpha y k.succ -
        tripleChartRadialPositions alpha y k.castSucc,
      tripleChartAngularPositions alpha y k.succ -
        tripleChartAngularPositions alpha y k.castSucc) =
      (tripleChartRadialPositions alpha y k.succ, tripleChartAngularPositions alpha y k.succ) -
      (tripleChartRadialPositions alpha y k.castSucc, tripleChartAngularPositions alpha y k.castSucc)
      by rfl, map_sub]
  ring

theorem tripleAngularMean_boundary_source_H (alpha : TripleVector)
    (y : TripleChartVariables) (ha : ∑ i, alpha i = 1) :
    tripleAngularMean 0 0 alpha y = -y 1 * y 0 * Real.sin (y 4) *
      (((y 1) ^ 2 + (y 0) ^ 2 - 2 * y 1 * y 0 * Real.cos (y 4)) ^
        (-(3 : ℝ) / 2) - 1) := by
  rw [tripleAngularMean_at_boundary alpha y ha]
  exact regularTripleScalarH_source_formula (y 1) (y 4) (y 0)

end DominantFiveBody
