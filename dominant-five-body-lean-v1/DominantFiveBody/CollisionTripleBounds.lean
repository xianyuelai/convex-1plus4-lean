import DominantFiveBody.CollisionTripleField

/-! # Initial quantitative bounds for a complete triple

All masses in the extreme angular rows are current masses. The estimates
below never divide by an individual triple mass share.
-/

noncomputable section
open scoped BigOperators Matrix ContDiff
open Filter Set Topology

namespace DominantFiveBody
set_option maxHeartbeats 800000

def tripleAngularCoefficient (eps : ℝ) (r theta : Satellite → ℝ) (i j : Satellite) : ℝ :=
  r i * r j * Real.sinc (theta j - theta i) *
    ((satelliteDistance (polarSatellites r theta) i j ^ 3)⁻¹ - (1 + eps)⁻¹)

theorem fullAngularMatrix_eq_gap_coefficient (eps : ℝ) (r theta : Satellite → ℝ)
    (i j : Satellite) :
    fullAngularMatrix eps r theta i j = (theta j - theta i) * tripleAngularCoefficient eps r theta i j := by
  unfold fullAngularMatrix tripleAngularCoefficient
  rw [← sinc_mul_argument (theta j - theta i)]
  ring

theorem tripleAngularCoefficient_reverse (eps : ℝ) (r theta : Satellite → ℝ)
    (i j : Satellite) : tripleAngularCoefficient eps r theta j i = tripleAngularCoefficient eps r theta i j := by
  have hg : theta i - theta j = -(theta j - theta i) := by ring
  have hd : satelliteDistance (polarSatellites r theta) j i =
      satelliteDistance (polarSatellites r theta) i j := norm_sub_rev _ _
  unfold tripleAngularCoefficient
  rw [hg, Real.sinc_neg, hd]
  ring

theorem tripleAngularCoefficient_lower (eps d : ℝ) (r theta : Satellite → ℝ)
    (i j : Satellite) (heps : 0 ≤ eps) (hd : 0 < d) (hsmall : d ≤ 1 / 4)
    (hra : (1 / 2 : ℝ) ≤ r i) (hrb : (1 / 2 : ℝ) ≤ r j)
    (hsinc : (1 / 2 : ℝ) ≤ Real.sinc (theta j - theta i))
    (hsep : 0 < satelliteDistance (polarSatellites r theta) i j)
    (hdiam : satelliteDistance (polarSatellites r theta) i j ≤ d) :
    1 / (16 * d ^ 3) ≤ tripleAngularCoefficient eps r theta i j := by
  have hrprod : (1 / 4 : ℝ) ≤ r i * r j := by nlinarith [mul_le_mul hra hrb (by norm_num) (by linarith : 0 ≤ r i)]
  have hc : (1 + eps)⁻¹ ≤ (1 : ℝ) := by
    apply (inv_le_one₀ (by linarith : 0 < 1 + eps)).mpr
    linarith
  have hd3 : 0 < d ^ 3 := pow_pos hd 3
  have hdist3 : 0 < satelliteDistance (polarSatellites r theta) i j ^ 3 := pow_pos hsep 3
  have hpow := pow_le_pow_left₀ hsep.le hdiam 3
  have hinv : (d ^ 3)⁻¹ ≤ (satelliteDistance (polarSatellites r theta) i j ^ 3)⁻¹ :=
    inv_anti₀ hdist3 hpow
  have hdsmall : d ^ 3 ≤ 1 / 2 := by
    have ht := pow_le_pow_left₀ hd.le hsmall 3
    norm_num at ht
    linarith
  have hhalf : 1 / (2 * d ^ 3) ≤ (d ^ 3)⁻¹ - 1 := by
    apply (div_le_iff₀ (by positivity : 0 < 2 * d ^ 3)).mpr
    have he : ((d ^ 3)⁻¹ - 1) * (2 * d ^ 3) = 2 - 2 * d ^ 3 := by
      field_simp
    rw [he]
    nlinarith
  have hco : 1 / (2 * d ^ 3) ≤ (satelliteDistance (polarSatellites r theta) i j ^ 3)⁻¹ - (1 + eps)⁻¹ := by
    linarith
  have hmul : (1 / 8 : ℝ) ≤ r i * r j * Real.sinc (theta j - theta i) := by
    have h := mul_le_mul hrprod hsinc (by norm_num : (0 : ℝ) ≤ 1 / 2)
      (by nlinarith [hra] : 0 ≤ r i * r j)
    norm_num at h
    exact h
  have h := mul_le_mul hmul hco (by positivity : 0 ≤ 1 / (2 * d ^ 3))
    (by linarith : 0 ≤ r i * r j * Real.sinc (theta j - theta i))
  unfold tripleAngularCoefficient
  convert! h using 1
  ring

/-- Exact first-minus-last angular identity of the complete lower triple.
The internal masses multiply angular gaps whose sum is the full width. -/
theorem physical_triple_extreme_angular_identity (eps : ℝ) (mu r theta : Satellite → ℝ)
    (hroot : ∀ i, angularResidual eps mu r theta i = 0) :
    mu 3 * (physicalSourceFullAngularField eps (r 3) (theta 3) (r 2) (theta 2) -
      physicalSourceFullAngularField eps (r 3) (theta 3) (r 0) (theta 0)) =
      (mu 0 + mu 2) * (theta 2 - theta 0) * tripleAngularCoefficient eps r theta 0 2 +
        mu 1 * ((theta 1 - theta 0) * tripleAngularCoefficient eps r theta 0 1 +
          (theta 2 - theta 1) * tripleAngularCoefficient eps r theta 1 2) := by
  have h0 := hroot 0
  have h2 := hroot 2
  rw [angularResidual_eq_full_matrix_sum, Fin.sum_univ_four] at h0 h2
  simp only [fullAngularMatrix_self, mul_zero, zero_add, add_zero] at h0 h2
  rw [fullAngularMatrix_reverse eps r theta 0 2, fullAngularMatrix_reverse eps r theta 1 2] at h2
  simp only [fullAngularMatrix_eq_physicalSourceFullAngularField] at h0 h2
  have h01 := fullAngularMatrix_eq_gap_coefficient eps r theta 0 1
  have h02 := fullAngularMatrix_eq_gap_coefficient eps r theta 0 2
  have h12 := fullAngularMatrix_eq_gap_coefficient eps r theta 1 2
  simp only [fullAngularMatrix_eq_physicalSourceFullAngularField] at h01 h02 h12
  rw [h01, h02] at h0
  rw [h02, h12] at h2
  linarith

theorem triple_mass_cube_upper_of_extreme_rows (eps d C : ℝ) (mu r theta : Satellite → ℝ)
    (hm : PositiveRatio mu) (_hd : 0 < d)
    (hgap01 : 0 < theta 1 - theta 0) (hgap12 : 0 < theta 2 - theta 1)
    (hco01 : 1 / (16 * d ^ 3) ≤ tripleAngularCoefficient eps r theta 0 1)
    (hco02 : 1 / (16 * d ^ 3) ≤ tripleAngularCoefficient eps r theta 0 2)
    (hco12 : 1 / (16 * d ^ 3) ≤ tripleAngularCoefficient eps r theta 1 2)
    (hroot : ∀ i, angularResidual eps mu r theta i = 0)
    (hJ : physicalSourceFullAngularField eps (r 3) (theta 3) (r 2) (theta 2) -
      physicalSourceFullAngularField eps (r 3) (theta 3) (r 0) (theta 0) ≤
        C * (theta 2 - theta 0)) :
    (mu 0 + mu 1 + mu 2) / d ^ 3 ≤ 16 * C * mu 3 := by
  have hwidth : 0 < theta 2 - theta 0 := by linarith
  have hlow01 := mul_le_mul_of_nonneg_left hco01 hgap01.le
  have hlow02 := mul_le_mul_of_nonneg_left hco02 hwidth.le
  have hlow12 := mul_le_mul_of_nonneg_left hco12 hgap12.le
  have hlow0 := mul_le_mul_of_nonneg_left hlow02 (add_pos (hm.1 0) (hm.1 2)).le
  have hlow1 := mul_le_mul_of_nonneg_left (add_le_add hlow01 hlow12) (hm.1 1).le
  have hidentity := physical_triple_extreme_angular_identity eps mu r theta hroot
  have hupper := mul_le_mul_of_nonneg_left hJ (hm.1 3).le
  have hlow : (mu 0 + mu 1 + mu 2) * (theta 2 - theta 0) / (16 * d ^ 3) ≤
      mu 3 * (physicalSourceFullAngularField eps (r 3) (theta 3) (r 2) (theta 2) -
        physicalSourceFullAngularField eps (r 3) (theta 3) (r 0) (theta 0)) := by
    rw [hidentity]
    convert! add_le_add hlow0 hlow1 using 1 <;> ring
  have h := hlow.trans hupper
  apply (mul_le_mul_iff_right₀ hwidth).mp
  have hscaled := mul_le_mul_of_nonneg_left h (show (0 : ℝ) ≤ 16 by norm_num)
  convert! hscaled using 1 <;> ring

theorem polar_support_triangle_formula (ra rb rp va vb vp : ℝ) :
    det2 (polarPoint rb vb - polarPoint ra va) (polarPoint rp vp - polarPoint ra va) =
      rb * rp * Real.sin (vp - vb) - ra * rp * Real.sin (vp - va) + ra * rb * Real.sin (vb - va) := by
  simp [det2, polarPoint, point, Real.sin_sub]
  ring

/-- The actual exterior support inequality prevents a large radial drop
along an ordered internal edge. All constants are mass-independent. -/
theorem polar_support_radial_drop_le (ra rb rp va vb vp : ℝ)
    (hra : (1 / 2 : ℝ) ≤ ra) (hrb : (1 / 2 : ℝ) ≤ rb) (hrp : (1 / 2 : ℝ) ≤ rp)
    (hra2 : ra ≤ 2) (hrb2 : rb ≤ 2) (hrp2 : rp ≤ 2)
    (hangle : 0 < vb - va) (hsin : (1 / 2 : ℝ) ≤ Real.sin (vp - vb))
    (hsupport : 0 < det2 (polarPoint rb vb - polarPoint ra va) (polarPoint rp vp - polarPoint ra va)) :
    ra - rb ≤ 32 * (vb - va) := by
  by_cases hdrop : ra ≤ rb
  · linarith
  have hdr : 0 < ra - rb := by linarith
  have hprod : (1 / 4 : ℝ) ≤ rp * Real.sin (vp - vb) := by
    have hmul := mul_le_mul hrp hsin (by norm_num : (0 : ℝ) ≤ 1 / 2) (by linarith : 0 ≤ rp)
    norm_num at hmul
    exact hmul
  have hsinDiff : Real.sin (vp - vb) - Real.sin (vp - va) ≤ vb - va := by
    have h := (le_abs_self _).trans (Real.abs_sin_sub_sin_le (vp - vb) (vp - va))
    have he : vp - vb - (vp - va) = -(vb - va) := by ring
    simpa only [he, abs_neg, abs_of_pos hangle] using h
  have hsinGap : Real.sin (vb - va) ≤ vb - va := Real.sin_le hangle.le
  have hrap : 0 ≤ ra * rp := by positivity
  have hrab : 0 ≤ ra * rb := by positivity
  have hrap2 : ra * rp ≤ 4 := by nlinarith [mul_le_mul hra2 hrp2 (by linarith : 0 ≤ rp) (by norm_num : (0 : ℝ) ≤ 2)]
  have hrab2 : ra * rb ≤ 4 := by nlinarith [mul_le_mul hra2 hrb2 (by linarith : 0 ≤ rb) (by norm_num : (0 : ℝ) ≤ 2)]
  have herror1 := mul_le_mul_of_nonneg_left hsinDiff hrap
  have herror2 := mul_le_mul_of_nonneg_left hsinGap hrab
  have herror1up := mul_le_mul_of_nonneg_right hrap2 hangle.le
  have herror2up := mul_le_mul_of_nonneg_right hrab2 hangle.le
  have hdropLower := mul_le_mul_of_nonneg_left hprod hdr.le
  rw [polar_support_triangle_formula] at hsupport
  nlinarith

/-- Adjacent exterior support bounds and the real monotone-field bound
control every internal radial difference by the full angular width. -/
theorem three_radii_spread_le_width (ra rb rc va vb vc S K : ℝ)
    (hS : 0 ≤ S) (hK : 0 ≤ K) (hab : va < vb) (hbc : vb < vc)
    (hdrop01 : ra - rb ≤ S * (vb - va)) (hdrop12 : rb - rc ≤ S * (vc - vb))
    (hup02 : ra ≤ rc → rc - ra ≤ K * (vc - va)) :
    |rb - ra| ≤ (K + 2 * S) * (vc - va) ∧
      |rc - ra| ≤ (K + 2 * S) * (vc - va) ∧
      |rc - rb| ≤ (K + 2 * S) * (vc - va) := by
  have hW : 0 < vc - va := by linarith
  have h01 : 0 ≤ vb - va := by linarith
  have h12 : 0 ≤ vc - vb := by linarith
  have h01W := mul_le_mul_of_nonneg_left (by linarith : vb - va ≤ vc - va) hS
  have h12W := mul_le_mul_of_nonneg_left (by linarith : vc - vb ≤ vc - va) hS
  have hendpoint : rc - ra ≤ K * (vc - va) := by
    by_cases hac : ra ≤ rc
    · exact hup02 hac
    · nlinarith
  have hKw : 0 ≤ K * (vc - va) := mul_nonneg hK hW.le
  have hSw : 0 ≤ S * (vc - va) := mul_nonneg hS hW.le
  constructor
  · apply abs_le.mpr
    constructor <;> linarith
  · constructor
    · apply abs_le.mpr
      constructor <;> nlinarith
    · apply abs_le.mpr
      constructor <;> nlinarith

end DominantFiveBody
