import DominantFiveBody.NestedBoundaryDeterminant
import Mathlib.Analysis.Calculus.Deriv.Abs

/-! All original angular-block entries, including the off-diagonal terms. -/

noncomputable section
open scoped Matrix
open Filter Set Topology
namespace DominantFiveBody
open Coorbital
set_option maxHeartbeats 1000000

theorem kappaPrime_h_source : kappaPrime h = -(27 / 4 : ℝ) * Real.sin h := by
  have he : h / 2 = Real.pi / 6 := by unfold h; ring
  unfold kappaPrime
  rw [he, Real.sin_pi_div_six, Real.cos_pi_div_six]
  unfold h
  rw [Real.sin_pi_div_three]
  norm_num
  ring

theorem kappa_abs_equilateral_hasDerivAt (psi : ℝ) (hangle : |psi| = h) :
    HasDerivAt (fun x : ℝ => kappa |x|) (-(27 / 4 : ℝ) * Real.sin psi) psi := by
  have hh : 0 < h := by unfold h; positivity
  have hp : h < Real.pi := by unfold h; linarith [Real.pi_pos]
  have hcases : psi = h ∨ psi = -h :=
    abs_eq_abs.mp (hangle.trans (abs_of_pos hh).symm)
  rcases hcases with rfl | rfl
  · convert! (kappa_hasDerivAt hh hp).comp_of_eq h (hasDerivAt_abs_pos hh)
      (abs_of_pos hh).symm using 1
    simp only [kappaPrime_h_source, mul_one]
  · convert!
      (kappa_hasDerivAt hh hp).comp_of_eq (-h) (hasDerivAt_abs_neg (neg_neg_of_pos hh))
        (by rw [abs_neg, abs_of_pos hh]) using 1
    simp only [kappaPrime_h_source, Real.sin_neg]
    ring

theorem twice_inverse_abs_cube_hasDerivAt (Z : ℝ) (hZ : Z ≠ 0) :
    HasDerivAt (fun r : ℝ => 2 / |r| ^ 3) (-6 / (|Z| ^ 3 * Z)) Z := by
  have hd := ((tripleScalarForce_hasDerivAt hZ).const_mul 2).div (hasDerivAt_id Z) hZ
  have hn : ∀ᶠ r : ℝ in 𝓝 Z, r ≠ 0 :=
    (isClosed_eq continuous_id continuous_const).isOpen_compl.mem_nhds hZ
  have he : (fun r : ℝ => 2 / |r| ^ 3) =ᶠ[𝓝 Z] (fun r => 2 * tripleScalarForce r / r) := by
    filter_upwards [hn] with r hr
    unfold tripleScalarForce
    field_simp
  convert! hd.congr_of_eventuallyEq he using 1
  unfold tripleScalarForce
  simp only [id_eq]
  field_simp [hZ]
  ring

theorem nestedChartJacobian_unit_outer_full (alpha psi Z z : ℝ)
    (hreg : NestedChartRegular 0 0 0 alpha (nestedUnitPoint psi Z z))
    (hangle : |psi| = h) (hZ : Z ≠ 0) (v : NestedChartVariables)
    (hv0 : v 0 = 0) (hv1 : v 1 = 0) (hv2 : v 2 = 0) (hv3 : v 3 = 0) :
    nestedChartJacobian 0 0 0 alpha (nestedUnitPoint psi Z z) v 5 =
      (-(27 / 4 : ℝ) * Real.sin psi) * Z * v 4 +
        (kappa |psi| + 2 / |Z| ^ 3) * v 5 := by
  obtain ⟨hpsi, hpi, _, _⟩ := tripleBoundaryAngle_facts psi hangle
  have hp : HasDerivAt (fun s : ℝ => psi + s * v 4) (v 4) 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).mul_const (v 4)).const_add psi
  have hq : HasDerivAt (fun s : ℝ => Z + s * v 5) (v 5) 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).mul_const (v 5)).const_add Z
  have hk := (kappa_abs_equilateral_hasDerivAt psi hangle).comp_of_eq 0 hp (by simp)
  have hs := (tripleScalarForce_hasDerivAt hZ).comp_of_eq 0 hq (by simp)
  have hd := (hk.mul hq).sub hs
  apply nestedChartJacobian_apply_of_hasDerivAt _ _ _ _ _ _ hreg 5
  have he : (fun s : ℝ => nestedChartExtendedRows 0 0 0 alpha
      (nestedUnitPoint psi Z z + s • v) 5) =ᶠ[𝓝 0]
      (fun s => kappa |psi + s * v 4| * (Z + s * v 5) - tripleScalarForce (Z + s * v 5)) := by
    have hn : ∀ᶠ s : ℝ in 𝓝 0, psi + s * v 4 ≠ 0 :=
      (isClosed_eq (by fun_prop) continuous_const).isOpen_compl.mem_nhds (by simpa using hpsi)
    have hpi' : ∀ᶠ s : ℝ in 𝓝 0, |psi + s * v 4| < Real.pi :=
      (isOpen_lt (by fun_prop) continuous_const).mem_nhds (by simpa using hpi)
    filter_upwards [hn, hpi'] with s hn hs
    change nestedAngularOuterDifference 0 0 0 alpha (nestedUnitPoint psi Z z + s • v) = _
    rw [nestedUnitPoint_line _ _ _ _ _ hv0 hv1 hv2 hv3]
    exact nestedAngularOuterDifference_unit_boundary alpha _ _ _ hn hs
  convert! hd.congr_of_eventuallyEq he using 1
  simp only [Function.comp_apply, zero_mul, add_zero]
  ring

theorem nestedChartJacobian_unit_inner_full (alpha psi Z z : ℝ)
    (hreg : NestedChartRegular 0 0 0 alpha (nestedUnitPoint psi Z z))
    (hangle : |psi| = h) (hZ : Z ≠ 0) (hz : z ≠ 0) (v : NestedChartVariables)
    (hv0 : v 0 = 0) (hv1 : v 1 = 0) (hv2 : v 2 = 0) (hv3 : v 3 = 0) :
    nestedChartJacobian 0 0 0 alpha (nestedUnitPoint psi Z z) v 6 =
      (-(27 / 4 : ℝ) * Real.sin psi) * z * v 4 -
        6 / (|Z| ^ 3 * Z) * z * v 5 +
          (kappa |psi| + 2 / |Z| ^ 3 + 2 / |z| ^ 3) * v 6 := by
  obtain ⟨hpsi, hpi, _, _⟩ := tripleBoundaryAngle_facts psi hangle
  have hp : HasDerivAt (fun s : ℝ => psi + s * v 4) (v 4) 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).mul_const (v 4)).const_add psi
  have hQ : HasDerivAt (fun s : ℝ => Z + s * v 5) (v 5) 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).mul_const (v 5)).const_add Z
  have hq : HasDerivAt (fun s : ℝ => z + s * v 6) (v 6) 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).mul_const (v 6)).const_add z
  have hk := (kappa_abs_equilateral_hasDerivAt psi hangle).comp_of_eq 0 hp (by simp)
  have hI := (twice_inverse_abs_cube_hasDerivAt Z hZ).comp_of_eq 0 hQ (by simp)
  have hs := (tripleScalarForce_hasDerivAt hz).comp_of_eq 0 hq (by simp)
  have hd := ((hk.mul hq).add (hI.mul hq)).sub hs
  apply nestedChartJacobian_apply_of_hasDerivAt _ _ _ _ _ _ hreg 6
  have he : (fun s : ℝ => nestedChartExtendedRows 0 0 0 alpha
      (nestedUnitPoint psi Z z + s • v) 6) =ᶠ[𝓝 0]
      (fun s => kappa |psi + s * v 4| * (z + s * v 6) +
        2 / |Z + s * v 5| ^ 3 * (z + s * v 6) - tripleScalarForce (z + s * v 6)) := by
    have hn : ∀ᶠ s : ℝ in 𝓝 0, psi + s * v 4 ≠ 0 :=
      (isClosed_eq (by fun_prop) continuous_const).isOpen_compl.mem_nhds (by simpa using hpsi)
    have hpi' : ∀ᶠ s : ℝ in 𝓝 0, |psi + s * v 4| < Real.pi :=
      (isOpen_lt (by fun_prop) continuous_const).mem_nhds (by simpa using hpi)
    have hQ' : ∀ᶠ s : ℝ in 𝓝 0, Z + s * v 5 ≠ 0 :=
      (isClosed_eq (by fun_prop) continuous_const).isOpen_compl.mem_nhds (by simpa using hZ)
    filter_upwards [hn, hpi', hQ'] with s hn hs hQ'
    change nestedAngularInnerDifference 0 0 0 alpha (nestedUnitPoint psi Z z + s • v) = _
    rw [nestedUnitPoint_line _ _ _ _ _ hv0 hv1 hv2 hv3]
    exact nestedAngularInnerDifference_unit_boundary alpha _ _ _ hn hs hQ'
  convert! hd.congr_of_eventuallyEq he using 1
  simp only [Function.comp_apply, zero_mul, add_zero]
  ring

def nestedAngularBasisIndex : Fin 3 → Fin 7 := ![4, 5, 6]

def nestedAngularBoundaryMatrix (alpha psi omega : ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  fun i j => nestedChartJacobian 0 0 0 alpha (nestedBasePoint psi omega)
    ![0, 0, 0, 0, if j = 0 then 1 else 0, if j = 1 then 1 else 0,
      if j = 2 then 1 else 0] (nestedAngularBasisIndex i)

theorem nestedAngularBoundaryMatrix_source (alpha psi omega : ℝ)
    (hangle : |psi| = h) (hw : |omega| = 1) :
    let Z := omega * pairBoundaryScale tripleD0
    let z := pairBoundaryScale (3 * tripleD0)
    let C := -(27 / 4 : ℝ) * Real.sin psi
    nestedAngularBoundaryMatrix alpha psi omega =
      ![![tripleD0, 0, 0], ![C * Z, 3 * tripleD0, 0],
        ![C * z, -6 * tripleD0 * z / Z, 9 * tripleD0]] := by
  let Z := omega * pairBoundaryScale tripleD0
  let z := pairBoundaryScale (3 * tripleD0)
  let C := -(27 / 4 : ℝ) * Real.sin psi
  obtain ⟨hpsi, hpi, _, hD⟩ := tripleBoundaryAngle_facts psi hangle
  have hreg := nestedBasePoint_regular alpha psi omega hangle hw
  have hZ : Z ≠ 0 := nestedBasePoint_outer_ne_zero omega hw
  have hz : z ≠ 0 := (pairBoundaryScale_pos (3 * tripleD0)
    (mul_pos (by norm_num) tripleD0_pos)).ne'
  obtain ⟨hZscale, hzscale⟩ := nestedBasePoint_diagonal_scales omega hw
  have hcoef : 6 / (|Z| ^ 3 * Z) = 6 * tripleD0 / Z := by
    calc
      _ = 3 * (2 / |Z| ^ 3) / Z := by ring
      _ = _ := by rw [hZscale]; ring
  have hm (v : NestedChartVariables) (hv0 : v 0 = 0) (hv1 : v 1 = 0)
      (hv2 : v 2 = 0) (hv3 : v 3 = 0) :
      nestedChartJacobian 0 0 0 alpha (nestedBasePoint psi omega) v 4 = tripleD0 * v 4 := by
    exact (nestedChartJacobian_unit_mean alpha psi Z z hreg hpsi hpi v hv0 hv1 hv2 hv3).trans
      (by rw [hD])
  have ho (v : NestedChartVariables) (hv0 : v 0 = 0) (hv1 : v 1 = 0)
      (hv2 : v 2 = 0) (hv3 : v 3 = 0) :
      nestedChartJacobian 0 0 0 alpha (nestedBasePoint psi omega) v 5 =
        C * Z * v 4 + 3 * tripleD0 * v 5 := by
    rw [nestedBasePoint]
    rw [nestedChartJacobian_unit_outer_full alpha psi Z z hreg hangle hZ v hv0 hv1 hv2 hv3]
    rw [hD, hZscale]
    change C * Z * v 4 + (tripleD0 + 2 * tripleD0) * v 5 = _
    ring
  have hi (v : NestedChartVariables) (hv0 : v 0 = 0) (hv1 : v 1 = 0)
      (hv2 : v 2 = 0) (hv3 : v 3 = 0) :
      nestedChartJacobian 0 0 0 alpha (nestedBasePoint psi omega) v 6 =
        C * z * v 4 - 6 * tripleD0 * z / Z * v 5 + 9 * tripleD0 * v 6 := by
    rw [nestedBasePoint]
    rw [nestedChartJacobian_unit_inner_full alpha psi Z z hreg hangle hZ hz v hv0 hv1 hv2 hv3]
    rw [hD, hZscale, hzscale, hcoef]
    change C * z * v 4 - 6 * tripleD0 / Z * z * v 5 +
      (tripleD0 + 2 * tripleD0 + 6 * tripleD0) * v 6 = _
    ring
  change nestedAngularBoundaryMatrix alpha psi omega =
    ![![tripleD0, 0, 0], ![C * Z, 3 * tripleD0, 0],
      ![C * z, -6 * tripleD0 * z / Z, 9 * tripleD0]]
  ext i j
  fin_cases i
  · fin_cases j
    · simpa [nestedAngularBoundaryMatrix, nestedAngularBasisIndex] using
        (hm ![0, 0, 0, 0, 1, 0, 0] rfl rfl rfl rfl)
    · simpa [nestedAngularBoundaryMatrix, nestedAngularBasisIndex] using
        (hm ![0, 0, 0, 0, 0, 1, 0] rfl rfl rfl rfl)
    · simpa [nestedAngularBoundaryMatrix, nestedAngularBasisIndex] using
        (hm ![0, 0, 0, 0, 0, 0, 1] rfl rfl rfl rfl)
  · fin_cases j
    · simpa [nestedAngularBoundaryMatrix, nestedAngularBasisIndex] using
        (ho ![0, 0, 0, 0, 1, 0, 0] rfl rfl rfl rfl)
    · simpa [nestedAngularBoundaryMatrix, nestedAngularBasisIndex] using
        (ho ![0, 0, 0, 0, 0, 1, 0] rfl rfl rfl rfl)
    · simpa [nestedAngularBoundaryMatrix, nestedAngularBasisIndex] using
        (ho ![0, 0, 0, 0, 0, 0, 1] rfl rfl rfl rfl)
  · fin_cases j
    · simpa [nestedAngularBoundaryMatrix, nestedAngularBasisIndex] using
        (hi ![0, 0, 0, 0, 1, 0, 0] rfl rfl rfl rfl)
    · simpa [nestedAngularBoundaryMatrix, nestedAngularBasisIndex, neg_div] using
        (hi ![0, 0, 0, 0, 0, 1, 0] rfl rfl rfl rfl)
    · simpa [nestedAngularBoundaryMatrix, nestedAngularBasisIndex] using
        (hi ![0, 0, 0, 0, 0, 0, 1] rfl rfl rfl rfl)

end DominantFiveBody
