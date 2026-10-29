import DominantFiveBody.LocalContinuation

/-! Actual closed-simplex coorbital base Jacobian without an artificial
ordering of the reindexed labels. This permits fixing any positive mass. -/

noncomputable section
open scoped BigOperators ContDiff
open Filter Set Topology

namespace DominantFiveBody

theorem isOpen_separatedSemicircle : IsOpen {θ : Satellite → ℝ | SeparatedSemicircle θ} := by
  rw [isOpen_iff_mem_nhds]
  intro θ hθ
  apply Filter.eventually_all.mpr
  intro i
  apply Filter.eventually_all.mpr
  intro j
  by_cases hij : i = j
  · exact Filter.Eventually.of_forall (fun _ h => False.elim (h hij))
  have hn : ∀ᶠ ψ : Satellite → ℝ in 𝓝 θ, ψ i ≠ ψ j :=
    ((isClosed_eq (continuous_apply i) (continuous_apply j)).isOpen_compl).mem_nhds (hθ i j hij).1
  have hd : ∀ᶠ ψ : Satellite → ℝ in 𝓝 θ, |ψ j - ψ i| < Real.pi :=
    (isOpen_lt ((continuous_apply j).sub (continuous_apply i)).abs continuous_const).mem_nhds
      (hθ i j hij).2
  filter_upwards [hn, hd] with ψ hn hd
  exact fun _ => ⟨hn, hd⟩

theorem coorbitalKernel_eq_unit_chord_separated (θ : Satellite → ℝ)
    (hθ : SeparatedSemicircle θ) (i j : Satellite) (hij : i ≠ j) :
    coorbitalKernel (θ j - θ i) = Real.sin (θ j - θ i) *
      ((coorbitalDistance θ i j ^ 3)⁻¹ - 1) := by
  have hne : θ j - θ i ≠ 0 := sub_ne_zero.mpr (hθ i j hij).1.symm
  rcases lt_or_gt_of_ne hne with hneg | hpos
  · have hp : 0 < θ i - θ j := by linarith
    have hpi : θ i - θ j < Real.pi := by simpa only [abs_of_neg hneg, neg_sub] using (hθ i j hij).2
    have hc := unit_circle_chord (θ j) (θ i) hp hpi
    have ht : θ j - θ i = -(θ i - θ j) := by ring
    rw [ht, coorbitalKernel_neg, coorbitalKernel_eq_positive_formula _ hp.le, Real.sin_neg]
    have hd : coorbitalDistance θ i j = 2 * Real.sin ((θ i - θ j) / 2) := by
      rw [coorbitalDistance, norm_sub_rev]
      exact hc
    rw [hd]
    simp only [Coorbital.kernelF, inv_pow, neg_mul]
  · have hpi : θ j - θ i < Real.pi := by simpa only [abs_of_pos hpos] using (hθ i j hij).2
    have hc := unit_circle_chord (θ i) (θ j) hpos hpi
    rw [coorbitalKernel_eq_positive_formula _ hpos.le]
    simp only [Coorbital.kernelF, coorbitalDistance, hc, inv_pow]

theorem angularResidual_zero_unit_separated (μ θ : Satellite → ℝ)
    (hθ : SeparatedSemicircle θ) (i : Satellite) :
    angularResidual 0 μ (fun _ => 1) θ i = coorbitalResidual μ θ i := by
  unfold angularResidual coorbitalResidual
  apply Finset.sum_congr rfl
  intro j hj
  have hij : i ≠ j := Ne.symm (Finset.mem_erase.mp hj).1
  rw [coorbitalKernel_eq_unit_chord_separated θ hθ i j hij]
  have hc : satelliteDistance (polarSatellites (fun _ => 1) θ) i j = coorbitalDistance θ i j := by
    simp [satelliteDistance, polarSatellites, polarPoint, coorbitalDistance]
  rw [hc]
  norm_num
  ring

theorem coorbitalDistance_pos_separated (θ : Satellite → ℝ) (hθ : SeparatedSemicircle θ)
    (i j : Satellite) (hij : i ≠ j) : 0 < coorbitalDistance θ i j := by
  have hne : θ j - θ i ≠ 0 := sub_ne_zero.mpr (hθ i j hij).1.symm
  rcases lt_or_gt_of_ne hne with hneg | hpos
  · have hp : 0 < θ i - θ j := by linarith
    have hpi : θ i - θ j < Real.pi := by simpa only [abs_of_neg hneg, neg_sub] using (hθ i j hij).2
    rw [coorbitalDistance, norm_sub_rev, unit_circle_chord (θ j) (θ i) hp hpi]
    exact mul_pos (by norm_num) (Coorbital.sin_half_pos hp hpi)
  · have hpi : θ j - θ i < Real.pi := by simpa only [abs_of_pos hpos] using (hθ i j hij).2
    rw [coorbitalDistance, unit_circle_chord (θ i) (θ j) hpos hpi]
    exact mul_pos (by norm_num) (Coorbital.sin_half_pos hpos hpi)

theorem sliceRegular_at_coorbital_separated (μ : MassRatio) (y : SliceCoordinates)
    (hunit : ∀ i, sliceRadii y i = 1) (hθ : SeparatedSemicircle (sliceAngles y)) :
    SliceRegular (0, μ) y := by
  refine ⟨by norm_num, fun i => by rw [hunit i]; norm_num, ?_⟩
  intro i j hij
  have hp := coorbitalDistance_pos_separated (sliceAngles y) hθ i j hij
  have heq : coorbitalDistance (sliceAngles y) i j = ‖sliceSatellites y i - sliceSatellites y j‖ := by
    simp [coorbitalDistance, sliceSatellites, polarSatellites, polarPoint, hunit]
  rw [heq] at hp
  intro he
  simp [he] at hp

theorem reducedResidual_at_coorbital_root_separated (μ : MassRatio) (y : SliceCoordinates)
    (hunit : ∀ i, sliceRadii y i = 1) (hθ : SeparatedSemicircle (sliceAngles y))
    (hroot : ∀ i, coorbitalResidual μ (sliceAngles y) i = 0) : reducedResidual (0, μ) y = 0 := by
  have hr : sliceRadii y = fun _ => 1 := funext hunit
  funext k
  refine Fin.addCases (motive := fun k => reducedResidual (0, μ) y k = 0)
    (fun i : Fin 4 => ?_) (fun i : Fin 3 => ?_) k
  · simp [reducedResidual, radialResidual, hunit]
  · simpa only [reducedResidual, Fin.append_right, hr,
      angularResidual_zero_unit_separated μ (sliceAngles y) hθ i.succ] using hroot i.succ

theorem reducedAngularJacobian_zero_eq_separated (μ : MassRatio) (y : SliceCoordinates)
    (hreg : SliceRegular (0, μ) y) (hunit : ∀ i, sliceRadii y i = 1)
    (hθ : SeparatedSemicircle (sliceAngles y)) :
    reducedAngularJacobian (0, μ) y = coorbitalFreeRows.comp
      ((angularDifferential μ (sliceAngles y)).comp coorbitalAngleInjection) := by
  have hc : ContDiff ℝ 1 (fun z : SliceCoordinates => (((0 : ℝ), μ), z)) :=
    contDiff_const.prodMk contDiff_id
  have hd : HasFDerivAt (reducedResidual (0, μ)) (reducedJacobian (0, μ) y) y :=
    ((reducedResidual_joint_contDiffAt 1 (0, μ) y hreg).comp y hc.contDiffAt).differentiableAt
      (by norm_num) |>.hasFDerivAt
  have hinj : HasFDerivAt (fun a : Fin 3 → ℝ => y + sliceAngleInjection a) sliceAngleInjection 0 := by
    simpa using (hasFDerivAt_const y (0 : Fin 3 → ℝ)).add sliceAngleInjection.hasFDerivAt
  have hactual : HasFDerivAt (fun a : Fin 3 → ℝ =>
      sliceFreeAngleProjection (reducedResidual (0, μ) (y + sliceAngleInjection a)))
      (reducedAngularJacobian (0, μ) y) 0 := by
    have hd' : HasFDerivAt (reducedResidual (0, μ)) (reducedJacobian (0, μ) y)
        (y + sliceAngleInjection 0) := by simpa only [map_zero, add_zero] using hd
    convert! sliceFreeAngleProjection.hasFDerivAt.comp 0 (hd'.comp 0 hinj) using 1
  have hangles : HasFDerivAt (fun a : Fin 3 → ℝ => sliceAngles (y + sliceAngleInjection a))
      coorbitalAngleInjection 0 := by
    convert! sliceAnglesLinear.hasFDerivAt.comp 0 hinj using 1
    · funext a; exact (sliceAnglesLinear_apply _).symm
    · exact sliceAnglesLinear_comp_injection.symm
  have hco := coorbitalResidual_hasFDerivAt μ (sliceAngles y) hθ
  have hco' : HasFDerivAt (fun a : Fin 3 → ℝ => coorbitalFreeRows
      (fun i => coorbitalResidual μ (sliceAngles (y + sliceAngleInjection a)) i))
      (coorbitalFreeRows.comp ((angularDifferential μ (sliceAngles y)).comp coorbitalAngleInjection)) 0 := by
    have hcoAt : HasFDerivAt (fun angles i => coorbitalResidual μ angles i)
        (angularDifferential μ (sliceAngles y)) (sliceAngles (y + sliceAngleInjection 0)) := by
      simpa only [map_zero, add_zero] using hco
    convert! coorbitalFreeRows.hasFDerivAt.comp 0 (hcoAt.comp 0 hangles) using 1
  have hnear : ∀ᶠ a : Fin 3 → ℝ in 𝓝 0, SeparatedSemicircle (sliceAngles (y + sliceAngleInjection a)) := by
    have hbase : SeparatedSemicircle (sliceAngles (y + sliceAngleInjection 0)) := by
      simpa only [map_zero, add_zero] using hθ
    have h := hangles.continuousAt.tendsto.eventually (isOpen_separatedSemicircle.mem_nhds hbase)
    simpa only [map_zero, add_zero] using h
  have heq : (fun a : Fin 3 → ℝ =>
      sliceFreeAngleProjection (reducedResidual (0, μ) (y + sliceAngleInjection a))) =ᶠ[𝓝 0]
      (fun a => coorbitalFreeRows (fun i => coorbitalResidual μ (sliceAngles (y + sliceAngleInjection a)) i)) := by
    filter_upwards [hnear] with a ha
    have hr : sliceRadii (y + sliceAngleInjection a) = fun _ => 1 := by
      funext i; simp [sliceRadii, ← hunit i]
    funext i
    simp only [sliceFreeAngleProjection_apply, reducedResidual, Fin.append_right, hr,
      coorbitalFreeRows, ContinuousLinearMap.pi_apply, ContinuousLinearMap.proj_apply]
    exact angularResidual_zero_unit_separated μ _ ha i.succ
  exact hactual.unique (hco'.congr_of_eventuallyEq heq)

/-- Complete closed-mass base invertibility at any anchored separated
root. Only the actually omitted mass must be positive. -/
theorem reducedJacobian_at_closed_separated_root_isInvertible (μ : MassRatio) (y : SliceCoordinates)
    (hunit : ∀ i, sliceRadii y i = 1) (hμ : ∀ i, 0 ≤ μ i) (hsum : ∑ i, μ i = 1)
    (hμ₀ : 0 < μ 0) (hθ : SeparatedSemicircle (sliceAngles y))
    (hroot : ∀ i, coorbitalResidual μ (sliceAngles y) i = 0) :
    (reducedJacobian (0, μ) y).IsInvertible := by
  have hreg := sliceRegular_at_coorbital_separated μ y hunit hθ
  apply reducedJacobian_zero_isInvertible_of_angular μ y hreg hunit
  apply euclidean_clm_isInvertible_of_injective
  intro a b hab
  have hzero : reducedAngularJacobian (0, μ) y (a - b) = 0 := by rw [map_sub, hab, sub_self]
  rw [reducedAngularJacobian_zero_eq_separated μ y hreg hunit hθ] at hzero
  let u := coorbitalAngleInjection (a - b)
  have hothers : ∀ i : Satellite, i ≠ 0 → angularDifferential μ (sliceAngles y) u i = 0 := by
    intro i hi
    obtain ⟨j, rfl⟩ := Fin.exists_succAbove_eq hi
    have h := congrFun hzero j
    simpa [coorbitalFreeRows, u] using h
  have hfull : angularDifferential μ (sliceAngles y) u = 0 := by
    funext i
    by_cases hi : i = 0
    · subst i; exact angularDifferential_recover_row μ (sliceAngles y) u 0 hμ₀ hothers
    · exact hothers i hi
  have hconstant := (angularDifferential_kernel_iff_separated_nonnegative μ (sliceAngles y) u
    hμ hsum hθ hroot).mp hfull
  funext j
  have h := hconstant j.succ 0
  simpa [u, sub_eq_zero] using h

end DominantFiveBody
