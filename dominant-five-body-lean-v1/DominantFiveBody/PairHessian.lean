import DominantFiveBody.FixedAngleRows
import DominantFiveBody.PairJacobian
import DominantFiveBody.PairRecovery

/-! # The actual pair-chart Jacobian and the original shape Hessian

Both coordinate and row maps have explicit inverses for `t ≠ 0`.  The
fixed physical angle is the original satellite c (index 2).  The
nondegeneracy conclusion refers to the original centered configuration
and its six-dimensional shape space.
-/

noncomputable section
open scoped BigOperators ContDiff
open Filter Set Topology

namespace DominantFiveBody

def pairVariableProjection (i : Fin 7) : PairChartVariables →L[ℝ] ℝ :=
  ContinuousLinearMap.proj i

/-- Pair unknowns `(ρc,ρd,R,u,ω,ψ,z)` in the chart fixing original angle c.
The radial order in this fixed-angle chart is `(c,b,a,d)`. -/
def pairToFixedSlice (t alpha : ℝ) : PairChartVariables →L[ℝ] SliceCoordinates :=
  ContinuousLinearMap.pi ![
    pairVariableProjection 0,
    pairVariableProjection 2 + (alpha*t) • pairVariableProjection 3,
    pairVariableProjection 2 - ((1-alpha)*t) • pairVariableProjection 3,
    pairVariableProjection 1,
    pairVariableProjection 5 + (alpha*t) • pairVariableProjection 6,
    pairVariableProjection 5 - ((1-alpha)*t) • pairVariableProjection 6,
    pairVariableProjection 4]

def pairFromFixedSlice (t alpha : ℝ) : SliceCoordinates →L[ℝ] PairChartVariables :=
  ContinuousLinearMap.pi ![
    pairVariableProjection 0,
    pairVariableProjection 3,
    alpha • pairVariableProjection 2 + (1-alpha) • pairVariableProjection 1,
    t⁻¹ • (pairVariableProjection 1 - pairVariableProjection 2),
    pairVariableProjection 6,
    alpha • pairVariableProjection 5 + (1-alpha) • pairVariableProjection 4,
    t⁻¹ • (pairVariableProjection 4 - pairVariableProjection 5)]

theorem pairFromFixedSlice_pairToFixedSlice (t alpha : ℝ) (ht : t≠0)
    (y : PairChartVariables) : pairFromFixedSlice t alpha (pairToFixedSlice t alpha y)=y := by
  ext i
  fin_cases i <;> simp [pairFromFixedSlice,pairToFixedSlice,smul_eq_mul,pairVariableProjection]
  all_goals field_simp [ht]
  all_goals ring

theorem pairToFixedSlice_pairFromFixedSlice (t alpha : ℝ) (ht : t≠0)
    (y : SliceCoordinates) : pairToFixedSlice t alpha (pairFromFixedSlice t alpha y)=y := by
  ext i
  fin_cases i <;> simp [pairFromFixedSlice,pairToFixedSlice,smul_eq_mul,pairVariableProjection]
  all_goals field_simp [ht]
  all_goals ring

theorem pairToFixedSlice_isInvertible (t alpha : ℝ) (ht : t≠0) :
    (pairToFixedSlice t alpha).IsInvertible := by
  apply euclidean_clm_isInvertible_of_injective
  intro a b hab
  have h := congrArg (pairFromFixedSlice t alpha) hab
  simpa only [pairFromFixedSlice_pairToFixedSlice t alpha ht] using h

/-- Raw radial rows `(Rc,Rb,Ra,Rd)` and raw angular rows either
`(Tb,Ta,Td)` or `(Tc,Tb,Ta)` are the actual retained fixed-angle rows. -/
def pairFixedRowTransform (t alpha : ℝ) (keepD : Bool) :
    SliceCoordinates →L[ℝ] PairChartVariables :=
  let b : Fin 7 := if keepD then 4 else 5
  let a : Fin 7 := if keepD then 5 else 6
  let k : Fin 7 := if keepD then 6 else 4
  ContinuousLinearMap.pi ![
    pairVariableProjection 0,
    pairVariableProjection 3,
    alpha • pairVariableProjection 2 + (1-alpha) • pairVariableProjection 1,
    t⁻¹ • (pairVariableProjection 1 - pairVariableProjection 2),
    pairVariableProjection k,
    alpha • pairVariableProjection a + (1-alpha) • pairVariableProjection b,
    t⁻¹ • (pairVariableProjection b - pairVariableProjection a)]

def pairFixedRowInverse (t alpha : ℝ) (keepD : Bool) :
    PairChartVariables →L[ℝ] SliceCoordinates :=
  let Tb := pairVariableProjection 5 + (alpha*t) • pairVariableProjection 6
  let Ta := pairVariableProjection 5 - ((1-alpha)*t) • pairVariableProjection 6
  let Tk := pairVariableProjection 4
  ContinuousLinearMap.pi ![
    pairVariableProjection 0,
    pairVariableProjection 2 + (alpha*t) • pairVariableProjection 3,
    pairVariableProjection 2 - ((1-alpha)*t) • pairVariableProjection 3,
    pairVariableProjection 1,
    (if keepD then Tb else Tk),
    (if keepD then Ta else Tb),
    (if keepD then Tk else Ta)]

theorem pairFixedRowInverse_transform (t alpha : ℝ) (keepD : Bool) (ht : t≠0)
    (y : SliceCoordinates) :
    pairFixedRowInverse t alpha keepD (pairFixedRowTransform t alpha keepD y)=y := by
  ext i
  cases keepD <;> fin_cases i <;> simp [pairFixedRowInverse,pairFixedRowTransform,smul_eq_mul,pairVariableProjection]
  all_goals field_simp [ht]
  all_goals ring

theorem pairFixedRowTransform_inverse (t alpha : ℝ) (keepD : Bool) (ht : t≠0)
    (y : PairChartVariables) :
    pairFixedRowTransform t alpha keepD (pairFixedRowInverse t alpha keepD y)=y := by
  ext i
  cases keepD <;> fin_cases i <;> simp [pairFixedRowInverse,pairFixedRowTransform,smul_eq_mul,pairVariableProjection]
  all_goals field_simp [ht]
  all_goals ring

theorem pairFixedRowTransform_isInvertible (t alpha : ℝ) (keepD : Bool) (ht : t≠0) :
    (pairFixedRowTransform t alpha keepD).IsInvertible := by
  apply euclidean_clm_isInvertible_of_injective
  intro a b hab
  have h := congrArg (pairFixedRowInverse t alpha keepD) hab
  simpa only [pairFixedRowInverse_transform t alpha keepD ht] using h

theorem fixedAngleRadii_pairToFixedSlice (t alpha : ℝ) (y : PairChartVariables) :
    fixedAngleRadii 2 (pairToFixedSlice t alpha y)=pairChartRadii t alpha y := by
  ext i
  fin_cases i <;> rfl

theorem fixedAngleAngles_pairToFixedSlice (t alpha : ℝ) (y : PairChartVariables) :
    fixedAngleAngles 2 (pairToFixedSlice t alpha y)=pairChartAngles t alpha y := by
  ext i
  fin_cases i <;> rfl
theorem fixedAngleSatellites_pairToFixedSlice (t alpha : ℝ) (y : PairChartVariables) :
    fixedAngleSatellites 2 (pairToFixedSlice t alpha y)=pairChartPoints t alpha y := by
  rw [fixedAngleSatellites,fixedAngleRadii_pairToFixedSlice,fixedAngleAngles_pairToFixedSlice]
  rfl

theorem fixedAnglePhysicalConfiguration_pairToFixedSlice (eps t p alpha : ℝ)
    (y : PairChartVariables) :
    fixedAnglePhysicalConfiguration (eps,pairChartMass t p alpha) 2 (pairToFixedSlice t alpha y)=
      centeredFromRelative eps (pairChartMass t p alpha) (pairChartPoints t alpha y) := by
  rw [fixedAnglePhysicalConfiguration,fixedAngleSatellites_pairToFixedSlice]

theorem pairChartPhysicalRows_eq_fixed_transform (eps t p alpha : ℝ) (keepD : Bool)
    (y : PairChartVariables) :
    pairChartPhysicalRows eps t p alpha keepD y=
      pairFixedRowTransform t alpha keepD
        (fixedAngleDeletedResidual (eps,pairChartMass t p alpha) 2 (if keepD then 2 else 3)
          (pairToFixedSlice t alpha y)) := by
  let R := radialResidual eps (pairChartMass t p alpha) (pairChartRadii t alpha y) (pairChartAngles t alpha y)
  let T := angularResidual eps (pairChartMass t p alpha) (pairChartRadii t alpha y) (pairChartAngles t alpha y)
  simp only [fixedAngleDeletedResidual,fixedAngleRadii_pairToFixedSlice,
    fixedAngleAngles_pairToFixedSlice]
  ext i
  cases keepD <;> fin_cases i
  all_goals first | rfl | (
    first
    | change (R 1-R 0)/t=t⁻¹*(R 1-R 0)
    | change (T 1-T 0)/t=t⁻¹*(T 1-T 0)
    rw [div_eq_mul_inv,mul_comm])
theorem pairToFixedSlice_regular (eps t p alpha : ℝ) (y : PairChartVariables)
    (heps : 0<eps) (ht : 0<t) (hreg : PairChartRegular eps t alpha y)
    (hr : ∀ i, 0<pairChartRadii t alpha y i) :
    SliceRegular (eps,pairChartMass t p alpha ∘ fixedAnglePermutation 2)
      (pairToFixedSlice t alpha y) := by
  let e := fixedAnglePermutation (2 : Satellite)
  have hq : sliceSatellites (pairToFixedSlice t alpha y)=pairChartPoints t alpha y ∘ e := by
    ext i
    fin_cases i <;> rfl
  have hcollision := pairChartPoints_relativeCollisionFree eps t alpha y ht hreg
  refine ⟨by linarith,?_,?_⟩
  · intro i
    have hr' : 0<fixedAngleRadii 2 (pairToFixedSlice t alpha y) (e i) := by
      rw [fixedAngleRadii_pairToFixedSlice]
      exact hr (e i)
    change 0<sliceRadii (pairToFixedSlice t alpha y) (e.symm (e i)) at hr'
    simpa only [Equiv.symm_apply_apply] using hr'
  · intro i j hij
    rw [hq]
    exact hcollision.2 (e i) (e j) (e.injective.ne hij)

theorem pairChartExtendedRows_eq_fixed_transform (eps t p alpha : ℝ) (keepD : Bool)
    (y : PairChartVariables) (ht : 0<t) (hreg : PairChartRegular eps t alpha y) :
    pairChartExtendedRows eps t p alpha keepD y=
      pairFixedRowTransform t alpha keepD
        (fixedAngleDeletedResidual (eps,pairChartMass t p alpha) 2 (if keepD then 2 else 3)
          (pairToFixedSlice t alpha y)) := by
  rw [pairChartExtendedRows_eq_physical eps t p alpha keepD y ht hreg.2.2.1 hreg.1
    (hreg.2.1 0) (hreg.2.1 1) (pairChartRegular_external_pair _ _ _ _ hreg)]
  exact pairChartPhysicalRows_eq_fixed_transform eps t p alpha keepD y

theorem fixedAngleDeletedResidual_differentiableAt (p : ContinuationParameter)
    (fixed omitted : Satellite) (y : SliceCoordinates)
    (hreg : SliceRegular (p.1,p.2 ∘ fixedAnglePermutation fixed) y)
    (hμ : PositiveRatio p.2) :
    DifferentiableAt ℝ (fixedAngleDeletedResidual p fixed omitted) y := by
  let e := fixedAnglePermutation fixed
  let p' : ContinuationParameter := (p.1,p.2 ∘ e)
  have hm0 : p'.2 0≠0 := ne_of_gt (hμ.1 (e 0))
  have hd : DifferentiableAt ℝ (reducedResidual p') y := by
    have hc : ContDiff ℝ 1 (fun z : SliceCoordinates => (p',z)) :=
      contDiff_const.prodMk contDiff_id
    exact ((reducedResidual_joint_contDiffAt 1 p' y hreg).comp y hc.contDiffAt).differentiableAt
      (by norm_num)
  rw [fixedAngleDeletedResidual_eq]
  have heq : deletedReducedResidual p' (e.symm omitted)=
      fun z => deletedReducedRowTransform p'.2 (e.symm omitted) (reducedResidual p' z) :=
    funext (deletedReducedResidual_eq_row_transform p' (e.symm omitted) hm0)
  change DifferentiableAt ℝ (deletedReducedResidual p' (e.symm omitted)) y
  rw [heq]
  exact (deletedReducedRowTransform p'.2 (e.symm omitted)).differentiableAt.comp y hd

/-- This is an equality of derivatives of the actual functions, obtained
from their equality throughout the actual open regular chart. -/
theorem pairChartJacobian_eq_fixed_transform (eps t p alpha : ℝ) (keepD : Bool)
    (y : PairChartVariables) (heps : 0<eps) (ht : 0<t)
    (hm : PositiveRatio (pairChartMass t p alpha))
    (hreg : PairChartRegular eps t alpha y) (hr : ∀ i, 0<pairChartRadii t alpha y i) :
    pairChartJacobian eps t p alpha keepD y=
      ((pairFixedRowTransform t alpha keepD).comp
        (fderiv ℝ (fixedAngleDeletedResidual (eps,pairChartMass t p alpha) 2
          (if keepD then 2 else 3)) (pairToFixedSlice t alpha y))).comp (pairToFixedSlice t alpha) := by
  have hs := pairToFixedSlice_regular eps t p alpha y heps ht hreg hr
  have hd := fixedAngleDeletedResidual_differentiableAt (eps,pairChartMass t p alpha)
    2 (if keepD then 2 else 3) (pairToFixedSlice t alpha y) hs hm
  have hjc : ContinuousAt (fun z : PairChartVariables => ((![eps,t,p,alpha] : Fin 4 → ℝ),z)) y := by
    fun_prop
  have hnear : ∀ᶠ z in 𝓝 y, PairChartRegular eps t alpha z :=
    hjc.eventually (pairChartRegular_isOpen.mem_nhds hreg)
  have heq : pairChartExtendedRows eps t p alpha keepD =ᶠ[𝓝 y]
      (fun z => pairFixedRowTransform t alpha keepD
        (fixedAngleDeletedResidual (eps,pairChartMass t p alpha) 2 (if keepD then 2 else 3)
          (pairToFixedSlice t alpha z))) :=
    hnear.mono (fun z hz => pairChartExtendedRows_eq_fixed_transform eps t p alpha keepD z ht hz)
  have hc := (pairFixedRowTransform t alpha keepD).hasFDerivAt.comp y
    (hd.hasFDerivAt.comp y (pairToFixedSlice t alpha).hasFDerivAt)
  exact (hc.congr_of_eventuallyEq heq).fderiv

/-- Complete pair-chart instance of Lemma 3.1. At positive physical
scales and positive radii, its genuine Jacobian is invertible exactly
when the original six-dimensional physical shape Hessian is
nondegenerate. No relation between ε and t is imposed. -/
theorem pairChartJacobian_isInvertible_iff_shape (eps t p alpha : ℝ) (keepD : Bool)
    (y : PairChartVariables) (heps : 0<eps) (ht : 0<t)
    (hm : PositiveRatio (pairChartMass t p alpha))
    (hreg : PairChartRegular eps t alpha y) (hr : ∀ i, 0<pairChartRadii t alpha y i)
    (hroot : pairChartExtendedRows eps t p alpha keepD y=0) :
    (pairChartJacobian eps t p alpha keepD y).IsInvertible ↔
      ShapeHessianNondegenerate (masses eps (pairChartMass t p alpha)) 1
        (centeredFromRelative eps (pairChartMass t p alpha) (pairChartPoints t alpha y)) := by
  have hs := pairToFixedSlice_regular eps t p alpha y heps ht hreg hr
  have hLi := pairFixedRowTransform_isInvertible t alpha keepD (ne_of_gt ht)
  have hSi := pairToFixedSlice_isInvertible t alpha (ne_of_gt ht)
  have hfixed : fixedAngleDeletedResidual (eps,pairChartMass t p alpha) 2
      (if keepD then 2 else 3) (pairToFixedSlice t alpha y)=0 := by
    rw [pairChartExtendedRows_eq_fixed_transform eps t p alpha keepD y ht hreg] at hroot
    exact hLi.injective.eq_iff' (map_zero _)|>.mp hroot
  rw [pairChartJacobian_eq_fixed_transform eps t p alpha keepD y heps ht hm hreg hr]
  obtain ⟨eL,heL⟩ := hLi
  obtain ⟨eS,heS⟩ := hSi
  rw [←heL,←heS,ContinuousLinearMap.isInvertible_comp_equiv,
    ContinuousLinearMap.isInvertible_equiv_comp]
  have h := fixedAngleDeletedJacobian_isInvertible_iff_shape
    (eps,pairChartMass t p alpha) 2 (if keepD then 2 else 3)
    (pairToFixedSlice t alpha y) hs heps hm hfixed
  rw [heS]
  simpa only [fixedAnglePhysicalConfiguration_pairToFixedSlice] using h

end DominantFiveBody

