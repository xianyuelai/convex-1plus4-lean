import DominantFiveBody.PairExterior

/-! # The actual derivative at the zero-scale target diagonal -/

noncomputable section
open scoped BigOperators

namespace DominantFiveBody

-- Use the normed-space instances also in derivative statements whose
-- displayed formula does not itself mention a norm.
local instance newtonPlaneAddCommGroup : AddCommGroup Plane := (inferInstance : NormedAddCommGroup Plane).toAddCommGroup
local instance newtonPlaneModule : Module ℝ Plane := (inferInstance : NormedSpace ℝ Plane).toModule
local instance newtonPlaneTopology : TopologicalSpace Plane :=
  (inferInstance : PseudoMetricSpace Plane).toUniformSpace.toTopologicalSpace

def newtonTargetDerivative (source target : Plane) : Plane →L[ℝ] Plane :=
  (3/‖source-target‖^5) • ((innerSL ℝ (source-target)).smulRight (source-target))-
    (‖source-target‖^3)⁻¹ • ContinuousLinearMap.id ℝ Plane

theorem newtonTargetDerivative_apply (source target direction : Plane) :
    newtonTargetDerivative source target direction=
      (3/‖source-target‖^5*inner ℝ (source-target) direction) • (source-target)-
        (‖source-target‖^3)⁻¹ • direction := by
  change (3/‖source-target‖^5) • (inner ℝ (source-target) direction • (source-target))-
    (‖source-target‖^3)⁻¹ • direction = _
  rw [smul_smul]

theorem newtonTargetField_hasFDerivAt (source target : Plane) (hsep : source≠target) :
    HasFDerivAt (newtonTargetField source) (newtonTargetDerivative source target) target := by
  have hdiff : HasFDerivAt (fun q : Plane => source-q) (-(ContinuousLinearMap.id ℝ Plane)) target := by
    convert! (-(ContinuousLinearMap.id ℝ Plane)).hasFDerivAt.const_add source using 1
  have hnorm := (norm_hasFDerivAt (source-target) (sub_ne_zero.mpr hsep)).comp target hdiff
  have hn : ‖source-target‖≠0 := norm_ne_zero_iff.mpr (sub_ne_zero.mpr hsep)
  have hinv := (hasDerivAt_inv (pow_ne_zero 3 hn)).comp_hasFDerivAt target (hnorm.pow 3)
  have hd := hinv.smul hdiff
  apply hd.congr_fderiv
  ext v k
  simp only [newtonTargetDerivative,add_apply,sub_apply,
    smul_apply,neg_apply,ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.smulRight_apply,ContinuousLinearMap.id_apply,innerSL_apply_apply,
    PiLp.add_apply,PiLp.sub_apply,PiLp.smul_apply,PiLp.neg_apply,
    inner_neg_right,smul_eq_mul]
  norm_num
  field_simp
  ring

theorem dividedInverseCube_diagonal (source target direction : Plane) (hsep : source≠target) :
    dividedInverseCube source target target direction=
      3/‖source-target‖^5*inner ℝ (source-target) direction := by
  have hn : ‖source-target‖≠0 := norm_ne_zero_iff.mpr (sub_ne_zero.mpr hsep)
  unfold dividedInverseCube
  simp only [inner_add_right,inner_sub_right,real_inner_smul_right,inner_sub_left]
  rw [real_inner_comm source direction,real_inner_comm target direction]
  field_simp
  ring

/-- The extension's diagonal value is the derivative of the actual
Newton field. This identifies the zero-scale row with a genuine derivative. -/
theorem dividedNewtonTargetField_diagonal (source target direction : Plane) (hsep : source≠target) :
    dividedNewtonTargetField source target target direction=
      (fderiv ℝ (newtonTargetField source) target) direction := by
  rw [(newtonTargetField_hasFDerivAt source target hsep).fderiv,
    newtonTargetDerivative_apply,dividedNewtonTargetField,dividedInverseCube_diagonal source target direction hsep]

end DominantFiveBody
