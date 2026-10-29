import DominantFiveBody.HessianCorrespondence

/-! The literal centered-space radial/tangent orthogonal direct sum in
Lemma 3.1, distinct from the seven-dimensional rotation-slice decomposition. -/
noncomputable section
namespace DominantFiveBody

def inertiaTangentSpace (m : MassVector) (x : Configuration) : Submodule ℝ Configuration :=
  centeredVariationSpace m ⊓ (massInnerRight m x).ker

theorem mem_inertiaTangentSpace (m : MassVector) (x w : Configuration) :
    w∈inertiaTangentSpace m x ↔ weightedPosition m w=0 ∧ massInner m x w=0 := by
  simp [inertiaTangentSpace,centeredVariationSpace,weightedPositionLinear_apply,massInnerRight_apply]

theorem radialRemoval_mem_inertiaTangent (m : MassVector) (hm : PositiveMasses m)
    (x : Configuration) (hx : NormalizedCentralConfiguration m x) (w : Configuration)
    (hw : w∈centeredVariationSpace m) : radialRemoval m x w∈inertiaTangentSpace m x := by
  have hI : massInner m x x≠0 := (massInner_self_pos m hm x (collisionFree_ne_zero x hx.1)).ne'
  rw [mem_inertiaTangentSpace]
  constructor
  · change weightedPositionLinear m (w-(massInner m x w/massInner m x x) • x)=0
    rw [map_sub,map_smul,show weightedPositionLinear m w=0 from hw,
      weightedPositionLinear_apply,hx.2.1,smul_zero,sub_self]
  · rw [radialRemoval,massInner_sub_right,massInner_smul_right,div_mul_cancel₀ _ hI,sub_self]

theorem centered_radial_tangent_direct_sum (m : MassVector) (hm : PositiveMasses m)
    (x : Configuration) (hx : NormalizedCentralConfiguration m x) :
    (Submodule.span ℝ {x} ⊔ inertiaTangentSpace m x = centeredVariationSpace m) ∧
    Disjoint (Submodule.span ℝ {x}) (inertiaTangentSpace m x) := by
  have hxE : x∈centeredVariationSpace m := hx.2.1
  have hI : massInner m x x≠0 := (massInner_self_pos m hm x (collisionFree_ne_zero x hx.1)).ne'
  constructor
  · apply le_antisymm
    · exact sup_le (Submodule.span_le.mpr (by simpa using hxE)) inf_le_left
    · intro w hw
      have hwr := radialRemoval_mem_inertiaTangent m hm x hx w hw
      have hrad : (massInner m x w/massInner m x x) • x∈Submodule.span ℝ {x} :=
        Submodule.smul_mem _ _ (Submodule.subset_span (by simp))
      have hsum := Submodule.add_mem_sup hrad hwr
      simpa only [radialRemoval,add_sub_cancel] using hsum
  · apply Submodule.disjoint_def.mpr
    intro w hrad htan
    obtain ⟨a,rfl⟩ := Submodule.mem_span_singleton.mp hrad
    have hh := ((mem_inertiaTangentSpace m x _).mp htan).2
    rw [massInner_smul_right] at hh
    have ha := (mul_eq_zero.mp hh).resolve_right hI
    rw [ha,zero_smul]

theorem centered_radial_tangent_hessian_orthogonal (m : MassVector) (hm : PositiveMasses m)
    (x : Configuration) (hx : NormalizedCentralConfiguration m x) :
    (∀ v∈Submodule.span ℝ {x},∀ w∈inertiaTangentSpace m x,physicalHessian m 1 x v w=0) ∧
      physicalHessian m 1 x x x=3*inertia m x ∧ 0<3*inertia m x := by
  refine ⟨?_,?_,?_⟩
  · intro v hv w hw
    obtain ⟨a,rfl⟩ := Submodule.mem_span_singleton.mp hv
    have hw0 := ((mem_inertiaTangentSpace m x w).mp hw).2
    rw [physicalHessian, map_smul,smul_apply,smul_eq_mul]
    change a*physicalHessian m 1 x x w=0
    rw [physicalHessian_radial_of_normalizedCC m x hx,hw0,mul_zero,mul_zero]
  · rw [physicalHessian_radial_of_normalizedCC m x hx,massInner_self_eq_inertia]
  · have hI := massInner_self_pos m hm x (collisionFree_ne_zero x hx.1)
    rw [massInner_self_eq_inertia] at hI
    positivity

end DominantFiveBody
