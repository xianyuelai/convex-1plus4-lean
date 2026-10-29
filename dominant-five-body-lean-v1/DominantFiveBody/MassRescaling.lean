import DominantFiveBody.Main

/-! Positive common mass rescaling, including the actual constrained Hessian.
This verifies the unnormalized-mass remark following Theorem 1.1. -/
noncomputable section
open scoped BigOperators
namespace DominantFiveBody

def scaleMasses (c : ℝ) (m : MassVector) : MassVector := fun i => c*m i

theorem totalMass_scaleMasses (c : ℝ) (m : MassVector) :
    totalMass (scaleMasses c m)=c*totalMass m := by
  simp [totalMass,scaleMasses,Finset.mul_sum]

theorem weightedPosition_scaleMasses (c : ℝ) (m : MassVector) (x : Configuration) :
    weightedPosition (scaleMasses c m) x=c • weightedPosition m x := by
  simp [weightedPosition,scaleMasses,mul_smul,Finset.smul_sum]

theorem massCenter_scaleMasses (c : ℝ) (hc : c≠0) (m : MassVector) (x : Configuration) :
    massCenter (scaleMasses c m) x=massCenter m x := by
  simp [massCenter,totalMass_scaleMasses,weightedPosition_scaleMasses,smul_smul,
    mul_inv_rev,hc]

theorem massInner_scaleMasses (c : ℝ) (m : MassVector) (v w : Configuration) :
    massInner (scaleMasses c m) v w=c*massInner m v w := by
  simp [massInner,scaleMasses,Finset.mul_sum,mul_assoc]

theorem acceleration_scaleMasses (c : ℝ) (m : MassVector) (x : Configuration) (i : Label) :
    acceleration (scaleMasses c m) x i=c • acceleration m x i := by
  simp [acceleration,scaleMasses,Finset.smul_sum,mul_div_assoc,mul_smul]

theorem multiplierEquation_scaleMasses (c : ℝ) (hc : c≠0) (m : MassVector)
    (x : Configuration) (lam : ℝ) (he : MultiplierEquation m x lam) :
    MultiplierEquation (scaleMasses c m) x (c*lam) := by
  intro i
  rw [acceleration_scaleMasses,massCenter_scaleMasses c hc,he i,smul_smul,mul_neg]

theorem centralConfiguration_scaleMasses (c : ℝ) (hc : 0<c) (m : MassVector)
    (x : Configuration) (hx : CentralConfiguration m x) :
    CentralConfiguration (scaleMasses c m) x := by
  obtain ⟨hcol,lam,hl,he⟩ := hx
  exact ⟨hcol,c*lam,mul_pos hc hl,multiplierEquation_scaleMasses c hc.ne' m x lam he⟩

theorem scaleMasses_inverse (c : ℝ) (hc : c≠0) (m : MassVector) :
    scaleMasses c⁻¹ (scaleMasses c m)=m := by
  ext i
  simp [scaleMasses,hc]

theorem centralConfiguration_scaleMasses_iff (c : ℝ) (hc : 0<c) (m : MassVector)
    (x : Configuration) : CentralConfiguration (scaleMasses c m) x ↔ CentralConfiguration m x := by
  constructor
  · intro hx
    simpa only [scaleMasses_inverse c hc.ne'] using
      centralConfiguration_scaleMasses c⁻¹ (inv_pos.mpr hc) (scaleMasses c m) x hx
  · exact centralConfiguration_scaleMasses c hc m x

theorem shapeSpace_scaleMasses (c : ℝ) (hc : c≠0) (m : MassVector) (x : Configuration) :
    shapeSpace (scaleMasses c m) x=shapeSpace m x := by
  have hcenter : centered (scaleMasses c m) x=centered m x := by
    funext i
    simp only [centered,massCenter_scaleMasses c hc]
  ext v
  simp only [mem_shapeSpace_iff,hcenter,
    weightedPosition_scaleMasses,massInner_scaleMasses,smul_eq_zero,mul_eq_zero,hc,
    false_or]

theorem physicalHessian_scaleMasses (c : ℝ) (m : MassVector) (lam : ℝ)
    (x : Configuration) (hx : CollisionFree x) (v w : Configuration) :
    physicalHessian (scaleMasses c m) (c*lam) x v w=c^2*physicalHessian m lam x v w := by
  rw [physicalHessian_explicit _ _ x hx,physicalHessian_explicit m lam x hx,
    massInner_scaleMasses,mul_add,Finset.mul_sum]
  congr 1
  · apply Finset.sum_congr rfl
    intro p _
    unfold scaleMasses
    ring
  · ring

theorem nondegenerateCentralConfiguration_scaleMasses (c : ℝ) (hc : 0<c)
    (m : MassVector) (x : Configuration) (hx : NondegenerateCentralConfiguration m x) :
    NondegenerateCentralConfiguration (scaleMasses c m) x := by
  obtain ⟨hcol,lam,hl,he,hd,hn⟩ := hx
  refine ⟨hcol,c*lam,mul_pos hc hl,multiplierEquation_scaleMasses c hc.ne' m x lam he,?_,?_⟩
  · rw [shapeSpace_scaleMasses c hc.ne']
    exact hd
  · intro v hv hvker
    apply hn v
    · simpa only [shapeSpace_scaleMasses c hc.ne'] using hv
    · intro w hw
      have hz := hvker w (by simpa only [shapeSpace_scaleMasses c hc.ne'] using hw)
      rw [physicalHessian_scaleMasses c m lam x hcol] at hz
      exact (mul_eq_zero.mp hz).resolve_left (pow_ne_zero 2 hc.ne')

theorem positive_masses_normalized_ratios (m : MassVector) (hm : PositiveMasses m) :
    ∃ (ε : ℝ) (μ : MassRatio),0<ε ∧ PositiveRatio μ ∧
      ε=(∑ i : Satellite,m i.succ)/m 0 ∧ m=scaleMasses (m 0) (masses ε μ) := by
  let S : ℝ := ∑ i : Satellite,m i.succ
  have hS : 0<S := Finset.sum_pos (fun i _ => hm i.succ) Finset.univ_nonempty
  refine ⟨S/m 0,fun i => m i.succ/S,div_pos hS (hm 0),?_,rfl,?_⟩
  · refine ⟨fun i => div_pos (hm i.succ) hS,?_⟩
    rw [←Finset.sum_div]
    exact div_self hS.ne'
  · funext i
    refine Fin.cases ?_ (fun j => ?_) i
    · simp [scaleMasses]
    · simp only [scaleMasses,masses_satellite]
      field_simp [hS.ne',(hm 0).ne']

theorem main_uniform_unnormalized :
    ∃ δ : ℝ,0<δ ∧ ∀ m : MassVector,PositiveMasses m →
      (∑ i : Satellite,m i.succ)/m 0<δ → ∀ σ : HullOrder,
      ∃ x : Configuration,StrictConvexCentralConfiguration m σ x ∧
        (∀ y,StrictConvexCentralConfiguration m σ y → OrientedSimilar x y) ∧
        (∀ y,StrictConvexCentralConfiguration m σ y → NondegenerateCentralConfiguration m y) := by
  obtain ⟨δ,hδ,hmain⟩ := main_uniform
  refine ⟨δ,hδ,?_⟩
  intro m hm hsmall σ
  obtain ⟨ε,μ,hε,hμ,heps,heq⟩ := positive_masses_normalized_ratios m hm
  obtain ⟨x,hx,hu,hn⟩ := hmain μ hμ ε hε (by rwa [heps]) σ
  have hcc (y : Configuration) : CentralConfiguration m y ↔ CentralConfiguration (masses ε μ) y := by
    conv_lhs => rw [heq]
    exact centralConfiguration_scaleMasses_iff (m 0) (hm 0) (masses ε μ) y
  refine ⟨x,⟨(hcc x).mpr hx.1,hx.2⟩,?_,?_⟩
  · intro y hy
    exact hu y ⟨(hcc y).mp hy.1,hy.2⟩
  · intro y hy
    have hh := nondegenerateCentralConfiguration_scaleMasses (m 0) (hm 0) (masses ε μ) y
      (hn y ⟨(hcc y).mp hy.1,hy.2⟩)
    rwa [←heq] at hh

end DominantFiveBody
