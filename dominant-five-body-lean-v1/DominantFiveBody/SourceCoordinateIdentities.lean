import DominantFiveBody.Coordinates
import DominantFiveBody.SingleScaleKernel

/-! Exact defining identities used in the source's centered/relative change
and its removable sinc singularity. -/
noncomputable section
open scoped ContDiff
namespace DominantFiveBody

theorem centeredFromRelative_source_formulas (ε : ℝ) (μ : MassRatio)
    (q : SatelliteConfiguration) :
    liftRelative q 0=0 ∧
      centeredFromRelative ε μ q 0= -(ε/(1+ε)) • relativeAverage μ q ∧
      (∀ i : Satellite, centeredFromRelative ε μ q i.succ=
        q i-(ε/(1+ε)) • relativeAverage μ q) ∧
      centeredFromRelative 0 μ q=liftRelative q ∧
      (∀ i j : Label,pairDistance (centeredFromRelative ε μ q) i j=
        pairDistance (liftRelative q) i j) := by
  refine ⟨rfl,?_,fun _ => rfl,?_,?_⟩
  · simp [centeredFromRelative,liftRelative,neg_smul]
  · funext i
    simp [centeredFromRelative]
  · intro i j
    simp only [pairDistance,centeredFromRelative,sub_sub_sub_cancel_right]

theorem sinc_source_extension :
    Real.sinc 0=1 ∧ (∀ t : ℝ,t≠0 → Real.sinc t=Real.sin t/t) ∧
      ContDiff ℝ ∞ Real.sinc :=
  ⟨Real.sinc_zero,fun _ ht => Real.sinc_of_ne_zero ht,sinc_contDiff ∞⟩

end DominantFiveBody
