import Mathlib.Topology.Covering.Basic
import Mathlib.Topology.LocallyConstant.Basic

noncomputable section
open Set Topology

namespace DominantFiveBody

theorem unique_fiber_of_equiv {E X : Type*} (f : E → X) {x y : X}
    (e : (f ⁻¹' {x}) ≃ (f ⁻¹' {y})) (hx : ∃! a, f a = x) :
    ∃! a, f a = y := by
  obtain ⟨a, ha, huniq⟩ := hx
  let q : f ⁻¹' {x} := ⟨a, ha⟩
  have hall : ∀ v : f ⁻¹' {x}, v = q := fun v => Subtype.ext (huniq v.val v.property)
  refine ⟨(e q).val, (e q).property, ?_⟩
  intro b hb
  let v : f ⁻¹' {y} := ⟨b, by simpa using hb⟩
  have heq : v = e q := by
    calc v = e (e.symm v) := (e.apply_symm_apply v).symm
      _ = e q := congrArg e (hall (e.symm v))
  exact congrArg Subtype.val heq

/-- The fixed-mass fiber equivalence supplied by each covering chart
makes the one-point-fiber proposition locally constant, including empty fibers. -/
theorem covering_unique_fiber_locallyConstant {E X : Type*}
    [TopologicalSpace E] [TopologicalSpace X] (f : E → X)
    (hc : IsCoveringMapOn f univ) :
    IsLocallyConstant (fun x => ∃! a, f a = x) := by
  apply (IsLocallyConstant.iff_exists_open _).mpr
  intro x
  obtain ⟨hd, U, hxU, hU, hfU, H, hH⟩ := hc x (mem_univ x)
  refine ⟨U, hU, hxU, ?_⟩
  intro y hy
  have heven : IsEvenlyCovered f y (f ⁻¹' {x}) := ⟨hd, U, hy, hU, hfU, H, hH⟩
  apply propext
  exact ⟨unique_fiber_of_equiv f heven.fiberHomeomorph.toEquiv.symm,
    unique_fiber_of_equiv f heven.fiberHomeomorph.toEquiv⟩

theorem covering_unique_fiber_of_preconnected {E X : Type*}
    [TopologicalSpace E] [TopologicalSpace X] [PreconnectedSpace X] (f : E → X)
    (hc : IsCoveringMapOn f univ) {x : X} (hx : ∃! a, f a = x) :
    ∀ y, ∃! a, f a = y := by
  let C : LocallyConstant X Prop := ⟨fun x => ∃! a, f a = x,
    covering_unique_fiber_locallyConstant f hc⟩
  intro y
  have heq := C.apply_eq_of_preconnectedSpace x y
  change (∃! a, f a = x) = (∃! a, f a = y) at heq
  exact heq ▸ hx

end DominantFiveBody
