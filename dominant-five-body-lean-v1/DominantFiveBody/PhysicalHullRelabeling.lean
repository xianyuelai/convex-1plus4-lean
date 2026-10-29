import DominantFiveBody.CoorbitalContinuation
import DominantFiveBody.FixedAngleRows
import DominantFiveBody.RotationTransport
import DominantFiveBody.Application
import DominantFiveBody.HullOrderTransport

/-! # Actual mass and hull transport to every oriented order

Labels and masses are transported together in the equations. This never
enlarges `OrientedSimilar`, whose labels remain fixed.
-/

noncomputable section
open scoped BigOperators ContDiff
open Filter Set Topology

namespace DominantFiveBody

theorem satelliteLabelPermutation_hull (σ : HullOrder) :
    satelliteLabelPermutation (hullSatellitePermutation σ)=σ.labels := by
  apply Equiv.ext
  intro i
  refine Fin.cases ?_ (fun j => ?_) i
  · exact σ.primary_first.symm
  · change ((σ.labels j.succ).pred (hullOrder_label_succ_ne_zero σ j)).succ=σ.labels j.succ
    exact Fin.succ_pred _ _

theorem strictConvex_hull_reindex_iff (σ : HullOrder) (x : Configuration) :
    StrictConvexInOrder standardHullOrder (x ∘ σ.labels) ↔ StrictConvexInOrder σ x := by
  rfl

theorem strictConvex_hull_pullback (σ : HullOrder) (x : Configuration)
    (hx : StrictConvexInOrder standardHullOrder x) :
    StrictConvexInOrder σ (x ∘ σ.labels.symm) := by
  apply (strictConvex_hull_reindex_iff σ (x ∘ σ.labels.symm)).mp
  simpa only [Function.comp_assoc,Equiv.symm_comp_self,Function.comp_id] using hx

theorem masses_hull_pullback (ε : ℝ) (μ : MassRatio) (σ : HullOrder) :
    masses ε (μ ∘ hullSatellitePermutation σ) ∘ σ.labels.symm=masses ε μ := by
  rw [masses_satellitePermutation,satelliteLabelPermutation_hull,Function.comp_assoc,
    Equiv.self_comp_symm,Function.comp_id]

/-- Proposition 3.3 supplies genuine multiplier-one roots, strict
convexity in every requested original-label hull order, and the
original physical six-dimensional shape Hessian. The threshold here
may depend on the fixed positive mass ratio and hull order. -/
theorem normalized_physical_local_existence_all_orders (μ : MassRatio) (hμ : PositiveRatio μ)
    (σ : HullOrder) :
    ∃ δ : ℝ, 0<δ ∧ ∀ ε, 0<ε → ε<δ → ∃ x,
      NormalizedCentralConfiguration (masses ε μ) x ∧ StrictConvexInOrder σ x ∧
        ShapeHessianNondegenerate (masses ε μ) 1 x := by
  classical
  let e := hullSatellitePermutation σ
  let ν := μ ∘ e
  have hν : PositiveRatio ν := positiveRatio_satellitePermutation μ hμ e
  obtain ⟨η,r,C,hη,_,_,hbranches⟩ := coorbital_compact_physical_continuation {ν}
    isCompact_singleton (by intro ζ hζ; simpa only [Set.mem_singleton_iff.mp hζ] using hν)
  obtain ⟨ψ,_,_,hbranch⟩ := hbranches ν (Set.mem_singleton _)
  refine ⟨η,hη,?_⟩
  intro ε hε hεη
  have h := hbranch ε ν (by simpa only [abs_of_pos hε] using hεη) (by simpa using hη)
  obtain ⟨hx,_,hn⟩ := h.2.2.2.2.2.2.2 hε hν
  let x := slicePhysicalConfiguration (ε,ν) (ψ (ε,ν))
  have hmass : masses ε ν ∘ σ.labels.symm=masses ε μ := masses_hull_pullback ε μ σ
  have hx' := normalizedCC_permutation (masses ε ν) x hx σ.labels.symm
  have hn' := shapeHessianNondegenerate_permutation_forward (masses ε ν) x hx σ.labels.symm hn
  rw [hmass] at hx' hn'
  exact ⟨x ∘ σ.labels.symm,hx',strictConvex_hull_pullback σ x h.1,hn'⟩

/-- The original geometric fixed-parameter local existence premise is
now discharged for the whole open positive mass simplex and all orders. -/
theorem physical_fixed_parameter_local_existence : FixedParameterLocalExistence PhysicalRoot := by
  intro p
  obtain ⟨δ,hδ,hroots⟩ := normalized_physical_local_existence_all_orders p.1.val p.1.property p.2
  refine ⟨δ,hδ,?_⟩
  intro ε hε hεδ
  obtain ⟨x,hx,hconv,_⟩ := hroots ε hε hεδ
  exact ⟨x,normalized_is_central _ _ hx,hconv⟩

end DominantFiveBody

