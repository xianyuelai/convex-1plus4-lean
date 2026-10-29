import DominantFiveBody.Specification
import DominantFiveBody.UniformThreshold

/-! # Conditional threshold assembly for the actual geometric statement

The three sequence-exclusion conditions below use the physical predicates
from `Definitions`, including SO(2) similarity and the actual second Fréchet
derivative. They are still assumptions: §2 and §§4–6 have not supplied them.
This file does not declare an unconditional `main_uniform` theorem.
-/

namespace DominantFiveBody

abbrev PhysicalParameter := {μ : MassRatio // PositiveRatio μ} × HullOrder

def PhysicalRoot (p : PhysicalParameter) (ε : ℝ) (x : Configuration) : Prop :=
  StrictConvexCentralConfiguration (masses ε p.1.val) p.2 x

def PhysicalExistence (p : PhysicalParameter) (ε : ℝ) : Prop :=
  ∃ x, PhysicalRoot p ε x

def PhysicalUniqueness (p : PhysicalParameter) (ε : ℝ) : Prop :=
  ∀ x y, PhysicalRoot p ε x → PhysicalRoot p ε y → OrientedSimilar x y

def PhysicalNondegeneracy (p : PhysicalParameter) (ε : ℝ) : Prop :=
  ∀ x, PhysicalRoot p ε x → NondegenerateCentralConfiguration (masses ε p.1.val) x

/-- Theorem 1.1 (`thm:main`) assembled from THREE EXPLICIT uniform inputs.
The hypotheses are neither supplied instances nor hidden typeclass conditions. -/
theorem main_of_uniform_physical_facts
    (hexistence : UniformBelow PhysicalExistence)
    (huniqueness : UniformBelow PhysicalUniqueness)
    (hnondegeneracy : UniformBelow PhysicalNondegeneracy) : MainUniformStatement := by
  obtain ⟨δ, hδ, hall⟩ := uniformBelow_three hexistence huniqueness hnondegeneracy
  refine ⟨δ, hδ, ?_⟩
  intro μ hμ ε hε hεδ σ
  obtain ⟨⟨x, hx⟩, hu, hn⟩ := hall (⟨μ, hμ⟩, σ) ε hε hεδ
  exact ⟨x, hx, fun y hy => hu x y hx hy, fun y hy => hn y hy⟩

/-- §7, specialized to the FULL mass simplex and ALL oriented five-point orders.
This is a conditional theorem; the three bad-sequence exclusions are open
research obligations, not claimed consequences of an implemented chart system. -/
theorem main_of_no_bad_physical_sequences
    (hexistence : ¬ BadSequence PhysicalExistence)
    (huniqueness : ¬ BadSequence PhysicalUniqueness)
    (hnondegeneracy : ¬ BadSequence PhysicalNondegeneracy) : MainUniformStatement :=
  main_of_uniform_physical_facts
    (uniformBelow_of_no_badSequence hexistence)
    (uniformBelow_of_no_badSequence huniqueness)
    (uniformBelow_of_no_badSequence hnondegeneracy)

end DominantFiveBody
