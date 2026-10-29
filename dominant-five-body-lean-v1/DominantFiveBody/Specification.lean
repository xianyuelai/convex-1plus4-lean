import DominantFiveBody.Definitions

/-! # Theorem 1.1 specification (a proposition, not a proved theorem)

The uniform cutoff comes before the positive mass-ratio vector. Uniqueness uses
the original geometric central-configuration equation and the label-preserving
SO(2), translation, positive-scale relation. Nondegeneracy is the actual second
derivative on the geometrically defined six-dimensional shape space.
-/

namespace DominantFiveBody

/-- Paper Theorem 1.1, label `thm:main`. This module contains only the
specification; `DominantFiveBody.main_uniform` is supplied in `Main.lean`. -/
def MainUniformStatement : Prop :=
  ∃ δ : ℝ, 0 < δ ∧
    ∀ μ : MassRatio, PositiveRatio μ →
    ∀ ε : ℝ, 0 < ε → ε < δ →
    ∀ σ : HullOrder,
      ∃ x : Configuration,
        StrictConvexCentralConfiguration (masses ε μ) σ x ∧
        (∀ y : Configuration,
          StrictConvexCentralConfiguration (masses ε μ) σ y → OrientedSimilar x y) ∧
        (∀ y : Configuration,
          StrictConvexCentralConfiguration (masses ε μ) σ y →
            NondegenerateCentralConfiguration (masses ε μ) y)

end DominantFiveBody
