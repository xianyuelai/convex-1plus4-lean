import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Calculus.FDeriv.Defs
import Mathlib.LinearAlgebra.Determinant
import Mathlib.LinearAlgebra.FiniteDimensional.Basic

/-!
# Physical objects for the supplied 19-page manuscript

Source: `source/dominant_five_body_ARMA_rewritten.tex`, Kaitai Xiao.
Five labels are 0,1,2,3,4; satellite indices in `Fin 4` are shifted by `Fin.succ`.
These are geometric and differential definitions, not theorem interfaces.
Division is total in Lean: analytical claims must establish collision freedom,
positive masses, and any other required nonzero denominators separately.
-/

noncomputable section
open scoped BigOperators

namespace DominantFiveBody

abbrev Label := Fin 5
abbrev Satellite := Fin 4
abbrev Plane := EuclideanSpace ℝ (Fin 2)
abbrev Configuration := Label → Plane
abbrev SatelliteConfiguration := Satellite → Plane
abbrev MassVector := Label → ℝ
abbrev MassRatio := Satellite → ℝ

def point (a b : ℝ) : Plane := WithLp.toLp 2 ![a, b]

def PositiveRatio (μ : MassRatio) : Prop :=
  (∀ i, 0 < μ i) ∧ ∑ i, μ i = 1

/-- Equation `eq:masses`. The primary mass is always one. -/
def masses (ε : ℝ) (μ : MassRatio) : MassVector :=
  Fin.cases 1 (fun i => ε * μ i)

def PositiveMasses (m : MassVector) : Prop := ∀ i, 0 < m i

def totalMass (m : MassVector) : ℝ := ∑ i, m i

def weightedPosition (m : MassVector) (x : Configuration) : Plane :=
  ∑ i, m i • x i

def massCenter (m : MassVector) (x : Configuration) : Plane :=
  (totalMass m)⁻¹ • weightedPosition m x

def centered (m : MassVector) (x : Configuration) : Configuration :=
  fun i => x i - massCenter m x

/-- Primary-relative positions, distinct from the centered positions. -/
def primaryRelative (x : Configuration) : Configuration := fun i => x i - x 0

def satellitesRelative (x : Configuration) : SatelliteConfiguration :=
  fun i => primaryRelative x i.succ

def liftRelative (q : SatelliteConfiguration) : Configuration := Fin.cases 0 q

def relativeAverage (μ : MassRatio) (q : SatelliteConfiguration) : Plane :=
  ∑ i, μ i • q i

/-- §3: `x₀=-ε/(1+ε) X`, `xᵢ=qᵢ-ε/(1+ε) X`. -/
def centeredFromRelative (ε : ℝ) (μ : MassRatio)
    (q : SatelliteConfiguration) : Configuration :=
  fun i => liftRelative q i - (ε / (1 + ε)) • relativeAverage μ q

def pairDistance (x : Configuration) (i j : Label) : ℝ := ‖x i - x j‖

def CollisionFree (x : Configuration) : Prop :=
  ∀ i j, i ≠ j → x i ≠ x j

def pairs : Finset (Label × Label) := Finset.univ.filter (fun p => p.1 < p.2)

/-- Equation `eq:UI`: all ten unordered Newtonian interactions. -/
def potential (m : MassVector) (x : Configuration) : ℝ :=
  ∑ p ∈ pairs, m p.1 * m p.2 / pairDistance x p.1 p.2

def inertia (m : MassVector) (x : Configuration) : ℝ :=
  ∑ i, m i * ‖x i‖ ^ 2

/-- For lam=1 this is exactly the paper's `G=U+I/2`. -/
def augmentedPotential (m : MassVector) (lam : ℝ) (x : Configuration) : ℝ :=
  potential m x + lam / 2 * inertia m x

def acceleration (m : MassVector) (x : Configuration) (i : Label) : Plane :=
  ∑ j ∈ Finset.univ.erase i,
    (m j / pairDistance x i j ^ 3) • (x j - x i)

def MultiplierEquation (m : MassVector) (x : Configuration) (lam : ℝ) : Prop :=
  ∀ i, acceleration m x i = (-lam) • (x i - massCenter m x)

/-- Original geometric central configuration; lam is not fixed. -/
def CentralConfiguration (m : MassVector) (x : Configuration) : Prop :=
  CollisionFree x ∧ ∃ lam : ℝ, 0 < lam ∧ MultiplierEquation m x lam

/-- Equation `eq:cc`: centered, multiplier one. -/
def NormalizedCentralConfiguration (m : MassVector) (x : Configuration) : Prop :=
  CollisionFree x ∧ weightedPosition m x = 0 ∧
    ∀ i, acceleration m x i = -x i

def det2 (u v : Plane) : ℝ := u 0 * v 1 - u 1 * v 0

def orientedArea (x : Configuration) (i j k : Label) : ℝ :=
  det2 (x j - x i) (x k - x i)

/-- An oriented hull list starting at the primary; all satellite permutations occur.
The addition `k+1` in the edge definition below is modulo five. -/
structure HullOrder where
  labels : Equiv.Perm Label
  primary_first : labels 0 = 0

/-- All three other points are strictly left of every directed hull edge.
The primary is included as a hull vertex. -/
def StrictConvexInOrder (σ : HullOrder) (x : Configuration) : Prop :=
  ∀ k j : Label, j ≠ k → j ≠ k + 1 →
    0 < orientedArea x (σ.labels k) (σ.labels (k + 1)) (σ.labels j)

def StrictConvexCentralConfiguration (m : MassVector) (σ : HullOrder)
    (x : Configuration) : Prop :=
  CentralConfiguration m x ∧ StrictConvexInOrder σ x

/-- Exactly translation, positive scaling, and an SO(2) transformation.
No reflection or relabeling is present. -/
def OrientedSimilar (x y : Configuration) : Prop :=
  ∃ (b : Plane) (a : ℝ) (R : Plane ≃ₗᵢ[ℝ] Plane),
    0 < a ∧ LinearMap.det R.toLinearEquiv.toLinearMap = 1 ∧
    ∀ i, y i = b + a • R (x i)

def quarterTurn (v : Plane) : Plane := point (-v 1) (v 0)

def rotationDirection (x : Configuration) : Configuration := fun i => quarterTurn (x i)

def massInner (m : MassVector) (v w : Configuration) : ℝ :=
  ∑ i, m i * inner ℝ (v i) (w i)

def weightedPositionLinear (m : MassVector) : Configuration →ₗ[ℝ] Plane :=
  ∑ i, m i • (LinearMap.proj i : Configuration →ₗ[ℝ] Plane)

def massInnerRight (m : MassVector) (v : Configuration) : Configuration →ₗ[ℝ] ℝ :=
  ∑ i, m i • ((innerₗ Plane) (v i)).comp (LinearMap.proj i)

/-- §3 `lem:hessian`: centered variations, fixed inertia tangent, rotation removed.
For a raw configuration, radial and rotation directions use its centered version.
No dimension or nondegeneracy claim is included in this submodule's definition. -/
def shapeSpace (m : MassVector) (x : Configuration) : Submodule ℝ Configuration :=
  (weightedPositionLinear m).ker ⊓
    ((massInnerRight m (centered m x)).ker ⊓
      (massInnerRight m (rotationDirection (centered m x))).ker)

/-- The actual second Fréchet derivative, not a residual Jacobian. Its regularity
and equality with explicit matrix expressions are separate proof obligations. -/
def physicalHessian (m : MassVector) (lam : ℝ) (x v w : Configuration) : ℝ :=
  (fderiv ℝ (fderiv ℝ (augmentedPotential m lam)) x) v w

/-- The bilinear kernel of the Hessian restricted to the geometric shape space. -/
def ShapeHessianNondegenerate (m : MassVector) (lam : ℝ) (x : Configuration) : Prop :=
  ∀ v ∈ shapeSpace m x,
    (∀ w ∈ shapeSpace m x, physicalHessian m lam x v w = 0) → v = 0

def NondegenerateCentralConfiguration (m : MassVector) (x : Configuration) : Prop :=
  CollisionFree x ∧ ∃ lam : ℝ, 0 < lam ∧ MultiplierEquation m x lam ∧
    Module.finrank ℝ (shapeSpace m x) = 6 ∧ ShapeHessianNondegenerate m lam x

end DominantFiveBody

