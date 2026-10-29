import DominantFiveBody.Definitions
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

/-! # The physical, mass-divided satellite equations

The formulae below are written before specializing any ratio to zero. No
division by a satellite mass is performed. They are the physical equations,
not the signed-scale smooth extensions of §5 (which remain unimplemented).
-/

noncomputable section
open scoped BigOperators

namespace DominantFiveBody

def polarPoint (r θ : ℝ) : Plane := point (r * Real.cos θ) (r * Real.sin θ)

def polarSatellites (r θ : Satellite → ℝ) : SatelliteConfiguration :=
  fun i => polarPoint (r i) (θ i)

def satelliteDistance (q : SatelliteConfiguration) (i j : Satellite) : ℝ := ‖q i - q j‖

def relativeField (μ : MassRatio) (q : SatelliteConfiguration) : Plane :=
  ∑ i, (μ i / ‖q i‖ ^ 3) • q i

/-- Equation `eq:G` in the genuine positive-mass physical variables. -/
def vectorResidual (ε : ℝ) (μ : MassRatio) (q : SatelliteConfiguration)
    (i : Satellite) : Plane :=
  q i - (‖q i‖ ^ 3)⁻¹ • q i +
    ε • (∑ j ∈ Finset.univ.erase i,
      (μ j / satelliteDistance q i j ^ 3) • (q j - q i)) -
    ε • relativeField μ q

/-- Equation `eq:R`; defined explicitly also when `μ i=0`. -/
def radialResidual (ε : ℝ) (μ r θ : Satellite → ℝ) (i : Satellite) : ℝ :=
  r i - (r i ^ 2)⁻¹ -
    ε * (∑ j ∈ Finset.univ.erase i,
      μ j * (r i - r j * Real.cos (θ j - θ i)) /
        satelliteDistance (polarSatellites r θ) i j ^ 3) -
    ε / (1 + ε) * inner ℝ (relativeAverage μ (polarSatellites r θ))
      (polarPoint 1 (θ i))

/-- Equation `eq:T`; the missing angular equation requires a positive omitted mass. -/
def angularResidual (ε : ℝ) (μ r θ : Satellite → ℝ) (i : Satellite) : ℝ :=
  ∑ j ∈ Finset.univ.erase i,
    μ j * r i * r j * Real.sin (θ j - θ i) *
      ((satelliteDistance (polarSatellites r θ) i j ^ 3)⁻¹ - (1 + ε)⁻¹)

/-- Equation `eq:Q`; retained as a probe equation at zero ratios. -/
def tangentialResidual (μ r θ : Satellite → ℝ) (i : Satellite) : ℝ :=
  ∑ j ∈ Finset.univ.erase i,
    μ j * r j * Real.sin (θ j - θ i) *
      ((satelliteDistance (polarSatellites r θ) i j ^ 3)⁻¹ - (r j ^ 3)⁻¹)

/-- The §3 mass metric `C=diag(μ)-ε/(1+ε) μ μᵀ`. -/
def relativeMassMatrix (ε : ℝ) (μ : MassRatio) : Matrix Satellite Satellite ℝ :=
  fun i j => (if i = j then μ i else 0) - ε / (1 + ε) * μ i * μ j

end DominantFiveBody
