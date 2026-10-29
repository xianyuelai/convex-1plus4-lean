import DominantFiveBody.BoundaryJacobian
import DominantFiveBody.Coorbital
import DominantFiveBody.CoorbitalModel
import DominantFiveBody.Definitions
import DominantFiveBody.HessianCorrespondence
import DominantFiveBody.LocalContinuation
import DominantFiveBody.PolarGaugeTransport
import DominantFiveBody.RadialDirectSum
import DominantFiveBody.RelativeAction
import DominantFiveBody.Residuals
import DominantFiveBody.SectionSevenEqualitySet
import DominantFiveBody.SliceConnection
import Lean
noncomputable section
open scoped BigOperators ContDiff Matrix.Norms.Operator Topology
universe u_1 u_2 u_3 u_4
set_option linter.unusedVariables false
example : ℝ := @DominantFiveBody.Coorbital.h
example : @Eq (ℝ) (@DominantFiveBody.Coorbital.h) (Real.pi / 3) := rfl
#print DominantFiveBody.Coorbital.h
#print axioms DominantFiveBody.Coorbital.h
example : ℝ → ℝ := @DominantFiveBody.Coorbital.kappa
example : @Eq (ℝ → ℝ) (@DominantFiveBody.Coorbital.kappa) (fun (t : ℝ) => (2 - Real.sin (t / 2) ^ 2) / (8 * Real.sin (t / 2) ^ 3) + Real.cos t) := rfl
#print DominantFiveBody.Coorbital.kappa
#print axioms DominantFiveBody.Coorbital.kappa
example : ℝ → ℝ := @DominantFiveBody.Coorbital.kappaPrime
example : @Eq (ℝ → ℝ) (@DominantFiveBody.Coorbital.kappaPrime) (fun (t : ℝ) => -Real.cos (t / 2) / (16 * Real.sin (t / 2) ^ 4) * (6 - Real.sin (t / 2) ^ 2 + 32 * Real.sin (t / 2) ^ 5)) := rfl
#print DominantFiveBody.Coorbital.kappaPrime
#print axioms DominantFiveBody.Coorbital.kappaPrime
example : ℝ → ℝ := @DominantFiveBody.Coorbital.kernelF
example : @Eq (ℝ → ℝ) (@DominantFiveBody.Coorbital.kernelF) (fun (t : ℝ) => Real.sin t * ((2 * Real.sin (t / 2))⁻¹ ^ 3 - 1)) := rfl
#print DominantFiveBody.Coorbital.kernelF
#print axioms DominantFiveBody.Coorbital.kernelF
example : ℝ → ℝ := @DominantFiveBody.Coorbital.pairPotential
example : @Eq (ℝ → ℝ) (@DominantFiveBody.Coorbital.pairPotential) (fun (t : ℝ) => (2 * Real.sin (t / 2))⁻¹ + 1 - Real.cos t) := rfl
#print DominantFiveBody.Coorbital.pairPotential
#print axioms DominantFiveBody.Coorbital.pairPotential
example : ℝ → ℝ := @DominantFiveBody.Coorbital.positiveRemainder
example : @Eq (ℝ → ℝ) (@DominantFiveBody.Coorbital.positiveRemainder) (fun (t : ℝ) => DominantFiveBody.Coorbital.kappa t - DominantFiveBody.Coorbital.slopeCoefficient t) := rfl
#print DominantFiveBody.Coorbital.positiveRemainder
#print axioms DominantFiveBody.Coorbital.positiveRemainder
example : ℝ → ℝ := @DominantFiveBody.Coorbital.slopeCoefficient
example : @Eq (ℝ → ℝ) (@DominantFiveBody.Coorbital.slopeCoefficient) (fun (t : ℝ) =>
  if t < DominantFiveBody.Coorbital.h then DominantFiveBody.Coorbital.kernelF t / (DominantFiveBody.Coorbital.h - t)
  else if t = DominantFiveBody.Coorbital.h then 0 else DominantFiveBody.Coorbital.kernelF t / (Real.pi - t)) := rfl
#print DominantFiveBody.Coorbital.slopeCoefficient
#print axioms DominantFiveBody.Coorbital.slopeCoefficient
example : Type := @DominantFiveBody.HullOrder
example : (labels : Equiv.Perm DominantFiveBody.Label) →
  (labels : DominantFiveBody.Label → DominantFiveBody.Label) 0 = 0 → DominantFiveBody.HullOrder := @DominantFiveBody.HullOrder.mk
#print DominantFiveBody.HullOrder
#print axioms DominantFiveBody.HullOrder
example : DominantFiveBody.MassVector → DominantFiveBody.Configuration → Prop := @DominantFiveBody.NormalizedCentralConfiguration
example : @Eq (DominantFiveBody.MassVector → DominantFiveBody.Configuration → Prop) (@DominantFiveBody.NormalizedCentralConfiguration) (fun (m : DominantFiveBody.MassVector) (x : DominantFiveBody.Configuration) =>
  DominantFiveBody.CollisionFree x ∧
    DominantFiveBody.weightedPosition m x = 0 ∧
      ∀ (i : DominantFiveBody.Label), DominantFiveBody.acceleration m x i = -x i) := rfl
#print DominantFiveBody.NormalizedCentralConfiguration
#print axioms DominantFiveBody.NormalizedCentralConfiguration
example : DominantFiveBody.Configuration → DominantFiveBody.Configuration → Prop := @DominantFiveBody.OrientedSimilar
example : @Eq (DominantFiveBody.Configuration → DominantFiveBody.Configuration → Prop) (@DominantFiveBody.OrientedSimilar) (fun (x y : DominantFiveBody.Configuration) =>
  ∃ (b : DominantFiveBody.Plane) (a : ℝ) (R : DominantFiveBody.Plane ≃ₗᵢ[ℝ] DominantFiveBody.Plane),
    0 < a ∧
      (LinearMap.det : (DominantFiveBody.Plane →ₗ[ℝ] DominantFiveBody.Plane) → ℝ)
            (↑R.toLinearEquiv : DominantFiveBody.Plane →ₗ[ℝ] DominantFiveBody.Plane) =
          1 ∧
        ∀ (i : DominantFiveBody.Label), y i = b + a • (R : DominantFiveBody.Plane → DominantFiveBody.Plane) (x i)) := rfl
#print DominantFiveBody.OrientedSimilar
#print axioms DominantFiveBody.OrientedSimilar
example : DominantFiveBody.MassRatio → Prop := @DominantFiveBody.PositiveRatio
example : @Eq (DominantFiveBody.MassRatio → Prop) (@DominantFiveBody.PositiveRatio) (fun (μ : DominantFiveBody.MassRatio) =>
  (∀ (i : DominantFiveBody.Satellite), 0 < μ i) ∧ ∑ i : DominantFiveBody.Satellite, μ i = 1) := rfl
#print DominantFiveBody.PositiveRatio
#print axioms DominantFiveBody.PositiveRatio
example : DominantFiveBody.MassVector → DominantFiveBody.Configuration → DominantFiveBody.Label → DominantFiveBody.Plane := @DominantFiveBody.acceleration
example : @Eq (DominantFiveBody.MassVector → DominantFiveBody.Configuration → DominantFiveBody.Label → DominantFiveBody.Plane) (@DominantFiveBody.acceleration) (fun (m : DominantFiveBody.MassVector) (x : DominantFiveBody.Configuration) (i : DominantFiveBody.Label) =>
  ∑ j ∈ Finset.univ.erase i, (m j / DominantFiveBody.pairDistance x i j ^ 3) • (x j - x i)) := rfl
#print DominantFiveBody.acceleration
#print axioms DominantFiveBody.acceleration
example : (DominantFiveBody.Satellite → ℝ) →
  (DominantFiveBody.Satellite → ℝ) → Matrix DominantFiveBody.Satellite DominantFiveBody.Satellite ℝ := @DominantFiveBody.angularJacobian
example : @Eq ((DominantFiveBody.Satellite → ℝ) →
  (DominantFiveBody.Satellite → ℝ) → Matrix DominantFiveBody.Satellite DominantFiveBody.Satellite ℝ) (@DominantFiveBody.angularJacobian) (fun (mass theta : DominantFiveBody.Satellite → ℝ) (i j : DominantFiveBody.Satellite) =>
  if i = j then ∑ k ∈ Finset.univ.erase i, mass k * DominantFiveBody.Coorbital.kappa |theta k - theta i|
  else -mass j * DominantFiveBody.Coorbital.kappa |theta j - theta i|) := rfl
#print DominantFiveBody.angularJacobian
#print axioms DominantFiveBody.angularJacobian
example : ℝ →
  (DominantFiveBody.Satellite → ℝ) →
    (DominantFiveBody.Satellite → ℝ) → (DominantFiveBody.Satellite → ℝ) → DominantFiveBody.Satellite → ℝ := @DominantFiveBody.angularResidual
example : @Eq (ℝ →
  (DominantFiveBody.Satellite → ℝ) →
    (DominantFiveBody.Satellite → ℝ) → (DominantFiveBody.Satellite → ℝ) → DominantFiveBody.Satellite → ℝ) (@DominantFiveBody.angularResidual) (fun (ε : ℝ) (μ r θ : DominantFiveBody.Satellite → ℝ) (i : DominantFiveBody.Satellite) =>
  ∑ j ∈ Finset.univ.erase i,
    μ j * r i * r j * Real.sin (θ j - θ i) *
      ((DominantFiveBody.satelliteDistance (DominantFiveBody.polarSatellites r θ) i j ^ 3)⁻¹ - (1 + ε)⁻¹)) := rfl
#print DominantFiveBody.angularResidual
#print axioms DominantFiveBody.angularResidual
example : DominantFiveBody.MassVector → ℝ → DominantFiveBody.Configuration → ℝ := @DominantFiveBody.augmentedPotential
example : @Eq (DominantFiveBody.MassVector → ℝ → DominantFiveBody.Configuration → ℝ) (@DominantFiveBody.augmentedPotential) (fun (m : DominantFiveBody.MassVector) (lam : ℝ) (x : DominantFiveBody.Configuration) =>
  DominantFiveBody.potential m x + lam / 2 * DominantFiveBody.inertia m x) := rfl
#print DominantFiveBody.augmentedPotential
#print axioms DominantFiveBody.augmentedPotential
example : ℝ → (ℝ → DominantFiveBody.SliceCoordinates) → (ℝ → DominantFiveBody.SliceCoordinates) → Set ℝ := @DominantFiveBody.branchEqualitySet
example : @Eq (ℝ → (ℝ → DominantFiveBody.SliceCoordinates) → (ℝ → DominantFiveBody.SliceCoordinates) → Set ℝ) (@DominantFiveBody.branchEqualitySet) (fun (radius : ℝ) (first second : ℝ → DominantFiveBody.SliceCoordinates) =>
  {s : ℝ | s ∈ Set.Ico 0 radius ∧ first s = second s}) := rfl
#print DominantFiveBody.branchEqualitySet
#print axioms DominantFiveBody.branchEqualitySet
example : ℝ → DominantFiveBody.MassRatio → DominantFiveBody.SatelliteConfiguration → DominantFiveBody.Configuration := @DominantFiveBody.centeredFromRelative
example : @Eq (ℝ → DominantFiveBody.MassRatio → DominantFiveBody.SatelliteConfiguration → DominantFiveBody.Configuration) (@DominantFiveBody.centeredFromRelative) (fun (ε : ℝ) (μ : DominantFiveBody.MassRatio) (q : DominantFiveBody.SatelliteConfiguration)
    (i : DominantFiveBody.Label) =>
  DominantFiveBody.liftRelative q i - (ε / (1 + ε)) • DominantFiveBody.relativeAverage μ q) := rfl
#print DominantFiveBody.centeredFromRelative
#print axioms DominantFiveBody.centeredFromRelative
example : DominantFiveBody.MassVector → Submodule ℝ DominantFiveBody.Configuration := @DominantFiveBody.centeredVariationSpace
example : @Eq (DominantFiveBody.MassVector → Submodule ℝ DominantFiveBody.Configuration) (@DominantFiveBody.centeredVariationSpace) (fun (m : DominantFiveBody.MassVector) => (DominantFiveBody.weightedPositionLinear m).ker) := rfl
#print DominantFiveBody.centeredVariationSpace
#print axioms DominantFiveBody.centeredVariationSpace
example : (DominantFiveBody.Satellite → ℝ) → DominantFiveBody.Satellite → DominantFiveBody.Satellite → ℝ := @DominantFiveBody.coorbitalDistance
example : @Eq ((DominantFiveBody.Satellite → ℝ) → DominantFiveBody.Satellite → DominantFiveBody.Satellite → ℝ) (@DominantFiveBody.coorbitalDistance) (fun (θ : DominantFiveBody.Satellite → ℝ) (i j : DominantFiveBody.Satellite) =>
  ‖DominantFiveBody.point (Real.cos (θ i)) (Real.sin (θ i)) - DominantFiveBody.point (Real.cos (θ j)) (Real.sin (θ j))‖) := rfl
#print DominantFiveBody.coorbitalDistance
#print axioms DominantFiveBody.coorbitalDistance
example : ℝ → ℝ := @DominantFiveBody.coorbitalKernel
example : @Eq (ℝ → ℝ) (@DominantFiveBody.coorbitalKernel) (fun (t : ℝ) => if 0 ≤ t then DominantFiveBody.Coorbital.kernelF t else -DominantFiveBody.Coorbital.kernelF (-t)) := rfl
#print DominantFiveBody.coorbitalKernel
#print axioms DominantFiveBody.coorbitalKernel
example : (DominantFiveBody.Satellite → ℝ) → Matrix DominantFiveBody.Satellite DominantFiveBody.Satellite ℝ := @DominantFiveBody.coorbitalMatrix
example : @Eq ((DominantFiveBody.Satellite → ℝ) → Matrix DominantFiveBody.Satellite DominantFiveBody.Satellite ℝ) (@DominantFiveBody.coorbitalMatrix) (fun (θ : DominantFiveBody.Satellite → ℝ) (i j : DominantFiveBody.Satellite) =>
  if i = j then 0 else DominantFiveBody.coorbitalKernel (θ j - θ i)) := rfl
#print DominantFiveBody.coorbitalMatrix
#print axioms DominantFiveBody.coorbitalMatrix
example : (DominantFiveBody.Satellite → ℝ) → (DominantFiveBody.Satellite → ℝ) → ℝ := @DominantFiveBody.coorbitalPotential
example : @Eq ((DominantFiveBody.Satellite → ℝ) → (DominantFiveBody.Satellite → ℝ) → ℝ) (@DominantFiveBody.coorbitalPotential) (fun (μ θ : DominantFiveBody.Satellite → ℝ) =>
  ∑ p ∈ DominantFiveBody.satellitePairs,
    μ p.1 * μ p.2 *
      ((DominantFiveBody.coorbitalDistance θ p.1 p.2)⁻¹ + DominantFiveBody.coorbitalDistance θ p.1 p.2 ^ 2 / 2)) := rfl
#print DominantFiveBody.coorbitalPotential
#print axioms DominantFiveBody.coorbitalPotential
example : (DominantFiveBody.Satellite → ℝ) → (DominantFiveBody.Satellite → ℝ) → DominantFiveBody.Satellite → ℝ := @DominantFiveBody.coorbitalResidual
example : @Eq ((DominantFiveBody.Satellite → ℝ) → (DominantFiveBody.Satellite → ℝ) → DominantFiveBody.Satellite → ℝ) (@DominantFiveBody.coorbitalResidual) (fun (μ θ : DominantFiveBody.Satellite → ℝ) (i : DominantFiveBody.Satellite) =>
  ∑ j ∈ Finset.univ.erase i, μ j * DominantFiveBody.coorbitalKernel (θ j - θ i)) := rfl
#print DominantFiveBody.coorbitalResidual
#print axioms DominantFiveBody.coorbitalResidual
example : DominantFiveBody.MassVector → DominantFiveBody.Configuration → ℝ := @DominantFiveBody.inertia
example : @Eq (DominantFiveBody.MassVector → DominantFiveBody.Configuration → ℝ) (@DominantFiveBody.inertia) (fun (m : DominantFiveBody.MassVector) (x : DominantFiveBody.Configuration) =>
  ∑ i : DominantFiveBody.Label, m i * ‖x i‖ ^ 2) := rfl
#print DominantFiveBody.inertia
#print axioms DominantFiveBody.inertia
example : DominantFiveBody.MassVector → DominantFiveBody.Configuration → Submodule ℝ DominantFiveBody.Configuration := @DominantFiveBody.inertiaTangentSpace
example : @Eq (DominantFiveBody.MassVector → DominantFiveBody.Configuration → Submodule ℝ DominantFiveBody.Configuration) (@DominantFiveBody.inertiaTangentSpace) (fun (m : DominantFiveBody.MassVector) (x : DominantFiveBody.Configuration) =>
  DominantFiveBody.centeredVariationSpace m ⊓ (DominantFiveBody.massInnerRight m x).ker) := rfl
#print DominantFiveBody.inertiaTangentSpace
#print axioms DominantFiveBody.inertiaTangentSpace
example : DominantFiveBody.SatelliteConfiguration → DominantFiveBody.Configuration := @DominantFiveBody.liftRelative
example : @Eq (DominantFiveBody.SatelliteConfiguration → DominantFiveBody.Configuration) (@DominantFiveBody.liftRelative) (fun (q : DominantFiveBody.SatelliteConfiguration) (i : Fin (4 + 1)) => Fin.cases 0 q i) := rfl
#print DominantFiveBody.liftRelative
#print axioms DominantFiveBody.liftRelative
example : ℝ → DominantFiveBody.MassRatio → DominantFiveBody.MassVector := @DominantFiveBody.masses
example : @Eq (ℝ → DominantFiveBody.MassRatio → DominantFiveBody.MassVector) (@DominantFiveBody.masses) (fun (ε : ℝ) (μ : DominantFiveBody.MassRatio) (i : Fin (4 + 1)) => Fin.cases 1 (fun (i : Fin 4) => ε * μ i) i) := rfl
#print DominantFiveBody.masses
#print axioms DominantFiveBody.masses
example : DominantFiveBody.HullOrder →
  (DominantFiveBody.Satellite → ℝ) → (DominantFiveBody.Satellite → ℝ) → DominantFiveBody.SliceCoordinates := @DominantFiveBody.orderedPolarSlice
example : @Eq (DominantFiveBody.HullOrder →
  (DominantFiveBody.Satellite → ℝ) → (DominantFiveBody.Satellite → ℝ) → DominantFiveBody.SliceCoordinates) (@DominantFiveBody.orderedPolarSlice) (fun (sigma : DominantFiveBody.HullOrder) (r theta : DominantFiveBody.Satellite → ℝ) =>
  have e := DominantFiveBody.hullSatellitePermutation sigma;
  DominantFiveBody.polarSlice (r ∘ (⇑e : DominantFiveBody.Satellite → DominantFiveBody.Satellite))
    fun (i : DominantFiveBody.Satellite) =>
    theta ((e : DominantFiveBody.Satellite → DominantFiveBody.Satellite) i) -
      theta ((e : DominantFiveBody.Satellite → DominantFiveBody.Satellite) 0)) := rfl
#print DominantFiveBody.orderedPolarSlice
#print axioms DominantFiveBody.orderedPolarSlice
example : DominantFiveBody.PositiveMassRatio → ℝ → DominantFiveBody.SliceCoordinates → Prop := @DominantFiveBody.orderedSliceRoot
example : @Eq (DominantFiveBody.PositiveMassRatio → ℝ → DominantFiveBody.SliceCoordinates → Prop) (@DominantFiveBody.orderedSliceRoot) (fun (mu : DominantFiveBody.PositiveMassRatio) (eps : ℝ) (y : DominantFiveBody.SliceCoordinates) =>
  DominantFiveBody.SliceRegular (eps, (↑mu : DominantFiveBody.MassRatio)) y ∧
    DominantFiveBody.OrderedSemicircle (DominantFiveBody.sliceAngles y) ∧
      DominantFiveBody.StrictConvexInOrder DominantFiveBody.standardHullOrder
          (DominantFiveBody.slicePhysicalConfiguration (eps, (↑mu : DominantFiveBody.MassRatio)) y) ∧
        DominantFiveBody.reducedResidual (eps, (↑mu : DominantFiveBody.MassRatio)) y = 0) := rfl
#print DominantFiveBody.orderedSliceRoot
#print axioms DominantFiveBody.orderedSliceRoot
example : DominantFiveBody.Configuration → DominantFiveBody.Label → DominantFiveBody.Label → ℝ := @DominantFiveBody.pairDistance
example : @Eq (DominantFiveBody.Configuration → DominantFiveBody.Label → DominantFiveBody.Label → ℝ) (@DominantFiveBody.pairDistance) (fun (x : DominantFiveBody.Configuration) (i j : DominantFiveBody.Label) => ‖x i - x j‖) := rfl
#print DominantFiveBody.pairDistance
#print axioms DominantFiveBody.pairDistance
example : Finset (DominantFiveBody.Label × DominantFiveBody.Label) := @DominantFiveBody.pairs
example : @Eq (Finset (DominantFiveBody.Label × DominantFiveBody.Label)) (@DominantFiveBody.pairs) ({p : DominantFiveBody.Label × DominantFiveBody.Label | p.1 < p.2}) := rfl
#print DominantFiveBody.pairs
#print axioms DominantFiveBody.pairs
example : ℝ → ℝ → DominantFiveBody.Plane := @DominantFiveBody.polarPoint
example : @Eq (ℝ → ℝ → DominantFiveBody.Plane) (@DominantFiveBody.polarPoint) (fun (r θ : ℝ) => DominantFiveBody.point (r * Real.cos θ) (r * Real.sin θ)) := rfl
#print DominantFiveBody.polarPoint
#print axioms DominantFiveBody.polarPoint
example : (DominantFiveBody.Satellite → ℝ) → (DominantFiveBody.Satellite → ℝ) → DominantFiveBody.SatelliteConfiguration := @DominantFiveBody.polarSatellites
example : @Eq ((DominantFiveBody.Satellite → ℝ) → (DominantFiveBody.Satellite → ℝ) → DominantFiveBody.SatelliteConfiguration) (@DominantFiveBody.polarSatellites) (fun (r θ : DominantFiveBody.Satellite → ℝ) (i : DominantFiveBody.Satellite) => DominantFiveBody.polarPoint (r i) (θ i)) := rfl
#print DominantFiveBody.polarSatellites
#print axioms DominantFiveBody.polarSatellites
example : DominantFiveBody.MassVector → DominantFiveBody.Configuration → ℝ := @DominantFiveBody.potential
example : @Eq (DominantFiveBody.MassVector → DominantFiveBody.Configuration → ℝ) (@DominantFiveBody.potential) (fun (m : DominantFiveBody.MassVector) (x : DominantFiveBody.Configuration) =>
  ∑ p ∈ DominantFiveBody.pairs, m p.1 * m p.2 / DominantFiveBody.pairDistance x p.1 p.2) := rfl
#print DominantFiveBody.potential
#print axioms DominantFiveBody.potential
example : DominantFiveBody.Plane → DominantFiveBody.Plane := @DominantFiveBody.quarterTurn
example : @Eq (DominantFiveBody.Plane → DominantFiveBody.Plane) (@DominantFiveBody.quarterTurn) (fun (v : DominantFiveBody.Plane) => DominantFiveBody.point (-v.ofLp 1) (v.ofLp 0)) := rfl
#print DominantFiveBody.quarterTurn
#print axioms DominantFiveBody.quarterTurn
example : ℝ →
  (DominantFiveBody.Satellite → ℝ) →
    (DominantFiveBody.Satellite → ℝ) → (DominantFiveBody.Satellite → ℝ) → DominantFiveBody.Satellite → ℝ := @DominantFiveBody.radialResidual
example : @Eq (ℝ →
  (DominantFiveBody.Satellite → ℝ) →
    (DominantFiveBody.Satellite → ℝ) → (DominantFiveBody.Satellite → ℝ) → DominantFiveBody.Satellite → ℝ) (@DominantFiveBody.radialResidual) (fun (ε : ℝ) (μ r θ : DominantFiveBody.Satellite → ℝ) (i : DominantFiveBody.Satellite) =>
  r i - (r i ^ 2)⁻¹ -
      ε *
        ∑ j ∈ Finset.univ.erase i,
          μ j * (r i - r j * Real.cos (θ j - θ i)) /
            DominantFiveBody.satelliteDistance (DominantFiveBody.polarSatellites r θ) i j ^ 3 -
    ε / (1 + ε) *
      Inner.inner ℝ (DominantFiveBody.relativeAverage μ (DominantFiveBody.polarSatellites r θ))
        (DominantFiveBody.polarPoint 1 (θ i))) := rfl
#print DominantFiveBody.radialResidual
#print axioms DominantFiveBody.radialResidual
example : ℝ → DominantFiveBody.MassRatio → DominantFiveBody.SatelliteConfiguration → ℝ := @DominantFiveBody.relativeAction
example : @Eq (ℝ → DominantFiveBody.MassRatio → DominantFiveBody.SatelliteConfiguration → ℝ) (@DominantFiveBody.relativeAction) (fun (eps : ℝ) (mu : DominantFiveBody.MassRatio) (q : DominantFiveBody.SatelliteConfiguration) =>
  ∑ i : DominantFiveBody.Satellite, mu i * (‖q i‖⁻¹ + ‖q i‖ ^ 2 / 2) +
      eps * DominantFiveBody.relativePairPotential mu q -
    eps / (1 + eps) / 2 * ‖DominantFiveBody.relativeAverage mu q‖ ^ 2) := rfl
#print DominantFiveBody.relativeAction
#print axioms DominantFiveBody.relativeAction
example : DominantFiveBody.MassRatio → DominantFiveBody.SatelliteConfiguration → DominantFiveBody.Plane := @DominantFiveBody.relativeAverage
example : @Eq (DominantFiveBody.MassRatio → DominantFiveBody.SatelliteConfiguration → DominantFiveBody.Plane) (@DominantFiveBody.relativeAverage) (fun (μ : DominantFiveBody.MassRatio) (q : DominantFiveBody.SatelliteConfiguration) =>
  ∑ i : DominantFiveBody.Satellite, μ i • q i) := rfl
#print DominantFiveBody.relativeAverage
#print axioms DominantFiveBody.relativeAverage
example : DominantFiveBody.MassRatio → DominantFiveBody.SatelliteConfiguration → DominantFiveBody.Plane := @DominantFiveBody.relativeField
example : @Eq (DominantFiveBody.MassRatio → DominantFiveBody.SatelliteConfiguration → DominantFiveBody.Plane) (@DominantFiveBody.relativeField) (fun (μ : DominantFiveBody.MassRatio) (q : DominantFiveBody.SatelliteConfiguration) =>
  ∑ i : DominantFiveBody.Satellite, (μ i / ‖q i‖ ^ 3) • q i) := rfl
#print DominantFiveBody.relativeField
#print axioms DominantFiveBody.relativeField
example : Finset (DominantFiveBody.Satellite × DominantFiveBody.Satellite) := @DominantFiveBody.satellitePairs
example : @Eq (Finset (DominantFiveBody.Satellite × DominantFiveBody.Satellite)) (@DominantFiveBody.satellitePairs) ({p : DominantFiveBody.Satellite × DominantFiveBody.Satellite | p.1 < p.2}) := rfl
#print DominantFiveBody.satellitePairs
#print axioms DominantFiveBody.satellitePairs
example : DominantFiveBody.Configuration → DominantFiveBody.SatelliteConfiguration := @DominantFiveBody.satellitesRelative
example : @Eq (DominantFiveBody.Configuration → DominantFiveBody.SatelliteConfiguration) (@DominantFiveBody.satellitesRelative) (fun (x : DominantFiveBody.Configuration) (i : DominantFiveBody.Satellite) =>
  DominantFiveBody.primaryRelative x (Fin.succ i)) := rfl
#print DominantFiveBody.satellitesRelative
#print axioms DominantFiveBody.satellitesRelative
example : DominantFiveBody.MassVector → DominantFiveBody.Configuration → Submodule ℝ DominantFiveBody.Configuration := @DominantFiveBody.shapeSpace
example : @Eq (DominantFiveBody.MassVector → DominantFiveBody.Configuration → Submodule ℝ DominantFiveBody.Configuration) (@DominantFiveBody.shapeSpace) (fun (m : DominantFiveBody.MassVector) (x : DominantFiveBody.Configuration) =>
  (DominantFiveBody.weightedPositionLinear m).ker ⊓
    ((DominantFiveBody.massInnerRight m (DominantFiveBody.centered m x)).ker ⊓
      (DominantFiveBody.massInnerRight m (DominantFiveBody.rotationDirection (DominantFiveBody.centered m x))).ker)) := rfl
#print DominantFiveBody.shapeSpace
#print axioms DominantFiveBody.shapeSpace
example : DominantFiveBody.SliceCoordinates → DominantFiveBody.Satellite → ℝ := @DominantFiveBody.sliceAngles
example : @Eq (DominantFiveBody.SliceCoordinates → DominantFiveBody.Satellite → ℝ) (@DominantFiveBody.sliceAngles) (fun (y : DominantFiveBody.SliceCoordinates) (i : Fin (3 + 1)) => Fin.cases 0 (fun (i : Fin 3) => y (Fin.natAdd 4 i)) i) := rfl
#print DominantFiveBody.sliceAngles
#print axioms DominantFiveBody.sliceAngles
example : DominantFiveBody.ContinuationParameter → DominantFiveBody.SliceCoordinates → DominantFiveBody.Configuration := @DominantFiveBody.slicePhysicalConfiguration
example : @Eq (DominantFiveBody.ContinuationParameter → DominantFiveBody.SliceCoordinates → DominantFiveBody.Configuration) (@DominantFiveBody.slicePhysicalConfiguration) (fun (p : DominantFiveBody.ContinuationParameter) (y : DominantFiveBody.SliceCoordinates) =>
  (DominantFiveBody.relativeCenteredContinuous p.1 p.2 :
      DominantFiveBody.SatelliteConfiguration → DominantFiveBody.Configuration)
    (DominantFiveBody.sliceSatellites y)) := rfl
#print DominantFiveBody.slicePhysicalConfiguration
#print axioms DominantFiveBody.slicePhysicalConfiguration
example : DominantFiveBody.SliceCoordinates → DominantFiveBody.Satellite → ℝ := @DominantFiveBody.sliceRadii
example : @Eq (DominantFiveBody.SliceCoordinates → DominantFiveBody.Satellite → ℝ) (@DominantFiveBody.sliceRadii) (fun (y : DominantFiveBody.SliceCoordinates) (i : DominantFiveBody.Satellite) => y (Fin.castAdd 3 i)) := rfl
#print DominantFiveBody.sliceRadii
#print axioms DominantFiveBody.sliceRadii
example : (DominantFiveBody.Satellite → ℝ) →
  (DominantFiveBody.Satellite → ℝ) → (DominantFiveBody.Satellite → ℝ) → DominantFiveBody.Satellite → ℝ := @DominantFiveBody.tangentialResidual
example : @Eq ((DominantFiveBody.Satellite → ℝ) →
  (DominantFiveBody.Satellite → ℝ) → (DominantFiveBody.Satellite → ℝ) → DominantFiveBody.Satellite → ℝ) (@DominantFiveBody.tangentialResidual) (fun (μ r θ : DominantFiveBody.Satellite → ℝ) (i : DominantFiveBody.Satellite) =>
  ∑ j ∈ Finset.univ.erase i,
    μ j * r j * Real.sin (θ j - θ i) *
      ((DominantFiveBody.satelliteDistance (DominantFiveBody.polarSatellites r θ) i j ^ 3)⁻¹ - (r j ^ 3)⁻¹)) := rfl
#print DominantFiveBody.tangentialResidual
#print axioms DominantFiveBody.tangentialResidual
example : ℝ →
  DominantFiveBody.MassRatio →
    DominantFiveBody.SatelliteConfiguration → DominantFiveBody.Satellite → DominantFiveBody.Plane := @DominantFiveBody.vectorResidual
example : @Eq (ℝ →
  DominantFiveBody.MassRatio →
    DominantFiveBody.SatelliteConfiguration → DominantFiveBody.Satellite → DominantFiveBody.Plane) (@DominantFiveBody.vectorResidual) (fun (ε : ℝ) (μ : DominantFiveBody.MassRatio) (q : DominantFiveBody.SatelliteConfiguration)
    (i : DominantFiveBody.Satellite) =>
  q i - (‖q i‖ ^ 3)⁻¹ • q i +
      ε • ∑ j ∈ Finset.univ.erase i, (μ j / DominantFiveBody.satelliteDistance q i j ^ 3) • (q j - q i) -
    ε • DominantFiveBody.relativeField μ q) := rfl
#print DominantFiveBody.vectorResidual
#print axioms DominantFiveBody.vectorResidual
example : DominantFiveBody.MassVector → DominantFiveBody.Configuration → DominantFiveBody.Plane := @DominantFiveBody.weightedPosition
example : @Eq (DominantFiveBody.MassVector → DominantFiveBody.Configuration → DominantFiveBody.Plane) (@DominantFiveBody.weightedPosition) (fun (m : DominantFiveBody.MassVector) (x : DominantFiveBody.Configuration) => ∑ i : DominantFiveBody.Label, m i • x i) := rfl
#print DominantFiveBody.weightedPosition
#print axioms DominantFiveBody.weightedPosition
