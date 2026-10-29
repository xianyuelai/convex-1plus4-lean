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
import DominantFiveBody.V1BoundaryIdentities
import DominantFiveBody.V1CoorbitalCoordinates
import Lean
noncomputable section
open scoped BigOperators ContDiff Matrix.Norms.Operator Topology
universe u_1 u_2 u_3 u_4 u_5 u_6 u v w
set_option linter.unusedVariables false
set_option linter.auxLemma false
set_option pp.fullNames true
set_option pp.proofs true
set_option pp.deepTerms true
set_option pp.coercions.types true
set_option pp.funBinderTypes true
set_option pp.numericTypes true
open Lean Elab Command in
run_cmd do
  let names : List Name := [``DominantFiveBody.Coorbital.h,``DominantFiveBody.Coorbital.kappa,``DominantFiveBody.Coorbital.kappaPrime,``DominantFiveBody.Coorbital.kernelF,``DominantFiveBody.Coorbital.pairPotential,``DominantFiveBody.Coorbital.positiveRemainder,``DominantFiveBody.Coorbital.slopeCoefficient,``DominantFiveBody.HullOrder,``DominantFiveBody.NormalizedCentralConfiguration,``DominantFiveBody.OrientedSimilar,``DominantFiveBody.PositiveRatio,``DominantFiveBody.acceleration,``DominantFiveBody.angularJacobian,``DominantFiveBody.angularResidual,``DominantFiveBody.augmentedPotential,``DominantFiveBody.branchEqualitySet,``DominantFiveBody.centeredFromRelative,``DominantFiveBody.centeredVariationSpace,``DominantFiveBody.coorbitalDistance,``DominantFiveBody.coorbitalFirstAngleInsertion,``DominantFiveBody.coorbitalHessianCoefficient,``DominantFiveBody.coorbitalHessianMatrix,``DominantFiveBody.coorbitalKernel,``DominantFiveBody.coorbitalMatrix,``DominantFiveBody.coorbitalPotential,``DominantFiveBody.coorbitalResidual,``DominantFiveBody.coorbitalSliceHessianMap,``DominantFiveBody.coorbitalSliceHessianMatrix,``DominantFiveBody.coorbitalSlicePotential,``DominantFiveBody.coorbitalSlicePotentialDerivative,``DominantFiveBody.inertia,``DominantFiveBody.inertiaTangentSpace,``DominantFiveBody.liftRelative,``DominantFiveBody.masses,``DominantFiveBody.orderedPolarSlice,``DominantFiveBody.orderedSliceRoot,``DominantFiveBody.pairDistance,``DominantFiveBody.pairs,``DominantFiveBody.polarPoint,``DominantFiveBody.polarSatellites,``DominantFiveBody.potential,``DominantFiveBody.quarterTurn,``DominantFiveBody.radialResidual,``DominantFiveBody.relativeAction,``DominantFiveBody.relativeAverage,``DominantFiveBody.relativeField,``DominantFiveBody.satellitePairs,``DominantFiveBody.satellitesRelative,``DominantFiveBody.shapeSpace,``DominantFiveBody.sliceAngles,``DominantFiveBody.slicePhysicalConfiguration,``DominantFiveBody.sliceRadii,``DominantFiveBody.tangentialResidual,``DominantFiveBody.v1CorrectedVectorResidual,``DominantFiveBody.v1FieldDefect,``DominantFiveBody.vectorResidual,``DominantFiveBody.weightedPosition]
  let mut result : Array Json := #[]
  for name in names do
    let info ← getConstInfo name
    let ty ← liftTermElabM do Meta.ppExpr info.type
    let mut fields := [("lean_declaration",toJson name.toString),("lean_statement",toJson ty.pretty)]
    match info with
    | .defnInfo defn =>
      let value ← liftTermElabM do Meta.ppExpr defn.value
      fields := fields ++ [("kind",toJson "definition"),("lean_value",toJson value.pretty)]
    | .inductInfo ind =>
      let mut ctors : Array Json := #[]
      for ctor in ind.ctors do
        let ci ← getConstInfo ctor
        let ct ← liftTermElabM do Meta.ppExpr ci.type
        ctors := ctors.push (Json.mkObj [("lean_declaration",toJson ctor.toString),("lean_statement",toJson ct.pretty)])
      fields := fields ++ [("kind",toJson "inductive"),("constructors",toJson ctors)]
    | _ => throwError "A definition reference is neither a definition nor an inductive type: {name}"
    result := result.push (Json.mkObj fields)
  liftIO <| IO.FS.writeFile "logs/source-audit-build/definition-values.json" (Json.pretty (toJson result))
