"""Prepare and replay exact types for the regular and nested slow-root source formulas."""
from pathlib import Path
import argparse
import json

root = Path(__file__).resolve().parents[1]
names = ['nestedBoundaryKernel_unit_hasDerivAt', 'nestedBoundaryKernel_unit_second_hasDerivAt', 'nestedBoundaryKernel_original_derivatives', 'nestedChartExtendedRows_boundary_alpha_independent', 'nestedChartJacobian_boundary_alpha_independent', 'nestedSourceCasePermutation_source', 'nestedSourceCaseTable_source', 'nestedSourceCase_order_is_original', 'nestedSource_individual_inverse_limits', 'nestedSource_common_balls_without_alpha_limit', 'nestedSource_radial_Oepsilon_from_original_bound', 'affinePolarPoint_divided_identity', 'affinePolarPoint_cartesian_Osquare', 'tripleChartPoint_cartesian_Osquare', 'tripleChart_exteriorMass_Ocube', 'tripleChart_relativeAverage_cubic_identity', 'tripleChart_relativeAverage_Ocube', 'tripleChart_reaction_Ocube', 'nestedBoundaryDisplacement_to_triple', 'nestedChartPoint_cartesian_Osquare', 'nestedChart_reaction_Ocube', 'newtonTargetField_affinePolar_Osquare', 'backgroundProbeField_affinePolar_Osquare', 'tripleInternalCartesian_scaling', 'tripleInternalVectorQuotient_zero', 'tripleInternalVectorQuotient_contDiffAt', 'tripleInternalVectorQuotient_Olinear', 'tripleInternalCartesian_Osquare']
fullnames = ['DominantFiveBody.' + name for name in names]
parser = argparse.ArgumentParser()
parser.add_argument('--prepare', action='store_true')
parser.add_argument('--finish', action='store_true')
args = parser.parse_args()
header = ['import DominantFiveBody.NestedSourceDerivativeDetails', 'import DominantFiveBody.NestedSourceSignTable', 'import DominantFiveBody.NestedSourceCaptureDetails', 'import DominantFiveBody.SlowInternalTaylor', 'open scoped BigOperators ContDiff Topology', 'universe u_1 u_2 u_3 u_4']
if args.prepare:
    code = header + ['import Lean']
    # Imports must precede all non-import commands.
    code = header[:4] + ['import Lean'] + header[4:] + [
        'set_option pp.fullNames true', 'set_option pp.proofs true',
        'set_option pp.deepTerms true', 'set_option pp.coercions.types true',
        'set_option pp.funBinderTypes true', 'set_option pp.numericTypes true', 'open Lean Elab Command in',
        'run_cmd do', '  let names : List Name := [' + ','.join('``'+name for name in fullnames) + ']',
        '  let mut result : Array Json := #[]', '  for name in names do',
        '    let info ← getConstInfo name', '    let pretty ← liftTermElabM do Meta.ppExpr info.type',
        '    result := result.push (Json.mkObj [("lean_declaration",toJson name.toString),("lean_statement",toJson pretty.pretty)])',
        '  liftIO <| IO.FS.writeFile "docs/nested-source-details-types.json" (Json.pretty (toJson result))']
    code += ['#print axioms '+name for name in fullnames]
    (root/'Audit/ExportNestedSourceDetails.lean').write_text('\n'.join(code)+'\n', encoding='utf-8')
if args.finish:
    types = json.loads((root/'docs/nested-source-details-types.json').read_text(encoding='utf-8'))
    byname = {entry['lean_declaration']: entry['lean_statement'] for entry in types}
    if set(byname) != set(fullnames):
        raise SystemExit('Missing or unexpected source declarations in exact type export.')
    if any('⋯' in type_ or '...' in type_ for type_ in byname.values()):
        raise SystemExit('A type contains an ellipsis.')
    code = header + ['set_option linter.unusedVariables false']
    for name in fullnames:
        code += ['example : '+byname[name]+' := @'+name, '#print axioms '+name, '']
    (root/'Audit/NestedSourceDetails.lean').write_text('\n'.join(code)+'\n', encoding='utf-8')
    print(f'{len(types)} complete actual type expressions ready for strict replay.')
