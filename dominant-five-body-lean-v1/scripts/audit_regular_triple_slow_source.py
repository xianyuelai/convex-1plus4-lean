"""Prepare and replay exact types for the regular and nested slow-root source formulas."""
from pathlib import Path
import argparse
import json

root = Path(__file__).resolve().parents[1]
names = ['polar_distance_sq_cos', 'sqrt_cube_inverse_eq_negative_three_halves', 'regularTripleScalarH_source_formula', 'regularTripleScalarH_differentiableAt', 'regularTripleScalarH_fderiv_apply', 'regularTripleBoundaryM_source_formula', 'tripleAngularDifference_boundary_eq_LM', 'tripleAngularMean_boundary_source_H', 'tripleSlowPoint_source_formula', 'nestedSlowPoint_source_formula', 'nestedBoundaryScalarPositions_source_formula', 'nestedBoundaryScalarPositions_weighted_center', 'nestedSlowRootCandidate_contDiffAt', 'nestedSlowRootCandidate_contDiffOn', 'tripleChart_zero_face_eq_slowPoint_of_local_uniqueness', 'nestedChart_zero_face_eq_slowPoint_of_local_uniqueness']
fullnames = ['DominantFiveBody.' + name for name in names]
parser = argparse.ArgumentParser()
parser.add_argument('--prepare', action='store_true')
parser.add_argument('--finish', action='store_true')
args = parser.parse_args()
header = ['import DominantFiveBody.RegularTripleSourceFormulas',
    'import DominantFiveBody.SlowRootSourceIdentities',
    'open scoped BigOperators ContDiff Topology', 'universe u_1 u_2 u_3 u_4']
if args.prepare:
    code = header + ['import Lean']
    # Imports must precede all non-import commands.
    code = [header[0], header[1], 'import Lean'] + header[2:] + [
        'set_option pp.fullNames true', 'set_option pp.proofs true',
        'set_option pp.deepTerms true', 'set_option pp.coercions.types true',
        'set_option pp.funBinderTypes true', 'set_option pp.numericTypes true', 'open Lean Elab Command in',
        'run_cmd do', '  let names : List Name := [' + ','.join('``'+name for name in fullnames) + ']',
        '  let mut result : Array Json := #[]', '  for name in names do',
        '    let info ← getConstInfo name', '    let pretty ← liftTermElabM do Meta.ppExpr info.type',
        '    result := result.push (Json.mkObj [("lean_declaration",toJson name.toString),("lean_statement",toJson pretty.pretty)])',
        '  liftIO <| IO.FS.writeFile "docs/regular-triple-slow-source-types.json" (Json.pretty (toJson result))']
    code += ['#print axioms '+name for name in fullnames]
    (root/'Audit/ExportRegularTripleSlowSource.lean').write_text('\n'.join(code)+'\n', encoding='utf-8')
if args.finish:
    types = json.loads((root/'docs/regular-triple-slow-source-types.json').read_text(encoding='utf-8'))
    byname = {entry['lean_declaration']: entry['lean_statement'] for entry in types}
    if set(byname) != set(fullnames):
        raise SystemExit('Missing or unexpected source declarations in exact type export.')
    if any('⋯' in type_ or '...' in type_ for type_ in byname.values()):
        raise SystemExit('A type contains an ellipsis.')
    code = header + ['set_option linter.unusedVariables false']
    for name in fullnames:
        code += ['example : '+byname[name]+' := @'+name, '#print axioms '+name, '']
    (root/'Audit/RegularTripleSlowSource.lean').write_text('\n'.join(code)+'\n', encoding='utf-8')
    print(f'{len(types)} complete actual type expressions ready for strict replay.')
