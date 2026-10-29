"""Prepare and replay exact types for the original scalar-potential route."""
from pathlib import Path
import argparse
import json

root = Path(__file__).resolve().parents[1]
names = ['tripleScalarPotential_source_formula', 'tripleScalarChamber_isOpen',
    'tripleScalarChamber_convex', 'tripleScalarPotential_ordered_formula',
    'tripleScalarPotential_nonneg', 'tripleQuadraticPotential_strictJensen',
    'inverse_positive_gap_convex', 'tripleScalarPotential_strictConvexOn',
    'tripleScalarPotential_continuousAt', 'tripleScalarPotential_sublevel_coordinate_bounds',
    'tripleScalarPotential_sublevel_gap_bounds', 'tripleScalarPotential_compact_sublevel',
    'tripleScalarPotential_isProperMap', 'tripleScalarPotential_hasFDerivAt',
    'tripleScalarPotential_fderiv_apply', 'tripleScalarPotential_divided_gradient',
    'tripleScalarPotential_critical_iff_root', 'tripleScalarPotential_exists_minimizer',
    'tripleScalarPotential_critical_isMinOn', 'tripleScalar_potential_root_existsUnique',
    'tripleScalar_potential_root_existsUnique_centered']
fullnames = ['DominantFiveBody.' + name for name in names]
parser = argparse.ArgumentParser()
parser.add_argument('--prepare', action='store_true')
parser.add_argument('--finish', action='store_true')
args = parser.parse_args()
header = ['import DominantFiveBody.TripleScalarPotentialMinimizer',
    'open scoped BigOperators ContDiff Topology', 'universe u_1 u_2 u_3 u_4']
if args.prepare:
    code = header + ['import Lean']
    # Imports must precede all non-import commands.
    code = [header[0], 'import Lean'] + header[1:] + [
        'set_option pp.fullNames true', 'set_option pp.proofs true',
        'set_option pp.deepTerms true', 'set_option pp.coercions.types true',
        'set_option pp.funBinderTypes true', 'open Lean Elab Command in',
        'run_cmd do', '  let names : List Name := [' + ','.join('``'+name for name in fullnames) + ']',
        '  let mut result : Array Json := #[]', '  for name in names do',
        '    let info ← getConstInfo name', '    let pretty ← liftTermElabM do Meta.ppExpr info.type',
        '    result := result.push (Json.mkObj [("lean_declaration",toJson name.toString),("lean_statement",toJson pretty.pretty)])',
        '  liftIO <| IO.FS.writeFile "docs/triple-scalar-potential-types.json" (Json.pretty (toJson result))']
    code += ['#print axioms '+name for name in fullnames]
    (root/'Audit/ExportTripleScalarPotential.lean').write_text('\n'.join(code)+'\n', encoding='utf-8')
if args.finish:
    types = json.loads((root/'docs/triple-scalar-potential-types.json').read_text(encoding='utf-8'))
    byname = {entry['lean_declaration']: entry['lean_statement'] for entry in types}
    if set(byname) != set(fullnames):
        raise SystemExit('Missing or unexpected source declarations in exact type export.')
    if any('⋯' in type_ or '...' in type_ for type_ in byname.values()):
        raise SystemExit('A type contains an ellipsis.')
    code = header + ['set_option linter.unusedVariables false']
    for name in fullnames:
        code += ['example : '+byname[name]+' := @'+name, '#print axioms '+name, '']
    (root/'Audit/TripleScalarPotential.lean').write_text('\n'.join(code)+'\n', encoding='utf-8')
    print(f'{len(types)} complete actual type expressions ready for strict replay.')
