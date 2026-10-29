"""Fail-closed source coverage and exact Lean acceptance generation.

No status is promoted by this program. Mathematical correspondence is recorded
in the source-reviewed ledger; every claimed binding is elaborated again by Lean.
"""
from pathlib import Path
import argparse
import hashlib
import json
import re
import runpy
import difflib

if not __debug__:
    raise RuntimeError('Whole-paper coverage must run without Python optimization; validation assertions are required.')

ROOT = Path(__file__).resolve().parents[1]
LEDGER = ROOT / 'docs/FULL_ASSERTIONS.json'
DEFS = ROOT / 'docs/DEFINITION_BINDINGS.json'
NAME = re.compile(r'^DominantFiveBody(?:\.[A-Za-z_][A-Za-z_0-9\']*)+$')
SCOPES = ['noncomputable section', 'open scoped BigOperators ContDiff Matrix.Norms.Operator Topology',
          'universe u_1 u_2 u_3 u_4 u_5 u_6 u v w',
          'set_option linter.unusedVariables false',
          # Exact exported instance terms may name auxiliary mathlib proofs.
          # This controls only the naming linter, never kernel/type checking.
          'set_option linter.auxLemma false']
# Ordinary pretty-printing loses the container type of isolated membership
# literals and can juxtapose nested absolute-value bars ambiguously. Preserve
# the kernel expression with explicit applications for these source bindings.
EXPLICIT_TYPES = [
    'DominantFiveBody.normalized_complete_lower_triple_nested_directions',
    'DominantFiveBody.physical_nested_polar_rectangle_derivatives_individually_uniform',
    'DominantFiveBody.pairChartExtendedRows_eq_physical',
    'DominantFiveBody.pair_areas_boundary_complete',
    'DominantFiveBody.nestedStrictConvex_of_positive_areas',
]


def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest().upper()


def read(path):
    return json.loads(path.read_text(encoding='utf-8-sig'))


def write(path, data):
    path.write_text(json.dumps(data, ensure_ascii=False, indent=2) + '\n', encoding='utf-8')


def checked_ledger(allow_open=False, check_types=True):
    data = read(LEDGER)
    assert data.get('complete_source_inventory') is True, 'Incomplete source inventory'
    scope = data['source_scope']
    for kind in ('tex', 'pdf'):
        assert digest(ROOT / scope[kind + '_path']) == scope[kind + '_sha256'].upper(), \
            f'{kind} source bytes differ from the reviewed inventory'
    rows = {a['id']: a for a in data['assertions']}
    assert len(rows) == len(data['assertions']) and rows, 'Empty or duplicate assertion IDs'
    source = (ROOT / scope['tex_path']).read_text(encoding='utf-8')
    # This is a v1 verifier, not a backwards-compatible metadata fallback.
    # The ledger must not select a weaker path by deleting its own version.
    validate_v1_source(data, source)
    for label in re.findall(r'\\begin\{(?:theorem|lemma|proposition|corollary)\}\s*\\label\{([^}]+)\}', source):
        assert label in rows, f'Uninventoried numbered assertion: {label}'
    errors = []
    visited, active = set(), set()

    def visit(key):
        assert key in rows, f'Unknown source reference: {key}'
        assert key not in active, f'Cyclic source references: {key}'
        if key in visited:
            return
        active.add(key)
        a = rows[key]
        state = a['status']
        if state in ('VERIFIED', 'DEFINITIONAL', 'CROSS_REFERENCE', 'BACKGROUND', 'NON_MATHEMATICAL'):
            assert not a.get('remaining_dependencies'), f'Closed assertion retains unresolved dependencies: {key}'
        bindings = a.get('lean_bindings', [])
        defs = a.get('definition_references', [])
        if state == 'VERIFIED':
            assert bindings, f'No exact theorem binding: {key}'
            assert not a.get('remaining_dependencies'), f'Unresolved dependencies: {key}'
        elif state == 'DEFINITIONAL':
            assert defs, f'No actual definition references: {key}'
            assert not a.get('remaining_dependencies'), f'Unresolved definition: {key}'
        elif state == 'CROSS_REFERENCE':
            assert a.get('source_assertion_references'), f'Empty source reference: {key}'
            assert a.get('proof_route_note') or a.get('proof_route') or a.get('source_derivation_status'), \
                f'Unexplained source reference: {key}'
        elif state in ('BACKGROUND', 'NON_MATHEMATICAL'):
            assert a.get('proof_route_note') or a.get('source_derivation_status'), \
                f'No source-review reason for excluded paragraph: {key}'
            assert a['claim_kind'] == 'prose_assertion', f'Excluded formal claim: {key}'
        elif state in ('OPEN', 'PARTIAL', 'CONDITIONAL'):
            errors.append(f'{key}: {state}: ' + '; '.join(a.get('remaining_dependencies', [])))
        else:
            raise AssertionError(f'Unknown assertion status: {key}: {state}')
        for b in bindings:
            assert NAME.fullmatch(b['lean_declaration']), f'Invalid Lean name: {key}: {b}'
            if check_types:
                assert b.get('lean_statement') and '⋯' not in b['lean_statement'] and \
                    not b['lean_statement'].lstrip().startswith(b['lean_declaration']), \
                    f'Incomplete explicit theorem type: {key}'
        for name in defs:
            assert NAME.fullmatch(name), f'Invalid definition name: {key}: {name}'
        for ref in a.get('source_assertion_references', []):
            visit(ref)
        active.remove(key)
        visited.add(key)

    for key in rows:
        visit(key)
    if errors and not allow_open:
        raise AssertionError('Unclosed paper assertions:\n' + '\n'.join(errors))
    return data, rows, errors


def validate_v1_source(data, source):
    """Check actual v1 text/ranges and independently re-enumerate all blocks.

    This rejects stale locations and omitted blocks.  It checks byte/text
    correspondence, not the truth of an English-to-Lean semantic judgement.
    """
    scope=data['source_scope']
    version=read(ROOT/'VERSION.json')
    assert version['version']==data.get('version')==scope.get('version')=='v1', 'Version identity differs'
    identity={k:scope[k] for k in ('tex_path','pdf_path','tex_sha256','pdf_sha256','pdf_page_count')}
    assert identity==version['source_identity'], 'Version/source identity differs'
    review=read(ROOT/data['migration_review'])
    baseline_path=ROOT/'logs/history/pre-v1/FULL_ASSERTIONS.json'
    assert digest(baseline_path)==review['baseline_ledger_sha256'], 'Historical inventory identity differs'
    baseline={r['id']:r for r in read(baseline_path)['assertions']}
    lines=source.splitlines()
    rows={r['id']:r for r in data['assertions']}
    new_kinds={
        'v1:hessian.coordinates':'displayed_assertion',
        'v1:hessian.entries':'displayed_assertion',
        'v1:hessian.quadratic':'displayed_assertion',
        'v1:hessian.slice':'prose_assertion',
        'v1:hessian.quadratic_connector':'prose_assertion',
        'v1:boundary.off_solution_projection':'displayed_assertion',
    }
    assert not review.get('retired_assertions'), 'v1 has no reviewed retired mathematical obligations'
    assert set(rows)==set(baseline)|set(new_kinds), 'A reviewed legacy or new v1 assertion was dropped or invented'
    for key,original in baseline.items():
        row=rows[key]
        assert row['claim_kind']==original['claim_kind'], f'Changed reviewed assertion kind: {key}'
        expected_status='VERIFIED' if key=='eq:co-equations' else original['status']
        assert row['status']==expected_status, f'Changed or downgraded reviewed assertion status: {key}'
        old_names={b['lean_declaration'] for b in original.get('lean_bindings',[])}
        current_names={b['lean_declaration'] for b in row.get('lean_bindings',[])}
        assert old_names<=current_names, f'Dropped original proof obligation binding: {key}'
        assert set(original.get('definition_references',[]))<=set(row.get('definition_references',[])), f'Dropped original defining object: {key}'
    for key,kind in new_kinds.items():
        assert rows[key]['claim_kind']==kind, f'Changed reviewed v1 assertion kind: {key}'
        expected_status='CROSS_REFERENCE' if key.endswith('connector') else 'VERIFIED'
        assert rows[key]['status']==expected_status, f'Changed reviewed v1 assertion status: {key}'
    reviewed=runpy.run_path(str(ROOT/'scripts/bind_v1_assertions.py'))['REVIEWED_V1_REQUIREMENTS']
    for key,requirements in reviewed.items():
        names={b['lean_declaration'] for b in rows[key].get('lean_bindings',[])}
        definitions=set(rows[key].get('definition_references',[]))
        assert set(requirements['theorems'])<=names, f'Missing reviewed v1 formula binding: {key}'
        assert set(requirements['definitions'])<=definitions, f'Missing reviewed v1 defining object: {key}'
    for key,row in rows.items():
        location=row['source_location']
        assert location['tex_path']==scope['tex_path'], f'Wrong source path: {key}'
        a,b=location['tex_lines']
        assert isinstance(a,int) and isinstance(b,int) and 1<=a<=b<=len(lines), f'Bad source interval: {key}'
        raw='\n'.join(lines[a-1:b])
        assert row.get('source_text')==raw, f'Stale source text/range: {key}'
        assert hashlib.sha256(raw.encode()).hexdigest().upper()==row.get('source_text_sha256'), f'Stale row source hash: {key}'
        if row['claim_kind']=='source_subclaim':
            assert key in baseline and baseline[key]['claim_kind']=='source_subclaim', f'Unreviewed source-subclaim exemption: {key}'
            assert row['exact_claim']==baseline[key]['exact_claim'], f'Changed legacy mathematical subclaim: {key}'
        else:
            assert row['exact_claim']==raw, f'Claim quote differs from current source: {key}'
    start,end=scope['source_body_tex_lines']
    assert 1<=start<=end<=len(lines), 'Bad source body interval'
    expected_start=next(i+2 for i,s in enumerate(lines) if s==r'\begin{abstract}')
    expected_end=next(i for i,s in enumerate(lines) if r'\begin{thebibliography}' in s)
    assert [start,end]==[expected_start,expected_end], 'Source body scope was truncated or moved'
    helpers=runpy.run_path(str(ROOT/'scripts/migrate_v1_source.py'))
    actual=helpers['source_units'](lines,start,end)
    inventory=data.get('source_inventory_units',[])
    assert [(x['kind'],*x['tex_lines']) for x in inventory]==actual, 'Incomplete or stale display/prose/statement inventory'
    for unit in inventory:
        a,b=unit['tex_lines']
        raw='\n'.join(lines[a-1:b])
        assert unit['source_text_sha256']==hashlib.sha256(raw.encode()).hexdigest().upper(), 'Changed inventory unit'
        covering=unit['covering_assertions']
        assert covering and all(k in rows for k in covering), 'Unknown or empty block binding'
        for n in range(a,b+1):
            if not lines[n-1].strip():
                continue
            assert any(rows[k]['source_location']['tex_lines'][0]<=n<=rows[k]['source_location']['tex_lines'][1]
                       for k in covering), f'Uncovered source line {n}'
    assert review['new_tex_sha256']==scope['tex_sha256'], 'Diff review is stale'
    old=(ROOT/'source/dominant_five_body_ARMA_rewritten.tex').read_text(encoding='utf-8-sig')
    assert digest(ROOT/'source/dominant_five_body_ARMA_rewritten.tex')==review['old_tex_sha256'], 'Diff baseline bytes differ'
    actual_changes=[]
    for op,a,b,c,d in difflib.SequenceMatcher(None,old.splitlines(),lines,autojunk=False).get_opcodes():
        if op!='equal':
            actual_changes.append(dict(number=len(actual_changes)+1,operation=op,old_lines=[a+1,b],new_lines=[c+1,d],
                old_text='\n'.join(old.splitlines()[a:b]),new_text='\n'.join(lines[c:d])))
    change_fields=('number','operation','old_lines','new_lines','old_text','new_text')
    assert [{k:x[k] for k in change_fields} for x in review['changes']]==actual_changes, 'Incomplete or stale source-diff review'
    assert all(x.get('review_status')=='SOURCE_REVIEWED' for x in review['changes']), 'Unreviewed manuscript change'
    pattern=re.compile(r'\\begin\{(theorem|lemma|proposition|corollary)\}(.*?)\\end\{\1\}',re.S)
    statements=lambda text:[(m.group(1),re.sub(r'\s+',' ',m.group(2)).strip()) for m in pattern.finditer(text)]
    assert statements(old)==statements(source), 'A v1 formal result statement changed from the reviewed baseline'
    assert len(statements(source))==14, 'Unexpected numbered theorem inventory'


def export_types(data, rows):
    names = {b['lean_declaration'] for a in rows.values() for b in a.get('lean_bindings', [])}
    # Later source patches intentionally replace earlier bindings of the same
    # assertion. Refresh those retained historical patch types as well, because
    # finish_types writes every patch before the deterministic merge.
    for filename in data['coverage_patches']:
        patch = read(ROOT / 'docs' / filename)
        names.update(b['lean_declaration'] for a in patch['assertions'] for b in a.get('lean_bindings', []))
    names = sorted(names)
    tails = {n.rsplit('.', 1)[1] for n in names}
    modules = set()
    for path in (ROOT / 'DominantFiveBody').glob('*.lean'):
        declared = set(re.findall(r'^\s*(?:@\[[^\]]+\]\s*)?(?:theorem|lemma)\s+([\w\']+)',
                                  path.read_text(encoding='utf-8-sig'), re.M))
        if tails & declared:
            modules.add('DominantFiveBody.' + path.stem)
    lines = ['import ' + m for m in sorted(modules)] + ['import Lean'] + SCOPES + [
        'set_option pp.fullNames true', 'set_option pp.proofs true', 'set_option pp.deepTerms true',
        'set_option pp.coercions.types true', 'set_option pp.funBinderTypes true',
        'set_option pp.numericTypes true',
        'open Lean Elab Command in', 'run_cmd do',
        '  let names : List Name := [' + ','.join('``' + n for n in names) + ']',
        '  let explicitNames : List Name := [' + ','.join('``' + n for n in EXPLICIT_TYPES) + ']',
        '  let mut result : Array Json := #[]',
        '  for name in names do', '    let info ← getConstInfo name',
        '    let ty ← liftTermElabM do',
        '      if explicitNames.contains name then',
        '        withOptions (fun o => (o.setBool `pp.explicit true).setBool `pp.notation false) (Meta.ppExpr info.type)',
        '      else Meta.ppExpr info.type',
        '    result := result.push (Json.mkObj [("lean_declaration",toJson name.toString),("lean_statement",toJson ty.pretty)])',
        '  liftIO <| IO.FS.writeFile "logs/source-audit-build/coverage-types.json" (Json.pretty (toJson result))']
    (ROOT / 'logs/source-audit-build/ExportCoverageTypes.lean').write_text('\n'.join(lines) + '\n', encoding='utf-8')
    print(f'Prepared exact type export for {len(names)} distinct declarations in {len(modules)} modules')


def finish_types(data, rows):
    types = {b['lean_declaration']: b['lean_statement'] for b in
             read(ROOT / 'logs/source-audit-build/coverage-types.json')}
    expected = {b['lean_declaration'] for a in rows.values() for b in a.get('lean_bindings', [])}
    assert expected <= set(types), 'New bindings appeared; export types again before finishing'
    pending = []
    for file in data['coverage_patches']:
        path = ROOT / 'docs' / file
        patch = read(path)
        for row in patch['assertions']:
            for binding in row.get('lean_bindings', []):
                name = binding['lean_declaration']
                assert name in types, f'Patch changed during type export: {file}: {name}'
                binding['lean_statement'] = types[name]
        patch['exact_type_export'] = 'Lean ConstantInfo.type, full names and proofs; re-elaboration required by final acceptance'
        pending.append((path, patch))
    for path, patch in pending:
        write(path, patch)
    print('Updated patch binding types; run integrate_coverage.py before generating acceptance')


def export_definitions(data, rows):
    names = sorted({n for a in rows.values() for n in a.get('definition_references', [])})
    modules = set()
    tails = {n.rsplit('.', 1)[1] for n in names}
    for path in (ROOT / 'DominantFiveBody').glob('*.lean'):
        declared = set(re.findall(r'^\s*(?:noncomputable\s+)?(?:def|abbrev|structure|inductive)\s+(\w+)',
                                  path.read_text(encoding='utf-8-sig'), re.M))
        if tails & declared:
            modules.add('DominantFiveBody.' + path.stem)
    lines = ['import ' + m for m in sorted(modules)] + ['import Lean'] + SCOPES + [
        'set_option pp.fullNames true', 'set_option pp.proofs true',
        'set_option pp.deepTerms true', 'set_option pp.coercions.types true',
        'set_option pp.funBinderTypes true', 'set_option pp.numericTypes true',
        'open Lean Elab Command in', 'run_cmd do',
        '  let names : List Name := [' + ','.join('``' + n for n in names) + ']',
        '  let mut result : Array Json := #[]',
        '  for name in names do',
        '    let info ← getConstInfo name',
        '    let ty ← liftTermElabM do Meta.ppExpr info.type',
        '    let mut fields := [("lean_declaration",toJson name.toString),("lean_statement",toJson ty.pretty)]',
        '    match info with',
        '    | .defnInfo defn =>',
        '      let value ← liftTermElabM do Meta.ppExpr defn.value',
        '      fields := fields ++ [("kind",toJson "definition"),("lean_value",toJson value.pretty)]',
        '    | .inductInfo ind =>',
        '      let mut ctors : Array Json := #[]',
        '      for ctor in ind.ctors do',
        '        let ci ← getConstInfo ctor',
        '        let ct ← liftTermElabM do Meta.ppExpr ci.type',
        '        ctors := ctors.push (Json.mkObj [("lean_declaration",toJson ctor.toString),("lean_statement",toJson ct.pretty)])',
        '      fields := fields ++ [("kind",toJson "inductive"),("constructors",toJson ctors)]',
        '    | _ => throwError "A definition reference is neither a definition nor an inductive type: {name}"',
        '    result := result.push (Json.mkObj fields)',
        '  liftIO <| IO.FS.writeFile "logs/source-audit-build/definition-values.json" (Json.pretty (toJson result))']
    path = ROOT / 'logs/source-audit-build/ExportDefinitionValues.lean'
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text('\n'.join(lines) + '\n', encoding='utf-8')
    print(f'Prepared actual type/value export for {len(names)} definitions')


def finish_definitions(data, rows):
    bindings = read(ROOT / 'logs/source-audit-build/definition-values.json')
    expected = {n for a in rows.values() for n in a.get('definition_references', [])}
    assert {x['lean_declaration'] for x in bindings} == expected, 'Definition export is incomplete or stale'
    write(DEFS, dict(source_tex_sha256=data['source_scope']['tex_sha256'], definitions=bindings))


def generate(data, rows, errors):
    defs = read(DEFS)
    assert defs['source_tex_sha256'] == data['source_scope']['tex_sha256'], 'Definition source binding differs'
    definitions = {d['lean_declaration']: d for d in defs['definitions']}
    expected = {n for a in rows.values() for n in a.get('definition_references', [])}
    assert set(definitions) == expected, 'Definition inventory differs from source ledger'
    lines = ['import DominantFiveBody'] + SCOPES + ['']
    pairs = set()
    names = set()
    for a in rows.values():
        for b in a.get('lean_bindings', []):
            pair = b['lean_declaration'], b['lean_statement']
            if pair in pairs:
                continue
            pairs.add(pair)
            name, statement = pair
            lines += ['-- Source binding: ' + a['id'], 'example : ' + statement + ' := @' + name, '']
            names.add(name)
    for name in sorted(expected):
        d = definitions[name]
        lines += ['-- Exact definition type and body: ' + name,
                  'example : ' + d['lean_statement'] + ' := @' + name]
        if d['kind'] == 'definition':
            assert d.get('lean_value') and '⋯' not in d['lean_value'], f'Incomplete definition body: {name}'
            lines += ['example : @Eq (' + d['lean_statement'] + ') (@' + name + ') (' + d['lean_value'] + ') := rfl']
        elif d['kind'] == 'inductive':
            assert d.get('constructors'), f'Missing inductive constructor types: {name}'
            for c in d['constructors']:
                lines += ['example : ' + c['lean_statement'] + ' := @' + c['lean_declaration']]
        else:
            raise AssertionError('Unknown definition binding kind: ' + name)
        lines += ['#print ' + name, '']
        names.add(name)
    lines += ['#print axioms ' + n for n in sorted(names)]
    (ROOT / 'PaperAcceptance/Coverage.lean').write_text('\n'.join(lines) + '\n', encoding='utf-8')
    write(ROOT / 'logs/PAPER_COVERAGE_EXPECTED.json', dict(
        ledger_sha256=digest(LEDGER), definition_bindings_sha256=digest(DEFS),
        coverage_lean_sha256=digest(ROOT / 'PaperAcceptance/Coverage.lean'),
        assertions=len(rows), exact_type_bindings=len(pairs), definitions=len(expected),
        axiom_names=sorted(names), unclosed_assertions=errors,
        whole_paper_closed=not errors))
    print(f'{len(rows)} assertions, {len(pairs)} exact types, {len(expected)} definitions; open={len(errors)}')


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('--allow-open', action='store_true', help='Development only; never used by verify_paper')
    parser.add_argument('--export-definitions', action='store_true')
    parser.add_argument('--finish-definitions', action='store_true')
    parser.add_argument('--generate', action='store_true')
    parser.add_argument('--export-types', action='store_true')
    parser.add_argument('--finish-types', action='store_true')
    args = parser.parse_args()
    data, rows, errors = checked_ledger(args.allow_open, not (
        args.export_types or args.finish_types or args.export_definitions or args.finish_definitions))
    if args.export_types:
        export_types(data, rows)
    if args.finish_types:
        finish_types(data, rows)
    if args.export_definitions:
        export_definitions(data, rows)
    if args.finish_definitions:
        finish_definitions(data, rows)
    if args.generate:
        generate(data, rows, errors)
    if not any((args.export_definitions, args.finish_definitions, args.generate, args.export_types, args.finish_types)):
        print(f'Coverage metadata checked: {len(rows)} entries, {len(errors)} open obligations')


if __name__ == '__main__':
    main()
