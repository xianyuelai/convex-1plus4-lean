"""Exercise the actual v1 ledger gate with in-memory negative controls only.

The canonical manuscript, ledger and shared verifier files are never rewritten.
These tests establish source/receipt integrity checks, not English-to-Lean
semantic equivalence or whole-paper kernel acceptance.
"""
from pathlib import Path
import copy
import datetime
import hashlib
import json
import runpy
import sys

ROOT = Path(__file__).resolve().parents[1]
OUTPUT = ROOT / 'logs/V1_SOURCE_NEGATIVE_CONTROLS.json'


def sha256(path):
    return hashlib.sha256(path.read_bytes()).hexdigest().upper()


def row(data, key):
    return next(value for value in data['assertions'] if value['id'] == key)


def remove_row(data, key):
    data['assertions'] = [value for value in data['assertions'] if value['id'] != key]


def main():
    if not __debug__:
        raise RuntimeError('Validation tests require Python without optimization.')
    namespace = runpy.run_path(str(ROOT / 'scripts/paper_coverage.py'))
    check = namespace['checked_ledger']
    context = check.__globals__
    real_read = context['read']
    baseline = real_read(context['LEDGER'])
    paths = [ROOT / name for name in (
        'source/convex_1plus4.tex', 'source/convex_1plus4.pdf',
        'source/dominant_five_body_ARMA_rewritten.tex',
        'docs/FULL_ASSERTIONS.json', 'logs/history/pre-v1/FULL_ASSERTIONS.json',
        'docs/V1_SOURCE_CHANGE_REVIEW.json', 'VERSION.json',
        'scripts/migrate_v1_source.py', 'scripts/bind_v1_assertions.py',
        'scripts/paper_coverage.py', 'scripts/v1_source_negative_controls.py')]
    before = {str(path.relative_to(ROOT)): sha256(path) for path in paths}

    def invoke(data):
        def memory_read(path):
            if Path(path).resolve() == context['LEDGER'].resolve():
                return data
            return real_read(path)
        context['read'] = memory_read
        try:
            result = check(allow_open=False, check_types=True)
            return {'accepted': True, 'rows': len(result[1]), 'open_rows': len(result[2])}
        except AssertionError as error:
            return {'accepted': False, 'exception': type(error).__name__, 'reason': str(error)}
        except Exception as error:
            return {'accepted': False, 'unexpected_exception': type(error).__name__, 'reason': str(error)}
        finally:
            context['read'] = real_read

    baseline_result = invoke(copy.deepcopy(baseline))
    tests = []

    def test(name, mutate):
        data = copy.deepcopy(baseline)
        mutate(data)
        result = invoke(data)
        tests.append({'name': name, 'expected': 'rejected', **result,
                      'passed': not result['accepted'] and 'unexpected_exception' not in result})

    key = 'v1:hessian.entries'
    test('missing_complete_flag', lambda d: d.pop('complete_source_inventory'))
    test('false_complete_flag', lambda d: d.update(complete_source_inventory=False))
    test('missing_v1_version', lambda d: d.pop('version'))
    test('unsupported_version', lambda d: d.update(version='legacy'))
    test('scope_version_mismatch', lambda d: d['source_scope'].update(version='legacy'))
    test('wrong_row_source_path', lambda d: row(d, key)['source_location'].update(tex_path='source/other.tex'))
    test('invalid_zero_row_interval', lambda d: row(d, key)['source_location'].update(tex_lines=[0, 0]))
    test('stale_row_interval', lambda d: row(d, key)['source_location'].update(tex_lines=[116, 118]))
    test('stale_row_text', lambda d: row(d, key).update(source_text=row(d, key)['source_text'] + '\nMUTATED'))
    test('stale_row_hash', lambda d: row(d, key).update(source_text_sha256='0' * 64))
    test('exact_claim_not_source', lambda d: row(d, key).update(exact_claim='MUTATED SOURCE CLAIM'))
    test('missing_inventory_unit_while_complete_true', lambda d: d['source_inventory_units'].pop(0))
    test('missing_new_formula_row', lambda d: remove_row(d, key))

    def remove_new_formula_and_inventory(data):
        remove_row(data, key)
        data['source_inventory_units'] = [unit for unit in data['source_inventory_units']
                                          if unit['tex_lines'] != [115, 117]]
    test('missing_new_formula_row_and_inventory_while_complete_true', remove_new_formula_and_inventory)
    test('empty_block_covering_assertions', lambda d: d['source_inventory_units'][0].update(covering_assertions=[]))
    test('unknown_block_covering_assertion', lambda d: d['source_inventory_units'][0].update(covering_assertions=['not:a:row']))
    test('duplicate_row_id', lambda d: d['assertions'].append(copy.deepcopy(row(d, key))))

    def truncated_body(data):
        data['source_scope']['source_body_tex_lines'] = [53, 54]
        lines = (ROOT / data['source_scope']['tex_path']).read_text(encoding='utf-8').splitlines()
        actual = runpy.run_path(str(ROOT / 'scripts/migrate_v1_source.py'))['source_units'](lines, 53, 54)
        keep = set(actual)
        data['source_inventory_units'] = [unit for unit in data['source_inventory_units']
                                          if (unit['kind'], *unit['tex_lines']) in keep]
        remove_row(data, 'v1:hessian.entries')
        remove_row(data, 'v1:hessian.coordinates')
    test('truncated_body_hides_new_formulas', truncated_body)

    def self_selected_exemption(data):
        row(data, key).update(claim_kind='source_subclaim', exact_claim='MUTATED SOURCE CLAIM')
    test('self_selected_subclaim_exemption', self_selected_exemption)
    test('changed_legacy_subclaim_quote', lambda d: row(d, 'kernel.collision_blowup').update(exact_claim='MUTATED SUBCLAIM'))
    test('missing_unreferenced_legacy_subclaim', lambda d: remove_row(d, 'kernel.collision_blowup'))
    test('missing_new_formula_bindings', lambda d: row(d, key).update(lean_bindings=[]))
    test('blank_exact_lean_type', lambda d: row(d, key)['lean_bindings'][0].update(lean_statement=''))
    test('open_new_formula', lambda d: row(d, key).update(status='OPEN', remaining_dependencies=['Negative control']))
    test('dropped_off_diagonal_binding_with_other_binding_retained',
         lambda d: row(d, key).update(lean_bindings=[binding for binding in row(d, key)['lean_bindings']
             if not binding['lean_declaration'].endswith('coorbitalHessianMatrix_offDiagonal')]))
    test('new_near_bound_replaced_by_old_uniform_limits',
         lambda d: row(d, 'prose:487').update(lean_bindings=[binding for binding in row(d, 'prose:487')['lean_bindings']
             if 'near_display' not in binding['lean_declaration']]))
    test('new_field_defect_replaced_by_old_reaction_Ocube',
         lambda d: row(d, 'prose:833').update(lean_bindings=[binding for binding in row(d, 'prose:833')['lean_bindings']
             if 'fieldDefect' not in binding['lean_declaration'] and 'v1FieldDefect' not in binding['lean_declaration']]))
    test('dropped_original_proof_binding',
         lambda d: row(d, 'prose:833')['lean_bindings'].pop(0))
    test('dropped_original_definition_binding',
         lambda d: row(d, 'eq:co-equations')['definition_references'].pop(0))
    test('downgraded_legacy_assertion_status',
         lambda d: row(d, 'kernel.collision_blowup').update(status='CROSS_REFERENCE'))
    test('changed_legacy_assertion_kind',
         lambda d: row(d, 'kernel.collision_blowup').update(claim_kind='prose_assertion'))
    test('dropped_new_physical_hessian_matrix_definition',
         lambda d: row(d, 'v1:hessian.coordinates').update(definition_references=[name
             for name in row(d, 'v1:hessian.coordinates')['definition_references']
             if not name.endswith('.coorbitalHessianMatrix')]))
    test('dropped_new_actual_slice_potential_definition',
         lambda d: row(d, 'v1:hessian.slice').update(definition_references=[name
             for name in row(d, 'v1:hessian.slice')['definition_references']
             if not name.endswith('.coorbitalSlicePotential')]))
    test('dropped_new_corrected_vector_residual_definition',
         lambda d: row(d, 'v1:boundary.off_solution_projection').update(definition_references=[name
             for name in row(d, 'v1:boundary.off_solution_projection')['definition_references']
             if not name.endswith('.v1CorrectedVectorResidual')]))

    def downgrade_and_tamper(data):
        data.pop('version')
        row(data, key).update(source_text='MUTATED SOURCE TEXT')
        data['source_inventory_units'].pop()
    test('version_downgrade_cannot_skip_text_inventory_checks', downgrade_and_tamper)

    after = {str(path.relative_to(ROOT)): sha256(path) for path in paths}
    unchanged = before == after
    success = baseline_result.get('accepted') is True and all(t['passed'] for t in tests) and unchanged
    report = {
        'schema_version': 1,
        'version': 'v1',
        'generated_at_utc': datetime.datetime.now(datetime.timezone.utc).isoformat(),
        'invocation': 'python -B scripts/v1_source_negative_controls.py',
        'method': 'Actual checked_ledger with deep-copied in-memory ledger mutations; all other reads use real current files.',
        'baseline': baseline_result,
        'control_count': len(tests),
        'rejected_as_expected': sum(t['passed'] for t in tests),
        'controls': tests,
        'disk_inputs_unchanged': unchanged,
        'input_sha256': before,
        'negative_controls_passed': success,
        'scope_limit': 'Source/metadata integrity negative controls only. They do not prove natural-language-to-Lean semantic equivalence, definition values, a clean Lean build, axiom audit, fresh kernel replay, PDF rendering, or whole-paper acceptance.'
    }
    OUTPUT.write_text(json.dumps(report, ensure_ascii=False, indent=2) + '\n', encoding='utf-8')
    print(json.dumps({'negative_controls_passed': success, 'baseline': baseline_result,
                      'control_count': len(tests), 'rejected_as_expected': report['rejected_as_expected'],
                      'disk_inputs_unchanged': unchanged, 'report': str(OUTPUT)}, ensure_ascii=False))
    return 0 if success else 1


if __name__ == '__main__':
    sys.exit(main())
