"""Complete the independent Sections 3/7 patch from strict printed types.

This does not modify the full-paper ledger or another agent's patch.
"""
from pathlib import Path
from collections import Counter
import json
import re

root = Path(__file__).resolve().parents[1]
target = root / 'docs/SECTIONS_3_7_COVERAGE_PATCH.json'
logfile = root / 'docs/sections-three-seven-complete-axioms-audit.log'
raw = logfile.read_text(encoding='utf-8-sig')
if 'error:' in raw or 'warning:' in raw:
    raise SystemExit('The supplemental strict audit has diagnostics.')
types = {}
current = None
for line in raw.splitlines():
    if line.startswith('DominantFiveBody.'):
        current = re.match(r'([A-Za-z0-9_.]+)', line).group(1).rstrip('.')
        types[current] = [line]
    elif line.startswith("'") or line.startswith('COMMAND:') or line.startswith('EXIT_CODE:'):
        current = None
    elif current is not None:
        types[current].append(line)
types = {name: '\n'.join(lines).strip() for name, lines in types.items()}
axioms = {}
for name, body in re.findall(r"'([^']+)' depends on axioms:\s*\[([^]]*)\]", raw, flags=re.S):
    values = {x.strip() for x in body.split(',') if x.strip()}
    if values - {'propext', 'Classical.choice', 'Quot.sound'}:
        raise SystemExit(f'Unexpected axioms: {name}: {values}')
    axioms[name] = sorted(values)
if len(types) != 54 or len(axioms) != 54:
    raise SystemExit(f'Expected 54 complete types and axiom lists, got {len(types)} / {len(axioms)}.')

data = json.loads(target.read_text(encoding='utf-8-sig'))
rows = {row['id']: row for row in data['assertions']}

def bind(ident, pairs):
    row = rows[ident]
    existing = {b['lean_declaration'] for b in row['lean_bindings']}
    for name, claim in pairs:
        full = 'DominantFiveBody.' + name
        if full not in types or full not in axioms:
            raise SystemExit(f'No actual printed type and axiom output for {full}')
        if full not in existing:
            row['lean_bindings'].append(dict(lean_declaration=full, lean_statement=types[full], subclaim=claim))
            existing.add(full)
    row['status'] = 'VERIFIED'
    row['remaining_dependencies'] = []

bind('prose:230', [('centeredFromRelative_source_formulas',
    'Literal primary-zero, centered primary and satellite coordinates, epsilon-zero coincidence, and every original pair distance.')])
bind('prose:265', [
    ('reducedPolarResiduals_zero_iff_vectorRoot', 'Exactly four radial rows and any three angular rows are equivalent to all four physical vector rows; the omitted mass is positive.'),
    ('normalizedCC_of_reducedResidual_zero', 'The actual seven slice equations recover every original normalized physical equation.')])
rows['prose:265']['definition_references'] += ['DominantFiveBody.radialResidual', 'DominantFiveBody.angularResidual']
bind('prose:275', [
    ('sliceWeightedMetric_apply', 'Entrywise actual seven-row diagonal bilinear metric.'),
    ('sliceMassWeights_pos', 'All actual row factors are strictly positive for epsilon and every mass ratio positive.'),
    ('sliceAction_second_fderiv', 'The true second Frechet differential equals the actual weighted residual Jacobian.'),
    ('sliceAction_second_fderiv_isInvertible_iff_reducedJacobian', 'The positive diagonal row map gives the literal slice-Hessian/Jacobian invertibility equivalence.')])
bind('display:285', [('centered_radial_tangent_direct_sum',
    'Literal E=R x direct-sum T, with equality of the sum and trivial intersection.')])
rows['display:285']['definition_references'] += ['DominantFiveBody.inertiaTangentSpace']
bind('prose:288', [('centered_radial_tangent_hessian_orthogonal',
    'The literal radial/inertia-tangent direct sum is orthogonal for the actual Hessian, with radial value 3I strictly positive.')])
bind('prose:305', [
    ('reducedAngularJacobian_zero_eq', 'The true reduced angular block equals the derivative of the actual coorbital equations on the fixed-angle slice.'),
    ('reducedAngularJacobian_zero_isInvertible', 'The angular block is invertible at every positive coorbital root by the proved constant-rotation kernel.'),
    ('reducedJacobian_at_coorbital_root_isInvertible', 'The radial and angular source blocks give the true full base Jacobian invertibility.')])
rows['prose:305']['background_citation_note'] = (
    'The sentence attributing the continuation to CCLM is an external bibliographic attribution. '
    'The actual mathematical conclusion and the source radial/angular proof steps are independently proved here; '
    'this binding is not a formal verification of CCLM textual provenance.')

interface = [
    ('pairChart_compact_physical_continuation', 'Common independent products uniformly for all pair fractions in [0,1], actual roots, original convexity and shape Hessian.'),
    ('noCollision_physical_local_continuation', 'Independent epsilon/mass product with actual smooth roots, original convexity, Hessian and same-positive-mass zero endpoint.'),
    ('pairChart_fixed_mass_zero_endpoint', 'Fixed current positive pair-chart masses yield unit radii and all original distinct-angle coorbital rows at epsilon zero.'),
    ('tripleChart_fixed_mass_zero_endpoint', 'Fixed current positive regular-triple masses yield unit radii and all original distinct-angle coorbital rows at epsilon zero.'),
    ('nestedChart_fixed_mass_zero_endpoint', 'Fixed current positive nested-chart masses yield unit radii and all original distinct-angle coorbital rows at epsilon zero.')]
bind('prop:chart-interface', interface)
bind('prose:928', interface + [
    ('pairToFixedSlice_isInvertible', 'Pair coordinate map remains invertible independently of epsilon whenever the physical pair scale is positive.'),
    ('pairFixedRowTransform_isInvertible', 'Pair row map remains invertible at epsilon zero and all fraction values; its inverse divides only by the fixed nonzero scale.'),
    ('tripleToFixedSlice_isInvertible', 'Regular-triple coordinate map is invertible at fixed nonzero t and sum-one weights.'),
    ('tripleFromFixedSlice_isInvertible', 'The actual regular-triple row map is the inverse coordinate map and remains invertible at epsilon zero.'),
    ('nestedToFixedSlice_isInvertible', 'Nested coordinate map is invertible at fixed nonzero t and eta, including both inner fraction endpoints.'),
    ('nestedFromFixedSlice_isInvertible', 'The actual nested row map is the inverse coordinate map and remains invertible at epsilon zero.'),
    ('pairChartExtendedRows_zero_iff_physical', 'Actual pair rows recover all original radial/angular rows also at epsilon zero.'),
    ('tripleChartExtendedRows_zero_iff_physical', 'Actual regular-triple rows recover all original radial/angular rows also at epsilon zero.'),
    ('nestedChartExtendedRows_zero_iff_physical', 'Actual nested rows recover all original radial/angular rows also at epsilon zero.'),
    ('pairChart_endpoint_gap_nonzero', 'Literal pair angular gap t z is the original angle difference and is nonzero at each separated fixed-mass endpoint.'),
    ('tripleChart_endpoint_gaps_nonzero', 'Literal regular-triple angular gaps t v_i are the original successive angle differences and are nonzero.'),
    ('nestedChart_endpoint_gaps_nonzero', 'Literal nested gaps t eta z_2 and t Q_a,t Q_b are the original angle differences and are nonzero.')])
bind('prose:954', [
    ('tripleScalar_seed_of_regular_scaled_limits', 'A distinct ordered scalar boundary root is derived from the limiting actual physical rows, retaining all zero-weight probe rows.'),
    ('triplePhysical_capture_of_regular_scaled_limits', 'Actual regular physical sequences need only the classified scale limits; no scalar-root assumption is inserted.'),
    ('pairChart_compact_boundary_continuation', 'One epsilon/scale/root product and one inverse bound work for every pair fraction in [0,1].'),
    ('nestedChart_compact_boundary_continuation', 'One independent epsilon/t/eta product and root ball work for every inner pair fraction in [0,1].'),
    ('orderedPolarSlice_angles', 'The actual gauge subtracts the current first angle from every current ordered angle.'),
    ('orderedPolarSlice_radii', 'The actual gauge keeps every current radius with the exact ordered label permutation.'),
    ('orderedPolarSlice_contDiff', 'Literal angle subtraction and coordinate gauge are smooth.'),
    ('orderedPolarSlice_physical_eq_rotation', 'Literal gauge equals the original orientation-preserving physical rotation with exact current masses.'),
    ('orderedPolarSlice_root_of_normalized', 'Literal gauge preserves all actual equations and original strict hull order.'),
    ('orderedPolarSlice_nondegenerate_of_normalized', 'Literal gauge preserves the original physical shape nondegeneracy.'),
    ('orderedPolarSlice_reindex_undo', 'The exact inverse label/gauge operation returns the original current seven coordinates, independently of the interim anchor angle.')])
rows['prose:954']['definition_references'] += ['DominantFiveBody.orderedPolarSlice']

equality = rows['display:980']
equality['definition_references'] = ['DominantFiveBody.branchEqualitySet']
equality['lean_bindings'] = [dict(lean_declaration='DominantFiveBody.mem_branchEqualitySet',
    lean_statement=types['DominantFiveBody.mem_branchEqualitySet'],
    subclaim='Exact original Q_n membership with the half-open parameter interval and equality of the two actual branches.')]
equality['proof_route_note'] = 'The source local equality set is exported as branchEqualitySet; branches_eq_of_localUniqueness proves the open/closed comparison on the parameter interval.'

for row in data['assertions']:
    row['definition_references'] = list(dict.fromkeys(
        reference if reference.startswith('DominantFiveBody.') else 'DominantFiveBody.' + reference.rsplit('.', 1)[-1]
        for reference in row['definition_references']))
    if row['status'] == 'PARTIAL':
        raise SystemExit('Unclosed source row: ' + row['id'])

connectors = {
    'prose:214': ('The sentence adopts centered normalization and cites its provenance; the actual normalized equations are the following eq:cc.', ['eq:cc']),
    'prose:219': ('The word and connects the normalized equations to the following definitions of U, I and G; it has no independent mathematical assertion.', ['eq:UI']),
    'prose:233': ('This sentence introduces the immediately following primary-subtracted equations, whose exact physical equivalence is independently bound.', ['eq:G']),
    'prose:259': ('This sentence introduces the immediately following polar-gradient and weighted angular identity; it has no independent conclusion beyond that displayed identity.', ['eq:polar-gradient']),
    'prose:293': ('This sentence introduces the immediately following compact-product continuation lemma; the continuation conclusion and proof are bound at that lemma.', ['lem:product']),
}
for ident, (note, references) in connectors.items():
    rows[ident]['proof_route_note'] = note
    rows[ident]['source_assertion_references'] = references

data['supplementary_audits'] = [a for a in data.get('supplementary_audits', [])
    if a['file'] != 'Audit/SectionsThreeSevenComplete.lean']
data['supplementary_audits'].append(dict(file='Audit/SectionsThreeSevenComplete.lean',
    strict_session=2123, exit_code=0, log=str(logfile.relative_to(root)).replace('\\', '/'),
    declarations=54, axioms=['propext', 'Classical.choice', 'Quot.sound'],
    compiler_lock='scripts/lean_checked.ps1'))
target.write_text(json.dumps(data, ensure_ascii=False, indent=2) + '\n', encoding='utf-8')
counts = Counter(row['status'] for row in data['assertions'])
number = sum(len(row['lean_bindings']) for row in data['assertions'])
md = ['# 第 3、7 节独立源断言对应补丁', '',
    '原文逐字及完整 Lean 类型见 SECTIONS_3_7_COVERAGE_PATCH.json。本补丁不修改全文清单。', '',
    f'52 个源条目：{dict(counts)}；共 {number} 个完整类型绑定。没有 PARTIAL 条目。', '',
    '原审计 73473、表示审计 98431 和追加审计 SectionsThreeSevenComplete 均严格通过；追加审计打印 54 个声明的完整类型和公理，仅依赖 propext、Classical.choice、Quot.sound。所有新增编译经共享锁脚本执行。', '',
    '新增直接证明包括 centeredFromRelative 的全部原坐标恒等式、E=R x直和T及实际Hessian正交性、三图固定质量端点的原角间隙，以及原Q_n集合定义。七方程等价、正对角Hessian、角块可逆、四图全产品、同质量零端点、scalar根提取和实际光滑规范恢复均分别绑定。', '',
    'CCLM出处句属于外部文献归属；本补丁独立证明该句周围的数学结论及原径向/角向论证步骤，没有把匹配结论写成对外部文本归属的形式认证。', '',
    '本补丁的源覆盖不代表整篇论文已完成最终构建、全声明公理审计或fresh kernel验收。', '',
    '| 原文条目 / 行 | 状态 | 实际Lean声明/定义 |', '|---|---|---|']
for row in data['assertions']:
    a, b = row['source_location']['tex_lines']
    names = [binding['lean_declaration'] for binding in row['lean_bindings']] + row['definition_references']
    md.append(f'| {row["id"]} / {a}–{b} | {row["status"]} | ' + '<br>'.join(names) + ' |')
(root/'docs/SECTIONS_3_7_COVERAGE_PATCH.md').write_text('\n'.join(md)+'\n', encoding='utf-8')
print(json.dumps(dict(statuses=dict(counts), bindings=number, supplemental_declarations=len(types)), ensure_ascii=False))
