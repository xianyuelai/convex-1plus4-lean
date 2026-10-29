"""Migrate the reviewed pre-v1 inventory to the immutable v1 manuscript.

This does not prove mathematics or promote a new obligation.  New mathematical
claims remain PARTIAL until their exact compiled Lean bindings are supplied.
All inherited rows retain their legacy identity and acquire exact v1 source
bytes; a separate complete block inventory guards against silent omissions.
"""
from pathlib import Path
import copy
import difflib
import hashlib
import json
import re

ROOT = Path(__file__).resolve().parents[1]
OLD_TEX = ROOT / 'source/dominant_five_body_ARMA_rewritten.tex'
NEW_TEX = ROOT / 'source/convex_1plus4.tex'
BASE = ROOT / 'logs/history/pre-v1/FULL_ASSERTIONS.json'


def digest_bytes(value):
    return hashlib.sha256(value).hexdigest().upper()


def read(path):
    return json.loads(path.read_text(encoding='utf-8-sig'))


def write(path, value):
    path.write_text(json.dumps(value, ensure_ascii=False, indent=2) + '\n', encoding='utf-8')


def source_units(lines, begin, end):
    """Inventory every display/table, named statement and prose paragraph."""
    units, occupied = [], set()
    i = begin - 1
    while i < end:
        s = lines[i].strip()
        m = re.match(r'\\begin\{(equation\*?|align\*?|gather\*?|table)\}', s)
        if s == r'\[' or m:
            closing = r'\]' if s == r'\[' else r'\end{' + m.group(1) + '}'
            j = i
            while j < end and closing not in lines[j]:
                j += 1
            if j == end:
                raise AssertionError(f'Unclosed source display at {i+1}')
            units.append(('display', i+1, j+1))
            occupied.update(range(i, j+1))
            i = j + 1
        else:
            i += 1
    named = re.compile(r'\\begin\{(theorem|lemma|proposition|corollary)\}')
    for i in range(begin-1, end):
        m = named.search(lines[i])
        if m:
            j = i
            closing = r'\end{' + m.group(1) + '}'
            while j < end and closing not in lines[j]:
                j += 1
            assert j < end
            units.append(('numbered', i+1, j+1))
    structural = re.compile(r'^\\(?:begin\{(?:abstract|proof|theorem|lemma|proposition|corollary)\}|end\{(?:abstract|proof|theorem|lemma|proposition|corollary)\}|section|subsection|paragraph|label\{)')
    start = None
    for i in range(begin-1, end+1):
        text = lines[i].strip() if i < end else ''
        skip = i in occupied or not text or text.startswith('%') or structural.match(text)
        if skip:
            if start is not None:
                units.append(('prose', start+1, i))
                start = None
        elif start is None:
            start = i
    return sorted(units, key=lambda u: (u[1], u[0], u[2]))


def main():
    old_lines = OLD_TEX.read_text(encoding='utf-8-sig').splitlines()
    new_lines = NEW_TEX.read_text(encoding='utf-8-sig').splitlines()
    ledger = read(BASE)
    opcodes = difflib.SequenceMatcher(None, old_lines, new_lines, autojunk=False).get_opcodes()
    changes = []
    for op, a, b, c, d in opcodes:
        if op != 'equal':
            changes.append(dict(number=len(changes)+1, operation=op,
                old_lines=[a+1,b], new_lines=[c+1,d],
                old_text='\n'.join(old_lines[a:b]), new_text='\n'.join(new_lines[c:d])))

    def mapped_interval(a, b):
        targets = []
        for op, i1, i2, j1, j2 in opcodes:
            lo, hi = max(a-1,i1), min(b,i2)
            if lo >= hi:
                continue
            if op == 'equal':
                targets.extend(range(j1+lo-i1+1, j1+hi-i1+1))
            elif op == 'replace':
                targets.extend(range(j1+1,j2+1))
        return [min(targets),max(targets)] if targets else None

    def source_text(a, b):
        return '\n'.join(new_lines[a-1:b])

    rows, retired = [], []
    for original in ledger['assertions']:
        row = copy.deepcopy(original)
        bounds = mapped_interval(*row['source_location']['tex_lines'])
        if bounds is None:
            retired.append(row)
            continue
        old_bounds = row['source_location']['tex_lines']
        row['legacy_source_location'] = copy.deepcopy(row['source_location'])
        row['source_location'] = dict(tex_path='source/convex_1plus4.tex',tex_lines=bounds,
                                     pdf_pages_from_aux_labels=[])
        row['source_text'] = source_text(*bounds)
        row['source_text_sha256'] = digest_bytes(row['source_text'].encode())
        row['v1_source_review'] = 'Preserved mathematical assertion; v1 source interval remapped from the complete pre-v1 ledger and reviewed against every manuscript diff block.'
        if row['claim_kind'] != 'source_subclaim':
            row['exact_claim'] = row['source_text']
        if row['paper_location'].startswith('TeX:'):
            row['paper_location'] = f'TeX:{bounds[0]}-{bounds[1]}'
        row['source_patch'] = 'V1_COVERAGE_PATCH.json'
        rows.append(row)
    by_id = {r['id']:r for r in rows}

    # The source now explicitly contains an equality, not merely a definition.
    row = by_id['eq:co-equations']
    row['status'] = 'VERIFIED'
    all_bindings = {b['lean_declaration']:b for r in ledger['assertions'] for b in r.get('lean_bindings',[])}
    equality_name = 'DominantFiveBody.coorbitalPotential_eq_angularPotential'
    row['lean_bindings'] = [copy.deepcopy(all_bindings.get(equality_name,
        dict(lean_declaration=equality_name,lean_statement='')))]
    row['proof_route_note'] = 'The old chord potential and the added angular-pair potential are equal by the actual unit-circle chord formula on OrderedSemicircle.'

    # New mathematical clauses must receive new exact Lean bindings.
    for key in ('prose:487','prose:833'):
        row = by_id[key]
        row['status'] = 'PARTIAL'
        row['remaining_dependencies'] = ['New v1 displayed estimate / off-solution correction requires exact additional Lean bindings.']
        row['v1_source_review'] = 'Existing limiting/boundary conclusions are retained; new formulas are separately open until their bridge lemmas compile and are bound.'

    # This is an explicit source-domain convention, already present as hconv
    # and horder in all three actual Lean scale theorems.
    for row in rows:
        if 'For the remainder of this section' in row.get('source_text','') and row['claim_kind']=='prose_assertion':
            row.update(status='CROSS_REFERENCE', lean_bindings=[], remaining_dependencies=[],
                source_assertion_references=['prop:pair-scale','prop:triple-scale','prop:nested-scale'],
                proof_route_note='v1 explicitly restricts the remaining section to strictly convex configurations in the standard directed order; the referenced Lean physical scale theorems already receive hconv and horder. This is a scope convention, not a new unconditional theorem.')

    def add(key, a, b, kind='displayed_assertion'):
        text = source_text(a,b)
        rows.append(dict(id=key,source_location=dict(tex_path='source/convex_1plus4.tex',tex_lines=[a,b],pdf_pages_from_aux_labels=[]),
            paper_location=f'TeX:{a}-{b}',exact_claim=text,source_text=text,
            source_text_sha256=digest_bytes(text.encode()),claim_kind=kind,status='PARTIAL',
            lean_bindings=[],remaining_dependencies=['Compile and bind the corresponding new v1 physical-object bridge lemmas.'],
            source_patch='V1_COVERAGE_PATCH.json',v1_source_review='New v1 mathematical assertion; no inherited success status.'))
    add('v1:hessian.coordinates',111,114)
    add('v1:hessian.entries',115,117)
    add('v1:hessian.quadratic',119,125)
    add('v1:hessian.slice',126,128,'prose_assertion')
    add('v1:hessian.quadratic_connector',118,118,'prose_assertion')
    rows[-1].update(status='CROSS_REFERENCE',remaining_dependencies=[],
        source_assertion_references=['v1:hessian.quadratic'],
        proof_route_note='Connector specifying the vector domain for the following matrix quadratic identity.')
    add('v1:boundary.off_solution_projection',841,844)

    start = next(i+2 for i,s in enumerate(new_lines) if s==r'\begin{abstract}')
    end = next(i for i,s in enumerate(new_lines) if r'\begin{thebibliography}' in s)
    units = source_units(new_lines,start,end)
    inventory=[]
    missing=[]
    for kind,a,b in units:
        covered=[r['id'] for r in rows if r['source_location']['tex_lines'][0]<=a and r['source_location']['tex_lines'][1]>=b]
        if not covered:
            # Newly split prose paragraphs can span two inherited units.  All
            # substantive lines must be covered, rather than guessed by text.
            covered=sorted({r['id'] for n in range(a,b+1) for r in rows
                if r['source_location']['tex_lines'][0]<=n<=r['source_location']['tex_lines'][1]})
            uncovered=[n for n in range(a,b+1) if new_lines[n-1].strip() and not any(
                r['source_location']['tex_lines'][0]<=n<=r['source_location']['tex_lines'][1] for r in rows)]
            if uncovered:
                missing.append(dict(kind=kind,lines=[a,b],uncovered=uncovered,text=source_text(a,b)))
        raw=source_text(a,b)
        inventory.append(dict(kind=kind,tex_lines=[a,b],source_text_sha256=digest_bytes(raw.encode()),covering_assertions=covered))
    if missing:
        print(json.dumps(missing,ensure_ascii=False,indent=2))
        raise AssertionError(f'{len(missing)} unmapped source blocks')
    for row in rows:
        for ref in row.get('source_assertion_references',[]):
            assert ref in {r['id'] for r in rows}, f'Retired referenced row {ref}'
    ledger['source_scope'].update(tex_path='source/convex_1plus4.tex',pdf_path='source/convex_1plus4.pdf',
        tex_sha256=digest_bytes(NEW_TEX.read_bytes()),pdf_sha256=digest_bytes((ROOT/'source/convex_1plus4.pdf').read_bytes()),
        source_body_tex_lines=[start,end],version='v1',
        page_mapping_note='v1 has 19 pages; exact source line intervals and raw-source hashes are checked. Old auxiliary page locations are not reused.')
    ledger.update(schema_version=3,version='v1',assertions=sorted(rows,key=lambda r:(r['source_location']['tex_lines'][0],r['id'])),
        coverage_patches=['V1_COVERAGE_PATCH.json'],source_inventory_units=inventory,
        migration_review='docs/V1_SOURCE_CHANGE_REVIEW.json',complete_source_inventory=True)
    write(ROOT/'docs/FULL_ASSERTIONS.json',ledger)
    write(ROOT/'docs/V1_COVERAGE_PATCH.json',dict(schema_version=3,version='v1',
        source_tex_sha256=ledger['source_scope']['tex_sha256'],assertions=ledger['assertions']))
    write(ROOT/'docs/V1_SOURCE_CHANGE_REVIEW.json',dict(version='v1',
        baseline_ledger_sha256=digest_bytes(BASE.read_bytes()),
        old_tex_sha256=digest_bytes(OLD_TEX.read_bytes()),new_tex_sha256=ledger['source_scope']['tex_sha256'],
        changes=changes,retired_assertions=retired,
        review_scope='Complete old/new TeX diff and all 14 unchanged formal result statements. New estimates and coordinate identities require fresh Lean bridges; semantic correspondence is a documented source review, not a formal parser proof of natural language.'))
    print(f'Migrated {len(rows)} rows; inventoried {len(inventory)} blocks; {len(changes)} diff blocks; {len(retired)} retired rows.')


if __name__=='__main__':
    main()
