"""Package the accepted v1 bytes, or validate them read-only with --check.

The existing locked environment is never installed, updated or invoked here.
Source identity, release metadata and the actual acceptance receipt must agree.
Runtime caches and locks are omitted; mathematical lockfiles and evidence stay.
"""
from pathlib import Path
import argparse
import datetime
import hashlib
import json
import os
import zipfile

ROOT = Path(__file__).resolve().parents[1]
VERSION = 'v1'
IDENTITY_FIELDS = ('tex_path', 'pdf_path', 'tex_sha256', 'pdf_sha256', 'pdf_page_count')
SOURCE_DIRECTORIES = ('DominantFiveBody', 'Audit', 'PaperAcceptance', 'scripts',
                      'source', 'docs', 'paper-reading')
RELEASE_FILES = ('README.md', 'FINAL_REPORT.md', 'PROOF_PACKAGE.md', 'VERSION.json',
                 '.gitignore', '.gitattributes', 'logs/SOURCE_BINDING.json')
EXCLUDED_DIRECTORIES = {'.lake', '.git', '__pycache__', '.cache', 'cache', 'tmp', 'temp'}
EXCLUDED_SUFFIXES = {'.pyc', '.pyo', '.tmp', '.lock'}


def sha256(path):
    return hashlib.sha256(path.read_bytes()).hexdigest().upper()


def read_json(path):
    return json.loads(path.read_text(encoding='utf-8-sig'))


def checked_relative_path(relative):
    """Receipt paths must stay in this project and use canonical POSIX spelling."""
    if not isinstance(relative, str):
        raise SystemExit('Noncanonical receipt path: ' + str(relative))
    path = ROOT / relative
    if not path.is_relative_to(ROOT) or path.relative_to(ROOT).as_posix() != relative:
        raise SystemExit('Noncanonical receipt path: ' + str(relative))
    if path.is_symlink() or not path.resolve().is_relative_to(ROOT.resolve()):
        raise SystemExit('Receipt path leaves this project: ' + relative)
    return path


def required_accepted_files():
    files = set(RELEASE_FILES)
    for directory in SOURCE_DIRECTORIES:
        for path in (ROOT / directory).rglob('*'):
            if path.is_file() and path.suffix not in {'.pyc', '.log'}:
                files.add(path.relative_to(ROOT).as_posix())
    for path in ROOT.iterdir():
        if path.is_file() and (path.suffix == '.lean' or path.name in
                               {'lakefile.toml', 'lake-manifest.json', 'lean-toolchain'}):
            files.add(path.relative_to(ROOT).as_posix())
    return files


def validate_acceptance():
    receipt_path = ROOT / 'logs/PAPER_ACCEPTANCE.json'
    receipt = read_json(receipt_path)
    if receipt.get('paper_verified') is not True:
        raise SystemExit('Whole-paper acceptance has not succeeded.')
    version = read_json(ROOT / 'VERSION.json')
    if version.get('version') != VERSION or receipt.get('version') != VERSION:
        raise SystemExit('The release and acceptance receipt must both identify v1.')
    identity = version.get('source_identity', {})
    if set(identity) != set(IDENTITY_FIELDS) or receipt.get('source_identity') != identity:
        raise SystemExit('Acceptance does not bind the current authoritative source identity.')
    if identity['tex_path'] != 'source/convex_1plus4.tex' or identity['pdf_path'] != 'source/convex_1plus4.pdf':
        raise SystemExit('v1 requires the frozen convex_1plus4 TeX/PDF pair.')
    for kind in ('tex', 'pdf'):
        if sha256(checked_relative_path(identity[kind + '_path'])) != identity[kind + '_sha256']:
            raise SystemExit('Authoritative ' + kind + ' bytes differ from VERSION.json.')
    ledger = read_json(ROOT / 'docs/FULL_ASSERTIONS.json')
    scope = ledger.get('source_scope', {})
    if scope.get('version') != VERSION or any(scope.get(k) != identity[k] for k in IDENTITY_FIELDS):
        raise SystemExit('The full assertion ledger belongs to a different source or version.')
    binding = read_json(ROOT / 'logs/SOURCE_BINDING.json')
    if binding.get('version') != VERSION or binding.get('source_identity') != identity:
        raise SystemExit('The source correspondence receipt belongs to another source or version.')
    if binding.get('pdf_layout_normalized_text_identical') is not True:
        raise SystemExit('The complete supplied/rebuilt PDF text comparison has not succeeded.')
    if binding.get('supplied_pdf_pages') != identity['pdf_page_count'] or binding.get('rebuilt_pdf_pages') != identity['pdf_page_count']:
        raise SystemExit('Source correspondence page counts differ.')
    hashes = receipt.get('source_and_code_sha256', {})
    if not isinstance(hashes, dict) or not hashes:
        raise SystemExit('Acceptance has no source-and-code hash inventory.')
    missing = sorted(required_accepted_files() - set(hashes))
    if missing:
        preview = ', '.join(missing[:12])
        raise SystemExit(f'Current files were not covered by acceptance ({len(missing)} total): ' + preview)
    for relative, expected in hashes.items():
        path = checked_relative_path(relative)
        if not path.is_file() or sha256(path) != expected.upper():
            raise SystemExit('Source changed after whole-paper acceptance: ' + relative)
    if sha256(ROOT / 'logs/VERIFICATION.json') != receipt.get('development_receipt_sha256', '').upper():
        raise SystemExit('Development verification receipt changed.')
    development = read_json(ROOT / 'logs/VERIFICATION.json')
    if not all(development.get(key) is True for key in
               ('verification_complete', 'main_uniform_proved', 'all_declared_theorems_axiom_audited')):
        raise SystemExit('Development verification lacks required successful checks.')
    coverage = receipt.get('coverage', {})
    if coverage.get('whole_paper_closed') is not True or coverage.get('unclosed_assertions') != []:
        raise SystemExit('Whole-paper coverage is not closed.')
    for key, relative in [('ledger_sha256', 'docs/FULL_ASSERTIONS.json'),
                          ('definition_bindings_sha256', 'docs/DEFINITION_BINDINGS.json'),
                          ('coverage_lean_sha256', 'PaperAcceptance/Coverage.lean')]:
        if sha256(ROOT / relative) != coverage.get(key, '').upper():
            raise SystemExit('Coverage no longer matches: ' + relative)
    for relative, expected in binding.get('evidence_files_sha256', {}).items():
        path = checked_relative_path(relative)
        if not path.is_file() or sha256(path) != expected.upper():
            raise SystemExit('Source-comparison evidence changed: ' + relative)
    return receipt_path, version, identity


def package_files():
    files = []
    for directory, subdirs, names in os.walk(ROOT, followlinks=False):
        subdirs[:] = [name for name in subdirs if name not in EXCLUDED_DIRECTORIES]
        for name in names:
            path = Path(directory) / name
            if path.is_symlink():
                raise SystemExit('Do not package a file symlink: ' + str(path))
            if name != 'DELIVERY.json' and path.suffix not in EXCLUDED_SUFFIXES:
                files.append(path)
    return sorted(files)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--check', action='store_true', help='Validate acceptance without writing any files or archive.')
    args = parser.parse_args()
    receipt_path, version, identity = validate_acceptance()
    if args.check:
        print(json.dumps({'version': VERSION, 'acceptance_valid': True,
                          'source_identity': identity,
                          'acceptance_receipt_sha256': sha256(receipt_path)}, ensure_ascii=False, indent=2))
        return
    files = package_files()
    manifest = {
        'schema_version': 2,
        'version': VERSION,
        'paper_verified': True,
        'created_at': datetime.datetime.now(datetime.timezone.utc).isoformat(),
        'source_identity': identity,
        'version_metadata_sha256': sha256(ROOT / 'VERSION.json'),
        'source_binding_receipt_sha256': sha256(ROOT / 'logs/SOURCE_BINDING.json'),
        'acceptance_receipt_sha256': sha256(receipt_path),
        'dependency_cache_included': False,
        'excluded_runtime_directories': sorted(EXCLUDED_DIRECTORIES),
        'files_sha256': {path.relative_to(ROOT).as_posix(): sha256(path) for path in files},
    }
    output = ROOT.parent / (ROOT.name + '.zip')
    temporary = output.with_suffix('.zip.tmp')
    with zipfile.ZipFile(temporary, 'w', compression=zipfile.ZIP_DEFLATED, compresslevel=9) as archive:
        for path in files:
            archive.write(path, ROOT.name + '/' + path.relative_to(ROOT).as_posix())
        archive.writestr(ROOT.name + '/DELIVERY.json', json.dumps(manifest, ensure_ascii=False, indent=2) + '\n')
    with zipfile.ZipFile(temporary) as archive:
        if archive.testzip() is not None:
            raise SystemExit('Archive integrity test failed.')
        for relative, expected in manifest['files_sha256'].items():
            observed = hashlib.sha256(archive.read(ROOT.name + '/' + relative)).hexdigest().upper()
            if observed != expected:
                raise SystemExit('Archive content differs: ' + relative)
    # Re-check after writing: accepted files must not change during packaging.
    validate_acceptance()
    if sha256(receipt_path) != manifest['acceptance_receipt_sha256']:
        raise SystemExit('Acceptance receipt changed during packaging.')
    os.replace(temporary, output)
    (ROOT / 'DELIVERY.json').write_text(json.dumps(manifest, ensure_ascii=False, indent=2) + '\n', encoding='utf-8')
    output.with_suffix('.zip.sha256').write_text(sha256(output) + '  ' + output.name + '\n', encoding='utf-8')
    print(json.dumps({'archive': str(output), 'files': len(files) + 1,
                      'bytes': output.stat().st_size, 'sha256': sha256(output)}, ensure_ascii=False, indent=2))


if __name__ == '__main__':
    main()
