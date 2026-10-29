"""Bind the strict partial assertion audit to its actual files and tool exit."""
from pathlib import Path
import hashlib
import json
import os
import subprocess
from datetime import datetime, timezone

root = Path(__file__).resolve().parents[2]
rel = 'logs/source-audit-build/AssertionCoveragePartial.lean'
cmd = ['C:/Users/衔月/.elan/bin/lake.exe', 'env', 'lean',
       '-DwarningAsError=true', '-DautoImplicit=false', rel]
env = os.environ.copy()
env['LEAN_NUM_THREADS'] = '2'
result = subprocess.run(cmd, cwd=root, env=env, text=True,
                        encoding='utf-8', stdout=subprocess.PIPE,
                        stderr=subprocess.STDOUT)
out = root/'logs/source-audit-build/partial-audit.log'
out.write_text(result.stdout, encoding='utf-8')
ledger = json.loads((root/'docs/FULL_ASSERTIONS.json').read_text(encoding='utf-8'))
assertions = ledger['assertions']
counts = {status: sum(a['status'] == status for a in assertions)
          for status in ['VERIFIED', 'OPEN', 'CONDITIONAL']}
files = ['source/dominant_five_body_ARMA_rewritten.tex',
         'docs/FULL_ASSERTIONS.json', 'docs/FULL_ASSERTIONS.md', rel,
         'logs/source-audit-build/generate_assertions.py',
         'DominantFiveBody/CollisionScales.lean',
         'DominantFiveBody/CollisionPairScales.lean',
         'DominantFiveBody/PairActualCapture.lean',
         'DominantFiveBody/CollisionNestedScales.lean',
         'DominantFiveBody/CollisionNestedGeometry.lean',
         'lean-toolchain', 'lake-manifest.json']
receipt = {
    'timestamp_utc': datetime.now(timezone.utc).isoformat(),
    'command': cmd, 'environment': {'LEAN_NUM_THREADS': '2'},
    'exit_code': result.returncode,
    'assertion_count': len(assertions), 'status_counts': counts,
    'scope': 'partial typed assertion coverage; not whole-paper acceptance',
    'whole_paper_acceptance': False,
    'hashes': {p: hashlib.sha256((root/p).read_bytes()).hexdigest() for p in files},
    'axiom_output_sha256': hashlib.sha256(out.read_bytes()).hexdigest(),
    'axiom_output_path': 'logs/source-audit-build/partial-audit.log',
}
(root/'logs/source-audit-build/partial-audit-receipt.json').write_text(
    json.dumps(receipt, ensure_ascii=False, indent=2)+'\n', encoding='utf-8')
print(json.dumps({k: receipt[k] for k in ['exit_code', 'assertion_count',
      'status_counts', 'whole_paper_acceptance']}, indent=2))
raise SystemExit(result.returncode)
