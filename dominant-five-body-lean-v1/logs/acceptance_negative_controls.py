"""Exercise metadata rejection in memory; never edit the real source ledger."""
from copy import deepcopy
from pathlib import Path
from datetime import datetime, timezone
import importlib.util
import json
import subprocess
import sys

ROOT = Path(__file__).resolve().parents[1]
spec = importlib.util.spec_from_file_location("coverage_under_test", ROOT / "scripts/paper_coverage.py")
module = importlib.util.module_from_spec(spec)
spec.loader.exec_module(module)
original_read = module.read
baseline = original_read(module.LEDGER)
module.read = lambda path: deepcopy(baseline) if path == module.LEDGER else original_read(path)
# This baseline permits genuine still-open development rows; it validates
# everything else. Negative controls identify their own precise rejection.
_, rows, development_open = module.checked_ledger(allow_open=True, check_types=False)
verified = next(row for row in baseline["assertions"] if row["status"] == "VERIFIED")
cross = next(row for row in baseline["assertions"] if row["status"] == "CROSS_REFERENCE")
checks = []

def rejected(name, mutate, reason, allow_open=True):
    changed = deepcopy(baseline)
    mutate(changed)
    module.read = lambda path: deepcopy(changed) if path == module.LEDGER else original_read(path)
    try:
        module.checked_ledger(allow_open=allow_open, check_types=False)
    except AssertionError as error:
        message = str(error)
        if reason not in message:
            raise RuntimeError(f"{name} failed for an unrelated reason: {message}") from error
        checks.append(dict(name=name, rejected=True, reason=message))
    else:
        raise RuntimeError(f"False success: {name}")

def row_with(data, ident):
    return next(row for row in data["assertions"] if row["id"] == ident)

ident = verified["id"]
def make_open(data):
    row = row_with(data, ident)
    row["status"] = "OPEN"
    row["remaining_dependencies"] = ["Negative-control original obligation"]

rejected("OPEN original assertion", make_open, ident + ": OPEN", allow_open=False)
rejected("Missing exact theorem binding", lambda data: row_with(data, ident).__setitem__("lean_bindings", []),
         "No exact theorem binding: " + ident)
rejected("Closed context hides a remaining obligation",
         lambda data: row_with(data, cross["id"]).__setitem__("remaining_dependencies", ["Unproved source subclaim"]),
         "Closed assertion retains unresolved dependencies: " + cross["id"])
rejected("Changed TeX source hash", lambda data: data["source_scope"].__setitem__("tex_sha256", "0" * 64),
         "tex source bytes differ from the reviewed inventory")
rejected("Duplicate assertion ID", lambda data: data["assertions"].append(deepcopy(verified)),
         "Empty or duplicate assertion IDs")

# An optimized interpreter must reject the module before assertion-based
# validation could be disabled. This child also performs no file mutation.
optimized = subprocess.run([sys.executable, "-I", "-X", "utf8", "-O", "-c",
    "import runpy; runpy.run_path(" + repr(str(ROOT / "scripts/paper_coverage.py")) + ")"],
    capture_output=True, text=True, encoding="utf-8")
if optimized.returncode == 0 or "must run without Python optimization" not in optimized.stderr:
    raise RuntimeError("Optimized Python did not reject the validator")
checks.append(dict(name="Python optimization", rejected=True, exit_code=optimized.returncode,
                  reason=optimized.stderr.strip()))

result = dict(created_at=datetime.now(timezone.utc).isoformat(), passed=True,
              scope="In-memory metadata negative controls only; not a Lean kernel check",
              real_ledger_was_modified=False, validated_source_rows=len(rows),
              baseline_development_open_rows=len(development_open), checks=checks)
(ROOT / "logs/ACCEPTANCE_NEGATIVE_CONTROLS.json").write_text(json.dumps(result, ensure_ascii=False, indent=2) + "\n", encoding="utf-8")
print(json.dumps({"passed": True, "checks": len(checks), "baseline_rows": len(rows),
                  "baseline_development_open_rows": len(development_open)}, ensure_ascii=False))
