"""List every mathematical source module in dependency order for bounded-memory builds."""
from pathlib import Path
import json
import re

root = Path(__file__).resolve().parents[1]
modules = {'DominantFiveBody.' + p.stem: p for p in (root / 'DominantFiveBody').glob('*.lean')}
ordered, active, done = [], set(), set()


def visit(name):
    if name in done:
        return
    if name in active:
        raise RuntimeError('Cyclic project imports: ' + name)
    active.add(name)
    for dep in re.findall(r'^import\s+(\S+)', modules[name].read_text(encoding='utf-8-sig'), re.M):
        if dep == 'DominantFiveBody':
            raise RuntimeError('Mathematical module imports its own umbrella: ' + name)
        if dep.startswith('DominantFiveBody.'):
            if dep not in modules:
                raise RuntimeError('Missing local source module: ' + dep)
            visit(dep)
    active.remove(name)
    done.add(name)
    ordered.append(name)


for name in sorted(modules):
    visit(name)
(root / 'logs/MODULE_BUILD_ORDER.json').write_text(json.dumps(ordered, indent=2) + '\n', encoding='utf-8')
print(f'{len(ordered)} modules in dependency order')
