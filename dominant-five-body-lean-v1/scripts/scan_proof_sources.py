"""Reject forbidden proof tokens outside Lean comments and string literals.

This is supplementary hygiene; actual theorem bodies, axiom closures and the
kernel replay are independently checked. It is not a Lean parser or a proof.
"""
from pathlib import Path
import re

ROOT = Path(__file__).resolve().parents[1]
FORBIDDEN = {'sorry', 'admit', 'sorryAx', 'axiom', 'constant', 'native_decide', 'unsafe', 'implemented_by'}


def code_only(text):
    out, depth, i, quoted = [], 0, 0, False
    while i < len(text):
        pair = text[i:i+2]
        char = text[i]
        if quoted:
            if char == '\\':
                out.extend('  ')
                i += 2
                continue
            if char == '"':
                quoted = False
            out.append('\n' if char == '\n' else ' ')
            i += 1
        elif depth:
            if pair == '/-':
                depth += 1
                out.extend('  ')
                i += 2
            elif pair == '-/':
                depth -= 1
                out.extend('  ')
                i += 2
            else:
                out.append('\n' if char == '\n' else ' ')
                i += 1
        elif pair == '/-':
            depth = 1
            out.extend('  ')
            i += 2
        elif pair == '--':
            end = text.find('\n', i)
            end = len(text) if end < 0 else end
            out.extend(' ' * (end-i))
            i = end
        elif char == '"':
            quoted = True
            out.append(' ')
            i += 1
        else:
            out.append(char)
            i += 1
    if depth or quoted:
        raise ValueError('Unterminated Lean comment or string')
    return ''.join(out)


def main():
    files = list(ROOT.glob('*.lean'))
    for directory in ('DominantFiveBody', 'Audit', 'PaperAcceptance'):
        files += list((ROOT / directory).rglob('*.lean'))
    failures = []
    for path in files:
        code = code_only(path.read_text(encoding='utf-8-sig'))
        for token in re.finditer(r"[A-Za-z_][A-Za-z_0-9']*", code):
            if token[0] in FORBIDDEN:
                failures.append(f'{path.relative_to(ROOT)}:{code[:token.start()].count(chr(10))+1}: {token[0]}')
    if failures:
        raise SystemExit('Forbidden proof tokens:\n' + '\n'.join(failures))
    print(f'No forbidden proof tokens in {len(files)} Lean source files')


if __name__ == '__main__':
    main()
