"""Merge independently reviewed source patches, preserving open obligations.

This is bookkeeping only. Exact type elaboration, axiom traversal and fresh
kernel replay are performed by verify_paper.ps1, not by this script.
"""
from pathlib import Path
from collections import Counter
import hashlib, json

root=Path(__file__).resolve().parents[1]
target=root/'docs/FULL_ASSERTIONS.json'
ledger=json.loads(target.read_text(encoding='utf-8-sig'))
source=root/ledger['source_scope']['tex_path']
digest=hashlib.sha256(source.read_bytes()).hexdigest().upper()
if ledger['source_scope']['tex_sha256'].upper()!=digest:
    raise SystemExit('Source hash differs from the complete original inventory.')
rows={e['id']:e for e in ledger['assertions']}
patches=ledger['coverage_patches']
applied=[]
for filename in patches:
    path=root/'docs'/filename
    if not path.exists():
        continue
    data=json.loads(path.read_text(encoding='utf-8-sig'))
    pdigest=data.get('source_tex_sha256',data.get('source_sha256'))
    if pdigest and pdigest.upper()!=digest:
        raise SystemExit(f'Source hash differs in {filename}')
    for update in data['assertions']:
        key=update['id']
        if key not in rows:
            raise SystemExit(f'Unknown assertion {key} in {filename}')
        old=rows[key]
        if update.get('exact_claim',old['exact_claim'])!=old['exact_claim']:
            raise SystemExit(f'Changed source assertion {key} in {filename}')
        original={k:old[k] for k in ('id','source_location','paper_location','exact_claim','claim_kind')}
        original.update(update)
        original['source_patch']=filename
        if original['status']=='SOURCE_CROSS_REFERENCE':
            original['status']='CROSS_REFERENCE'
        refs=original.get('source_assertion_references',original.get('source_cross_references'))
        if refs:
            original['source_assertion_references']=refs
        # Remove obsolete single-binding and target-only placeholders.
        bindings=original.get('lean_bindings',[])
        original['lean_declaration']=bindings[0]['lean_declaration'] if len(bindings)==1 else None
        original['lean_statement']=bindings[0]['lean_statement'] if len(bindings)==1 else None
        rows[key]=original
    applied.append(filename)
ledger['assertions']=sorted(rows.values(),key=lambda e:(e['source_location']['tex_lines'][0],e['id']))
ledger['schema_version']=2
ledger['coverage_patches']=applied
ledger['lean_statement_context']=['open scoped BigOperators ContDiff Matrix.Norms.Operator Topology',
    'universe u_1 u_2 u_3 u_4 u_5 u_6 u v w']
ledger['verification_note']='Source-reviewed mathematical coverage. VERIFIED bindings still require the final exact-type, all-axiom, rebuild and kernel receipts. OPEN/PARTIAL/CONDITIONAL substantive claims fail whole-paper acceptance. CROSS_REFERENCE is checked recursively, and is not an independent proof. DEFINITIONAL rows require exact definition-value bindings. Background citations and pure connectors are explicitly identified.'
target.write_text(json.dumps(ledger,ensure_ascii=False,indent=2)+'\n',encoding='utf-8')
counts=Counter(e['status'] for e in ledger['assertions'])
open_count=sum(counts[s] for s in ('OPEN','PARTIAL','CONDITIONAL'))
numbered=[e for e in ledger['assertions'] if e['claim_kind']=='numbered_assertion']
md=['# 全文数学断言对应表','',
    '主定理已有无条件证明。本文档另行核对原文全部实质数学断言；主定理的证明不自动关闭原稿中被替代的推导。',
    '',f'共 {len(ledger["assertions"])} 项源码记录。当前状态：'+str(dict(counts))+'。',
    '完整类型、子断言、原文逐字内容及尚缺依赖见 FULL_ASSERTIONS.json；最终验收入口为 scripts/verify_paper.ps1。',
    '', '| 原文位置 | 精确断言 | Lean 声明 | 尚缺依赖 | 状态 |', '|---|---|---|---|---|']
for e in ledger['assertions']:
    a,b=e['source_location']['tex_lines']
    binding=e.get('lean_bindings',[])
    names=[x['lean_declaration'] for x in binding]
    if not names and e.get('lean_declaration'): names=[e['lean_declaration']]
    claim=e['exact_claim'].replace('\n',' ').replace('|','\\|')
    deps='; '.join(e.get('remaining_dependencies',[])).replace('|','\\|')
    if e.get('source_assertion_references'):
        names+=['源交叉引用 '+', '.join(e['source_assertion_references'])]
    if e.get('definition_references'): names+=e['definition_references']
    md.append(f'| {e["id"]} / TeX {a}–{b} | {claim} | '+ '<br>'.join(names)+f' | {deps} | {e["status"]} |')
(root/'docs/FULL_ASSERTIONS.md').write_text('\n'.join(md)+'\n',encoding='utf-8')
status=['# 论文形式化当前状态','',
    '`DominantFiveBody.main_uniform : DominantFiveBody.MainUniformStatement` 已有实际无条件证明体。',
    'v1 独立 `PaperAcceptance/Main.lean` 的实际检查、公理范围及通过状态，以本版本 `logs/PAPER_ACCEPTANCE.json` 和其绑定日志为准。历史增量日志不代替本次检查。',
    '', ('**整篇论文尚未完成最终验收。** 原稿独立推导仍有未闭合条目。' if open_count else
         '**数学断言账本已闭合；最终验收以 `logs/PAPER_ACCEPTANCE.json` 为准。** 账本状态本身不代替完整重建和内核复检。'),
    '验证记录只适用于其中绑定的源码 SHA256；历史 `logs/VERIFICATION.json` 不能自动验证后续修改。',
    '', '主规格的独立语义核对见 `FINAL_MAIN_SEMANTIC_AUDIT.md`。全文逐项范围见 `FULL_ASSERTIONS.json`，其中原命题证明、原稿推导及替代证法分别记录。',
    '', '| 编号命题 | 当前源覆盖状态 | 尚缺依赖 |','|---|---|---|']
for e in numbered:
    status.append('| '+e['id']+' | '+e['status']+' | '+'; '.join(e.get('remaining_dependencies',[])).replace('|','\\|')+' |')
status+=['', ('当前正在补原稿中与替代主证明相互独立的中间断言，包括原缩放分组证明、标量势的原凸性路线、图的完整公式和定量估计。已证主定理不降低这些验收义务。' if open_count else
    '全部编号命题及实质中间断言均有实际声明、定义或递归源交叉引用绑定；原稿推导与替代证法的区别逐项保留。'),
    '', '后续验收还必须完成：所有正式模块统一构建、全声明公理审计、逐条完整类型重验、与锁定版本匹配的 fresh kernel replay，以及最终 verify_paper 成功记录。工具链保持 Lean 4.33.1，mathlib 保持锁定 revision。']
(root/'docs/STATUS.md').write_text('\n'.join(status)+'\n',encoding='utf-8')
print(json.dumps(dict(entries=len(rows),statuses=dict(counts),patches=applied),ensure_ascii=False,indent=2))
