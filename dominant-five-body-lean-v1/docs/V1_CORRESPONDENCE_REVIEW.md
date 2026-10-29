# v1 源稿对应独立审查记录

本记录在最终整篇验收前冻结。结论是：当前 v1 源稿与账本的文本、位置、增量数学桥接对应未发现未解决问题；本记录不宣称整篇 Lean 验收或 ZIP 发布通过。

## 实际核对范围

权威底本为 `source/convex_1plus4.tex` 与同名 PDF，共 19 页。TeX SHA256 为 `7EA6C309533C233C1BDD5B6C4BDD0BD8DB7374248699FDFD64AD63C124DD6C02`。完整机器记录与输入 SHA256 见 `docs/V1_CORRESPONDENCE_REVIEW.json`。

- 实核 349 个账本记录的源区间、逐行文本与 SHA256；320 条非子断言的 exact_claim 与区间原文完全相等。29 条历史 source_subclaim 是审查后的子断言表述，保持与已哈希历史底本逐字相同，并非伪装成原稿逐字引文。
- 独立重算 28 个 old/new diff 块，六个原始字段全部一致；14 个正式 theorem/lemma/proposition 陈述逐字未变。
- 330 个正文块为 116 个显示公式/表格、14 个正式陈述、200 个散文块。另做不依赖分段器的行区间并集检查：未覆盖的非空行仅为第 56、74、224 行的章节标题，无数学正文。正文内容范围由 TeX 独立导出为 53–1004；abstract 完整记录另包含第 52 行的环境起始语法。
- 当前状态为 282 VERIFIED、48 CROSS_REFERENCE、13 DEFINITIONAL、5 NON_MATHEMATICAL、1 BACKGROUND，无 OPEN/PARTIAL/CONDITIONAL。实际有 622 个不同 Lean 声明、856 次绑定，显式类型均非空；57 个定义记录均有类型和值。这些是当前数据事实，最终重新 elaboration 仍由验收流程负责。
- 独立逐字节确认旧工程的 277 个数学模块在 v1 中未变，Main/Specification 亦同；新增三份桥接。该字节事实不代替对旧证明内部的重新审查。

## 新增数学断言对应

| 新稿位置 | 账本记录 | 审查结论 |
|---|---|---|
| 90–97 | eq:co-equations | 真实弦长势与角核势相等；原残差、距离、势及卫星对定义引用保留。A：严格成立。 |
| 111–128 | v1:hessian.* | 从真实物理势二阶 fderiv 到矩阵元素、二次型和三维实际受限势的拉回。只要求原开半圆角域；没有增加平衡或正质量前提。Lean 索引 0 对应原稿 θ₁。A：严格成立。 |
| 371 | prose:360 | 严格凸、标准有向顺序明确化；实际尺度与 capture 定理原已带 hconv/horder。A：严格成立。 |
| 495–496 | prose:487 | C=1536 显示界及右边本身的一致 o(1)，均覆盖上下端实际 pair 极坐标矩形，没有质量比例下界。旧各源贡献极限保留。A：严格成立。 |
| 837–846 | prose:833 与 v1:boundary.off_solution_projection | 真实离解残差恒等式、不除 μ；只在 ε≠0 时除 ε。真正 Y−cεX 的立方因子及 O(t³) 接入实际 regular/nested/slow 路径。A：严格成立。 |

Hessian 新式没有以旧 `deletedAngularJacobian` 代替实际势的矩阵。`prose:833` 保留旧 `reaction_Ocube`，仅用于其原本的 reaction 变化断言；新 Y−cεX 必须另外绑定真正 fieldDefect 定理。三维切片经过实际一阶、二阶链式法则，没有仅定义一个期望二次型就称其为 Hessian。

近源新桥接使用了后段已经独立证明的精确尺度；`prose:487.proof_route` 已明确披露这条重排证明路线。旧尺度模块不导入新桥接，所以没有形式依赖循环，也没有声称逐步复刻原文的证明先后。

## 自动源校验与负向对照

对真实 `checked_ledger` 做深复制内存变异，磁盘源稿、账本和共享脚本保持不变。最终命令：

```powershell
python -B scripts/v1_source_negative_controls.py
```

实际基线接受 349 行、0 个未闭合项；35/35 个负向对照均被拒绝。日志为 `logs/V1_SOURCE_NEGATIVE_CONTROLS.json`。覆盖 stale 区间/文本/hash、exact_claim 与源不符、complete=true 时删块或删新增公式、版本降级、伪造 source_subclaim 豁免、缩小正文、删除无其他引用的历史义务、删新旧证明或定义绑定，以及用旧 uniform limits/reaction_Ocube 替代新数学桥接。

审查中曾发现并推动修复版本门控、可自选正文/豁免、未引用历史行可删除、新绑定可部分丢失等缺口。删除历史义务后接受 348 行、移除三类新绑定后仍接受的情况，确曾在仅内存变异中观察到；修复后的同类测试全部拒绝。当前验证器独立派生正文边界、重算源块和 28 个 diff、核对历史与新增 ID/种类/状态，并强制静态已审 theorem/definition 清单保留。

## 证据边界

总体判断：指定增量断言的对应证明成立，源完整性负向测试通过；未发现未解决的 v1 对应问题。最严重的三个当前问题：未发现。

这仍包含人工的 TeX/自然语言到 Lean 语义审查，不是该翻译过程的形式化定理。分段器针对当前源稿语法核对，不是任意未来 TeX 的完备解析器。本轮没有从头重审 277 个旧模块的全部内部证明，也没有运行最终 clean 全量构建、公理审计、fresh kernel 或打包。最终整篇是否通过，只能由独立的当次验收 receipt 判断；旧成功记录和本记录均不可代替它。
