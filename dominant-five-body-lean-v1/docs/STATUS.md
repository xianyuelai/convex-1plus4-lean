# 论文形式化当前状态

`DominantFiveBody.main_uniform : DominantFiveBody.MainUniformStatement` 已有实际无条件证明体。
v1 独立 `PaperAcceptance/Main.lean` 的实际检查、公理范围及通过状态，以本版本 `logs/PAPER_ACCEPTANCE.json` 和其绑定日志为准。历史增量日志不代替本次检查。

**数学断言账本已闭合；最终验收以 `logs/PAPER_ACCEPTANCE.json` 为准。** 账本状态本身不代替完整重建和内核复检。
验证记录只适用于其中绑定的源码 SHA256；历史 `logs/VERIFICATION.json` 不能自动验证后续修改。

主规格的独立语义核对见 `FINAL_MAIN_SEMANTIC_AUDIT.md`。全文逐项范围见 `FULL_ASSERTIONS.json`，其中原命题证明、原稿推导及替代证法分别记录。

| 编号命题 | 当前源覆盖状态 | 尚缺依赖 |
|---|---|---|
| thm:main | VERIFIED |  |
| lem:cycle | VERIFIED |  |
| thm:coorbital | VERIFIED |  |
| lem:probe | VERIFIED |  |
| prop:closed | VERIFIED |  |
| lem:hessian | VERIFIED |  |
| lem:product | VERIFIED |  |
| prop:local | VERIFIED |  |
| prop:uniform | VERIFIED |  |
| prop:pair-scale | VERIFIED |  |
| prop:triple-scale | VERIFIED |  |
| prop:nested-scale | VERIFIED |  |
| prop:chart-interface | VERIFIED |  |
| prop:connection | VERIFIED |  |

全部编号命题及实质中间断言均有实际声明、定义或递归源交叉引用绑定；原稿推导与替代证法的区别逐项保留。

后续验收还必须完成：所有正式模块统一构建、全声明公理审计、逐条完整类型重验、与锁定版本匹配的 fresh kernel replay，以及最终 verify_paper 成功记录。工具链保持 Lean 4.33.1，mathlib 保持锁定 revision。
