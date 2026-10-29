# v1 全文最终验收的范围

权威源为 `source/convex_1plus4.tex` 和同名 PDF，版本与 SHA256 见 `VERSION.json`。最终入口是：

```powershell
pwsh -NoProfile -File scripts/verify_paper.ps1 -Clean
```

只有当前 `logs/PAPER_ACCEPTANCE.json` 标识 v1、`paper_verified=true`，且绑定的源身份与文件字节均一致，才表示该版本完成整篇验收。这里不预填本轮结果；旧稿及旧记录保留为历史证据。

## 源文与数学

- `MainUniformStatement` 保留统一阈值、全部正质量比、有向顺序、同标签有向相似与真实 Hessian 非退化结论。完整展开检查在 `PaperAcceptance/Main.lean`。
- `docs/FULL_ASSERTIONS.json` 为新权威稿的全文账本；数量以当前 `logs/PAPER_COVERAGE_EXPECTED.json` 为准。旧稿 label、行号、辅助页码或数量不自动适用于本稿。
- VERIFIED 项须有完整实际声明绑定；DEFINITIONAL 项须有真实定义值；CROSS_REFERENCE 须递归闭合。OPEN、PARTIAL、CONDITIONAL 均阻止整篇验收。
- 源对应审读负责原文与形式命题之间的语义。完整类型 elaboration、定义值的 `rfl` 核对和公理依赖检查负责形式侧；它们不自动认证自然语言翻译。
- 取代原文某条推导的证明须在逐项路线说明中标明，原稿独立中间公式仍保留自己的义务。

## 机器检查

1. 核对 Lean/Lake `leanprover/lean4:v4.33.1` 和 `lake-manifest.json` 锁定的九个 Git 依赖 revision；mathlib 为 `0df444a360eaa60ab8c11dca51a86af692955474`。
2. 在现成环境中清理本项目构建产物并重新构建数学模块，复用锁定依赖缓存；编译持共享锁。复现命令不负责安装或更新依赖。
3. 全声明类型和实际 checked environment 依赖审计只允许 `Classical.choice`、`propext`、`Quot.sound`；具体结果以本轮日志为准。
4. 运行分发目录的 `leanchecker --fresh Audit` 和 `--fresh PaperAcceptance`，记录二进制 SHA256、命令及退出码。fresh replay 使用同一 Lean 内核，不是独立第二内核。
5. 比较验收前后的源码、权威原文、账本、定义值、覆盖目标、脚本和发布元数据的 SHA256，并核对生成的 Coverage 与账本／定义的三方绑定。
6. 验收入口的负对照检查只验证拒绝行为，不代替数学证明；其结果及适用源身份应从本轮记录读取。

自动回放完整类型可使用显式实例以消除容器和嵌套绝对值的打印歧义。相关命名类 linter 的设置不会代替或关闭内核／完整类型检查。

## 来源与交付

`logs/SOURCE_BINDING.json` 记录权威副本与提供稿的字节身份、两次隔离 pdfLaTeX 编译，以及 supplied/rebuilt PDF 的页数和整篇 `pdftotext -layout` 文本对照。该证据不宣称 PDF 二进制相等或数学定理成立。

`scripts/package_project.py --check` 只读核验成功 receipt、v1 源身份和当前字节；默认打包还生成 `DELIVERY.json`、`<工程目录名>.zip` 与 `.zip.sha256`，逐文件检查压缩包内容。ZIP 排除 `.lake`、`.git`、运行缓存、临时文件及编译锁，保留锁定配置、源码、文献来源和审计证据。

`.gitattributes` 中 `* -text` 禁止 Git checkout 的自动换行转换。验收按原始字节比较；从压缩包或 Git 取出后均应重新核验。v1 冻结后，后续修改在独立 v2 版本中进行。