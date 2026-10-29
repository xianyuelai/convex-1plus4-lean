# v1 交付与验证说明

本文件说明 v1 的结论、范围和验收判据。实际结果以当前 `logs/PAPER_ACCEPTANCE.json` 及其绑定文件为准；这里不把旧底本的成功记录复制为新版本结论。

## 版本身份

权威底本是 Kaitai Xiao 的 *Uniqueness of convex central configurations in the planar (1+4)-body problem*，文件为 `source/convex_1plus4.tex` 和 `source/convex_1plus4.pdf`。精确 SHA256、19 页信息和冻结规则见 `VERSION.json`。提供稿的原始字节保留，临时重编译副本存于 `logs/v1-source-build/`。该目录及 `logs/SOURCE_BINDING.json` 保存实际命令、工具身份、页数和整篇文本比较证据。

旧名稿件和旧审计保留作沿革材料。任何旧记录即使含有 `paper_verified=true`，也只能说明其所绑定的旧文件。

## 数学目标

主规格为 `DominantFiveBody.MainUniformStatement`，主定理入口为 `DominantFiveBody.main_uniform`。统一正阈值先于全部正质量比、正小参数和有向凸壳顺序量化；结论包括存在、在同标签平移／SO(2) 旋转／正缩放下唯一，以及真实增广势在六维形状空间上的 Hessian 非退化。

源账本 `docs/FULL_ASSERTIONS.json` 分别记录编号命题、展示公式、正文断言、定义、背景文字和递归源交叉引用。主定理证明不自动关闭原文的独立中间断言；替代证明与原路线的关系由逐项 `proof_route` 或 `proof_route_note` 说明。记录数量和绑定数量取当前生成的 `logs/PAPER_COVERAGE_EXPECTED.json`，不沿用旧稿统计值。

新稿涉及的坐标／Hessian 语义和边界说明，须以当前 Lean 声明和新稿映射为准。例如 `V1BoundaryIdentities.lean` 将离解极坐标投影以及固定外源路径上真正的 `Y-c_eps X` 立方阶写成显式定理。原有 action reaction 的立方阶不能替代该缺陷项。

## 怎样判定本轮已经通过

必须同时满足：

1. `logs/PAPER_ACCEPTANCE.json` 标识 `version=v1`、`paper_verified=true`，且源身份等于 `VERSION.json`。
2. receipt 绑定的源码、权威原文、账本、定义值、覆盖目标、发布说明、脚本和来源记录与当前文件逐字节相符。
3. receipt 内全部检查命令成功，开发验证记录满足所需状态；当前账本没有 OPEN、PARTIAL、CONDITIONAL。
4. `scripts/package_project.py --check` 成功；实际交付 ZIP 的 `DELIVERY.json` 逐文件哈希与压缩包内容一致。

未满足任一项时，只能报告已有的具体检查，不得宣称 v1 整篇验收成功。旧 `logs/VERIFICATION.json`、早期清理构建记录、单模块退出 0 或独立的源文本比较均不够。

## 验证方法与限度

复现入口为 `pwsh -NoProfile -File scripts/verify_paper.ps1 -Clean`。脚本核对 Lean 4.33.1 与锁定依赖，重新构建项目数学模块，回放完整声明类型和定义体，检查实际环境的依赖闭包。允许基础公理为 `Classical.choice`、`propext`、`Quot.sound`；具体观测以本轮日志为准。

`leanchecker --fresh Audit` 与 `--fresh PaperAcceptance` 使用同一 Lean 内核进行 fresh replay，不能称为独立第二内核。自然语言断言与 Lean 命题的对应仍须由源审读建立；类型核验不会自动证明翻译忠实。

来源比较、数学源对应、Lean 内核验收和 ZIP 完整性是不同证据。v1 的完整交付同时保留这些入口，未来 v2 在独立版本中继续。