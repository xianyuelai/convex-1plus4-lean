# Proof Package · v1

## Claim

本版本的目标为权威稿 `source/convex_1plus4.tex` 的主定理及其完整实质数学断言。统一阈值主规格是 `DominantFiveBody.MainUniformStatement`，证明入口是 `DominantFiveBody.main_uniform`。源文件身份由 `VERSION.json` 固定。

## Status

数学证明的实际声明、类型和依赖以 Lean 源码为准；v1 是否通过完整机器验收由当前 `logs/PAPER_ACCEPTANCE.json` 和相符的文件哈希判定。本文件不把历史验收、局部编译或账本状态写成新版本的成功凭证。

## Assumptions

主规格保留四个正卫星质量比之和为一、总卫星质量参数为正且小于统一阈值，以及给定有向凸壳顺序。阈值在所有这些参数之前量化。主定理不加入质量比下界或碰撞尺度与质量参数的耦合假设。

局部、边界和条件性辅助定理只在其完整类型所列条件下使用。正半径、无碰撞、非零参数、凸壳方向等条件不得从辅助计算中省略。新增边界缺陷阶数定理采用固定外源和非零聚团中心，不预设试探路径已是中心构型解。

## Notation

中心坐标为 $x$，主星相对坐标为 $q$；新稿分别用 $(r,\theta)$ 与 $(\rho,\varphi)$ 表示其极坐标。$X=\sum_i\mu_iq_i$，$Y=\sum_i\mu_iq_i/|q_i|^3$，$c_\varepsilon=(1+\varepsilon)^{-1}$。数学对象实际定义见 `DominantFiveBody/Definitions.lean`、`Residuals.lean` 和 `RelativeAction.lean`。

## Proof Strategy

先处理共轨极限的 Hessian 与全局唯一性，再分类可能的碰撞极限，构造独立参数上的正则图并控制有向面积。固定当前质量的零端点与实际序列捕获把有限参数解接到唯一共轨端点，最后通过紧性反证取得共同阈值。局部隐函数定理只负责局部延拓；全体解的捕获、连接及全局唯一性各有独立义务。

## Dependency Map

1. 共轨部分：核函数计算、循环比较、根方程及其角 Hessian。
2. 物理等价：中心／相对坐标、action、极坐标残差与真实 Hessian 的桥。
3. 碰撞部分：实际解的分组、尺度界、矩形／差商估计及分类穷尽。
4. 正则图：pair、regular triple、nested triple 和无碰撞图；延拓、Jacobian、面积与参数独立性。
5. 连接部分：同质量零端点、全体坏序列捕获与局部唯一性的拼接。
6. 最终入口：`OrderedSliceConnection.lean`、`OrderedSliceApplication.lean`、`Main.lean`。
7. 全文源义务：`docs/FULL_ASSERTIONS.json` 的逐项绑定；不由主链自动推出。

## Proof

证明体保存在上述模块，逐条源义务保存在账本。完整类型通过 `PaperAcceptance/Main.lean` 与生成的 `PaperAcceptance/Coverage.lean` 回放。新增边界桥显式区分离解恒等式和解上恒等式，并在固定外源的实际图路径上证明 $Y-c_\varepsilon X=O(t^3)$；不以 $\varepsilon c_\varepsilon(X-q_p)=O(t^3)$ 代替。

完整复现使用 `scripts/verify_paper.ps1 -Clean`，不安装或更新依赖。实际观察到的公理、命令退出码和 fresh replay 结果应从本轮 receipt 和日志读取。

## Corrections or Missing Assumptions

本说明不授权增加主定理假设或修改权威稿。若源对应中出现未闭合断言，必须在账本中保留 OPEN、PARTIAL 或 CONDITIONAL，并使整篇验收失败；不得用说明文件或历史记录关闭它。

## Open Risks

语义对应须人工审读；Lean 只检查被提交的形式命题。源码、文档或脚本在验收后改变会使 receipt 失效。fresh replay 仍使用同一 Lean 内核。源 PDF 的文本一致性、形式证明和压缩包完整性分别核验。