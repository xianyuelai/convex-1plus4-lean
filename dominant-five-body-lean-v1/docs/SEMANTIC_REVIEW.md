# Lean 规格与论文几何语义的独立审核

> **历史快照。** 本文件保留本次研究早期阶段的语义审查与修复记录，正文中“主定理、Hessian 桥、全解捕获尚未完成”等实现状态已经过时。当前 `main_uniform` 的最终语义与实际依赖检查见 `FINAL_MAIN_SEMANTIC_AUDIT.md`；不要把本文件的早期进度判断作为最终工程状态。原稿全文逐项验收仍以总断言清单及最终构建 receipt 为准。

审核日期：2026-10-03。对象为当前 `DominantFiveBody/{Definitions,Specification,Coordinates,Residuals,Coorbital,CoorbitalModel,WeightedHessian,UniformThreshold,Application,ForceBalance,ShapeDimension,Similarity}.lean`。本次只读 Lean 源码，未编辑这些模块；数学源文范围和外部 AF 输入的核验限度见 `SOURCE_AUDIT.md`、`DEPENDENCIES.md`。本文件审核“命题是否仍说原来的数学事情”，不以成功构建替代语义对应，也不把条件框架算作物理主定理的完成。首次发现的两项定义边界已由主代理修复，本审查已重新读取修复后源码与新增质量度量/六维形状空间/相似关系证明。

## 1. 主规格的对应

| 原论文对象 / 量词 | 当前 Lean 位置 | 语义审核结果 |
|---|---|---|
| 五个标签 0–4；主星为 0 | `Definitions.lean:21–27`、`masses` 35–36 | `Label = Fin 5`，卫星 `Fin 4` 经 `.succ` 映射到 1–4；没有去掉主星或把构型替换为抽象根。 |
| 正质量比、归一总和 1 | `PositiveRatio` 31–32；`Coordinates.masses_positive` 21–26 | 每一个卫星质量比均严格正，没有额外的统一正下界。质量确为 `m₀=1`、`mᵢ=ε μᵢ`。 |
| 任意有向壳序 `(0,ℓ₁,…,ℓ₄)` | `HullOrder` 108–110 | 五标签排列固定首位主星；卫星所有排列可表达。壳序是结论全称参数，而不是额外的对称性假设。 |
| 严格凸，主星也在壳上 | `StrictConvexInOrder` 114–116 | 每条正向相邻边要求其余三点都严格在左；`Fin 5` 的 `k+1` 模 5，因此包括末卫星→主星的闭合边。该严格支撑判据对应原稿 (4.4)。尚需形式证明它与通常凸包顶点顺序的表述等价。 |
| 真实 Newton 中心构型 | `potential` 75–76；`acceleration` 85–90；`CentralConfiguration` 93–94 | 势能对十个无序对求和；加速度对所有其他五标签求和；有质心、正乘子及碰撞自由。不是用定义把“中心构型”替换成隐函数图的根。 |
| 原几何构型与乘子一代表 | `CentralConfiguration` 93–94；`NormalizedCentralConfiguration` 97–99 | 两者分开定义，原规格允许平移及任意正乘子；规范代表要求质量加权中心为零、乘子为一。`Coordinates.normalized_is_central` 116 起仅证明一个方向，完整规范化/相似类代表唯一性还未实现。 |
| 模平移、旋转和正尺度，保留反射差别 | `OrientedSimilar` 124–127 | 使用标签不变的平移、`a>0` 与实平面线性等距同构 `R`，并要求 `det R=1`。这是真正 SO(2) 条件；不存在反射或标签重排。反射的 determinant 为 −1，不能凭该定义通过。 |
| 六维真实形状空间 | `shapeSpace` 145–148 | 定义为中心变分核、固定惯量切向核和旋转正交核的交。径向与旋转方向取原构型的质心平移版本。维数 6 没有藏在定义中，而是主非退化结论的一部分。 |
| 真实二阶变分 | `physicalHessian` 152–153 | 确为 `fderiv ℝ (fderiv ℝ (U+λI/2)) x` 的双线性评估，不是给残差 Jacobian 改名。仍须在无碰撞开集上证明 `C²`、导数公式、平移不变性以及原稿 `lem:hessian` 的约束/切片等价。 |
| 共同阈值在所有质量比之前 | `Specification.lean:15–26` | 严格保留 `∃ δ>0, ∀ μ, PositiveRatio μ → ∀ ε, 0<ε → ε<δ → ∀ σ,…`。没有偷换成 `∀ μ, ∃ δ(μ)`，没有把质量域改为内部紧子集。 |
| 恰好一个相似类和全部代表非退化 | `Specification.lean:20–26` | 存在实际严格凸 CC `x`；同一质量和壳序的任意实际 `y` 均与 `x` 正向相似；任意这样的 `y` 均满足几何非退化。不是仅对选中的某条局部分支断言唯一性。 |

**规格层面的判断：** `MainUniformStatement` 没有隐藏图构造、碰撞分类或全局唯一性假设；它是原论文目标的具体几何规格。该声明是 `def … : Prop`，不是定理；文件注释也明确没有 `main_uniform` 证明。

## 2. 两个已修复的定义边界

### 2.1 非退化谓词自身的无碰撞域

首次审核时 `NondegenerateCentralConfiguration` 的独立谓词内没有再写 `CollisionFree x`。修复后的 `Definitions.lean:160–162` 现在明确记录 `CollisionFree x ∧ ∃ lam,…`，同时保留正乘子方程、形状空间维数 6 和真实 Hessian 核为零。

首次版本也**没有削弱主规格**：其使用前件已经包含碰撞自由。修复使该谓词独立使用时也明确排除奇点，消除了域完整性问题。由于 Lean 的除法、`fderiv` 均是全定义，不能依赖名称自动排除奇点；仍需证明无碰撞域上的实际微分公式。这不是发现主定理的反例。

### 2.2 正参数角核不是奇延拓

`Coorbital.lean:21–22` 的 `kernelF` 是原稿在 `0<t<π` 上的公式，注释明确限定了这一用途。负参数上这条裸公式不是原稿的奇延拓：若 `0<t<π`，写 `a=(2 sin(t/2))⁻³`，则

\[
\texttt{kernelF}(-t)=\sin t\,(a+1),\qquad
-\texttt{kernelF}(t)=\sin t\,(1-a).
\]

修复通过新增 `CoorbitalModel.lean` 完成：`coorbitalKernel` 行 22–23 对负参数明确取 `-kernelF(-t)`；`coorbitalKernel_neg` 行 53 起证明它为奇函数；`coorbitalMatrix_reverse` 行 61 起证明实际矩阵反对称。`coorbitalResidual` 行 29–30 现在使用这个有符号核，全部四个探针行都保留；`coorbitalPotential` 行 40–43 使用真实单位圆弦长。角域以首角零、全部严格递增和末角 `<π` 明确排除角碰撞。

原 `Coorbital` 模块的导数和正性定理仍全部带正确正参数条件，没有发现错误的负角应用。`Residuals.angularResidual` 本来就通过真实距离和有符号 `sin` 定义。今后仍须把正参数解析定理转移到负角及实际角势导数；新增定义与反对称性没有自动证明这些导数桥。

## 3. 已证明辅助结果的范围

| 模块 | 已实现的内容 | 仍然缺少的连接 |
|---|---|---|
| `Coordinates` | 正质量、总质量、非零分母、碰撞距离为正、质心平移、主星相对坐标恢复、形状空间成员条件、规范 CC 推出原 CC | 原 CC 到乘子一及旋转规范代表、几何/规范唯一性互相转译。相似等价性质和真实形状维数现由下列新模块完成。 |
| `ShapeDimension` | 原 `shapeSpace` 的真实维数 6；质量内积正定、中心惯量正、径向/旋转质量正交；四个约束的满射由明确平移/径向/旋转原像证明。没有假定 CC、严格凸或 Hessian 非退化。 | 真实 Hessian 的旋转零模、径向 `3I` 与七行 Jacobian 等价仍未完成。 |
| `Similarity` | SO(2) 相似的反身/对称/传递、真实等价关系；正尺度距离缩放及无碰撞保持。 | 中心构型方程、严格凸和约束 Hessian 的相似协变性；规范代表唯一性。 |
| `ForceBalance` | 所有十对力的反对称、质量加权加速度和为零；在**显式无碰撞、中心为零、总质量非零**的条件下，由主星差分方程恢复全部乘子一方程 | `vectorResidual` 与该主星加速度差条件的具体等价、角加权恒等式及极坐标删行恢复。代数反对称可在全定义除法下证明，不代表物理碰撞处的奇力合法；最终物理恢复定理明确排除了碰撞。 |
| `Residuals` | 明确的物理向量、径向、角向、切向残差及质量矩阵定义 | 与中心构型方程的等价、极坐标要求 `rᵢ>0`、加权角恒等式、实际梯度/Hessian、正质量删行恢复；当前只是公式定义，没有偷偷作为已证引理。 |
| `Coorbital` | 正区间上的具体 `v'=-f`、`f'=-κ`、`v''=κ`、`κ'` 负及严格下降、`κ(h)=9/4`、短角区 `κ≥9/4>0`、端点核为零、f 的正/负段与下界、完整标量 b>0 | 有符号核的解析桥、角平衡方程到流环分解、根上的 Hessian 比较、properness、等质量纤维计数与 Theorem 2.2。尤其 **没有证明 κ 在整个 `(0,π)` 为正**；实际 `κ(π)=−7/8`，靠近 π 的 κ 为负。 |
| `CoorbitalModel` | 原文角域、正确奇核、实际矩阵/四行方程、弦长势定义；核为奇、矩阵反对称、全部探针为 Aμ、质量加权角和为零、正质量被删行恢复 | 核/势的实际梯度和完整 Hessian、平衡流分解、properness、AF 种子与所有质量比的根计数。 |
| `WeightedHessian` | 所有权严格正时的求和平方核；固定角切片上的正性；针对具体 κ/b 二次型且带**显式**循环比较假设 `hcycle` 的推论 | 原稿 Lemma 2.1 的根方程→平衡流→短环结构→比较不等式；物理 `D²V` 到该二次型的导数连接。不能把 `hcycle` 称为已证明，也不能将 κ 本身当作处处正权。 |
| `UniformThreshold` | 反例序列与统一阈值的等价；三正界最小值；开闭分支比较；条件捕获下的统一存在、唯一、非退化，以及条件主链拼接 | `FixedParameterLocalExistence`、`LocalContinuationUniqueness`、`ConnectionProperty` 在具体五体问题上的实例；零端点的具体角根；四图构造/捕获；真实 Hessian 非退化；规范根到主规格的几何桥。 |
| `Application` | 以开放正质量单纯形和所有有向壳序构成 `PhysicalParameter`；采用真实物理 root、SO(2) 唯一性及二阶微分非退化；从**显式假设**的三项 uniform fact 或三类反例序列排除拼接主规格 | 三类反例序列的排除本身没有获得证明；它们与三项物理统一结论等价，是待证输入，不能把条件定理称为完整主定理。 |

`UniformThreshold.main_of_chart_facts` 的定理本体保留所有三项假设，输出的是抽象 `root` 的 `∃!`。它目前没有获得具体物理图实例，也没有证明原稿 Proposition 7.1。`CapturedBranches` 只记录 §7 逻辑需要的连续性而非整篇图的光滑性；注释明确这一抽取范围。它没有自动提供任何实例，因而不存在“定义好捕获结构就证明了所有实际物理解都会被捕获”的偷换。

`Application.main_of_no_bad_physical_sequences` 已把**输出**连接到真实 `MainUniformStatement`，但三个类型为 `¬ BadSequence PhysicalExistence/PhysicalUniqueness/PhysicalNondegeneracy` 的输入逐个显式出现在定理参数中，没有已供应的实例、类型类或 axioms。由于 `UniformBelow ↔ ¬BadSequence`，这些是目标物理事实的等价待证形态；这项条件拼接不能作为 §4–§6 已实现的证据。`PhysicalUniqueness` 的结论正确地采用 `OrientedSimilar`，并未对未取旋转商的原构型错误地要求普通等号。

若将来以 `P` 实例化质量参数，需取开放正质量单纯形（或含该条件的类型）；以 `Y` 实例化已经固定旋转的七维物理规范坐标。直接以未取旋转商的 `Configuration` 实例化普通等号唯一性，会因为旋转轨道而说出错误命题。最终还须证明它与 SO(2) 相似类唯一性的桥。

本次读取的模块未发现 `axiom` 声明、`sorry`、`admit` 或 `unsafe` 证明替代；`Coordinates` 中的单词 “axiom” 只出现在说明注释。此项仅为本次读取范围的文本检查，完整内核/依赖公理检查应以构建及 `#print axioms` 审计报告为准。

## 4. 锁定 mathlib 的专用文献检索

`lean-toolchain` 是 `leanprover/lean4:v4.33.1`。manifest 的 mathlib 修订与实际 checkout HEAD 都是

`0df444a360eaa60ab8c11dca51a86af692955474`。

在 `.lake/packages/mathlib/Mathlib` 全源码检索 `Albouy`、`Corbera`、`Moeckel`、`coorbital`、`central configuration` 均无命中。进一步检索 Newtonian、gravitation、中心构型常见声明名称及 relative equilibria，也未发现可调用的相应天体力学实现。`satellite` 的匹配来自 Besicovitch 覆盖理论的度量球卫星族，数学对象不同，不能充当 coorbital 卫星的库定理。

因此，**本次锁定 mathlib 的源码检索没有找到 AF 等质量共轨分类或 CCLM 的实际四卫星物理延拓实现**。这是限定于当前库版本的检索结论，不是声称外界所有 Lean 项目都没有实现。mathlib 包含一般 IFT，不等于 AF、CCLM 的专用天体力学结论已经可导入。AF 的最低计数输入和 CCLM 的固定 `1+3` 背景范围见 `DEPENDENCIES.md`；四卫星局部 Jacobian、碰撞图及共同阈值仍是本稿自身的义务。

## 5. 当前版本可用的正确 IFT API

下列声明均从锁定 checkout 的源码读取；不是根据其他 mathlib 版本猜测 API。

| 模块 / 位置 | 声明 | 正确输入与用途 |
|---|---|---|
| `Analysis/Calculus/ContDiff/RCLike.lean:46–48` | `ContDiffAt.hasStrictFDerivAt'` | `ContDiffAt ℝ n f x`、明确 `HasFDerivAt f f' x`、`n≠0`，推出 `HasStrictFDerivAt f f' x`。普通单点 `HasFDerivAt` 不能直接替代严格导数的 IFT 输入。 |
| 同模块 62–64 | `ContDiffAt.hasStrictFDerivAt` | `Cⁿ` 和 `n≠0` 推出以真实 `fderiv` 为导数的严格可微性。 |
| `Analysis/Calculus/ImplicitFunction/ProdDomain.lean:47–69` | `HasStrictFDerivAt.implicitFunctionDataOfProdDomain` | `f : E₁×E₂→F` 的联合严格导数 `f'u`，以及 `(f'u ∘L ContinuousLinearMap.inr ℝ E₁ E₂).IsInvertible`。第二因子应放待解的形状变量，第一因子放独立参数。 |
| 同模块 89–92 | `HasStrictFDerivAt.implicitFunctionOfProdDomain` | 构造参数到待解变量的局部隐函数；相关空间为完备赋范空间。 |
| 同模块 100–105 | `HasStrictFDerivAt.eventually_apply_eq_iff_implicitFunctionOfProdDomain` | 邻域内 `f v = f u ↔ ψ v.1 = v.2`，给所需的局部根唯一性。尚须 `f u=0` 才是零集图。 |
| 同模块 107–116 | `HasStrictFDerivAt.hasStrictFDerivAt_implicitFunctionOfProdDomain` | 隐函数导数为负的形状偏导逆复合参数偏导。 |
| 同模块 118–133 | `HasStrictFDerivAt.tendsto_implicitFunctionOfProdDomain`、`eventually_apply_implicitFunctionOfProdDomain` | 局部分支的连续性和确实解原方程的邻域声明。 |
| `Analysis/Calculus/ImplicitFunction/Bivariate.lean:36–50` | `implicitFunctionOfBivariate` | 若采用 curried `f : E₁→E₂→F`，需邻域内两项 `HasFDerivAt`、两偏导在基点的连续性、形状偏导 `.IsInvertible`；模块内部构造联合严格导数。 |
| 同模块 64–80 | `eventually_apply_implicitFunctionOfBivariate`、`eventually_apply_eq_iff_implicitFunctionOfBivariate`、`hasStrictFDerivAt_implicitFunctionOfBivariate` | 同样给局部解、局部唯一性和严格导数，不能省掉偏导连续性输入。 |
| `Analysis/Calculus/InverseFunctionTheorem/FDeriv.lean:109–116` | `HasStrictFDerivAt.toOpenPartialHomeomorph` | 导数需以连续线性等价 `E ≃L[ℝ] F` 表示，且源空间完备；用于把增广映射 `(s,y)↦(s,F(y;s))` 变成局部坐标同胚。 |
| 同模块 147、156–186 | `localInverse`、`eventually_left_inverse`、`eventually_right_inverse`、`to_localInverse` | 提供局部逆与正确导数；仍要自行证明本稿增广导数确实可逆。 |

推荐后续采用 `ImplicitFunction.ProdDomain` 接口，对每一个**具体**正规残差证明联合 `ContDiffAt`、真实 Jacobian 与形状偏导可逆，再提升为严格导数并应用 IFT。单点 IFT 的邻域结论还需在参数紧基图上有限覆盖、统一根半径并粘合分支，才能得到本稿 Lemma 3.2 的独立参数产品；当前库的单点接口不能自动提供任意质量比的全局阈值。

## 6. 版本与最终检查绑定

本报告已重读主代理修复后的 `Definitions`，以及新增/扩展的 `CoorbitalModel`、`Application`、`ForceBalance`、`ShapeDimension`、`Similarity`、完整标量 b 与具体加权 κ 形式。不重复保留首次读取时已经过期的模块 hash；源码、编译产物及构建检查的准确版本绑定以交付时统一的构建 receipt 为准。之后如果继续变更源码，应检查本报告对应段落，不能把旧文字自动作为新版本已经审核的证据。

**审核结论：** 几何主规格基本准确，现有辅助证明没有观察到通过定义隐藏主定理前提、加入质量下界或假定 κ 在整个半圆正的做法。非退化谓词碰撞域与角核奇延拓的两项初审意见已修复。力平衡代数和物理方程恢复的适用域明确，没有利用零除法掩盖碰撞奇点。实际证明覆盖仍远低于整篇论文：真实物理图、全解捕获、等质量种子、Hessian 桥和 `MainUniformStatement` 的无条件证明尚未完成。条件物理拼接和阈值框架的内核检验不能认证这些缺失步骤。
