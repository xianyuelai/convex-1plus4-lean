# 第 7 节的条件形式化与未解除接口

> **早期条件框架快照。** 本页解释条件定理的字段与责任。当前这些字段已由实际五体结果实例化，`main_uniform` 已有无条件证明；本页的“未提供五体实例”仅描述最初阶段。当前实例和完整语义检查见 `FINAL_MAIN_SEMANTIC_AUDIT.md`，最终验收见 `logs/PAPER_ACCEPTANCE.json`。

本文件对应所提供原稿的 `sec:global`、`prop:connection` 和 `thm:main`。形式化模块是 `DominantFiveBody/UniformThreshold.lean`。

**当前已经闭合的是第 7 节的抽象连接论证，不是五体主定理。** `main_of_chart_facts` 的三个条件参数都有实际证明责任。当前未提供五体实例，不能据此声称原文 Theorem 1.1 已完成形式化。`root` 和 `nondegenerate` 是本抽象模块的显式参数；应用时必须采用真实中心构型方程和真实约束 Hessian 谓词，不能用这些接口替换核心几何定义。

## 量词与参数类型

```lean
def UniformBelow {P : Type u} (good : P → ℝ → Prop) : Prop :=
  ∃ δ : ℝ, 0 < δ ∧ ∀ p ε, 0 < ε → ε < δ → good p ε
```

`P` 完全任意。原问题的应用可以取 `P = { μ : MassRatio // PositiveRatio μ }`。该子类型是完整正质量开单纯形，允许各个 `μᵢ` 沿序列趋零；模块中没有质量比统一正下界、紧内子集、等质量或对称性假设。标准顺序的条件定理先使用这个 `P`；其他有向顺序还需证明同步重标号及相似类转换，或取 `P` 为正质量参数与有向顺序的积并为其实现全部接口。

因此输出的类型严格为：

```lean
∃ δ : ℝ, 0 < δ ∧ ∀ p ε, 0 < ε → ε < δ →
  (∃! y, root p ε y) ∧
  (∀ y, root p ε y → nondegenerate p ε y)
```

这是规范化代表的唯一性；代表与允许的平移、旋转、正比例缩放相似类之间的等价，仍须另行证明。反射和标签置换不能包含在原定理的相似等价关系中。

## 已通过 Lean 内核检查的链

| Lean 声明 | 数学内容 | 对应原文 |
|---|---|---|
| `badSequence_of_not_uniformBelow` | 没有共同正阈值，则选择 `0 < εₙ < 1/(n+1)` 的坏参数序列，并用夹逼证明 `εₙ → 0` | §7 三次反证 |
| `not_badSequence_of_uniformBelow` | 共同正阈值排除全部趋零坏序列 | §7 三次反证 |
| `uniformBelow_iff_no_badSequence` | 上述两方向组成严格等价 | §7 三次反证 |
| `uniformBelow_three` | 三个正阈值取 `min δ₁ (min δ₂ δ₃)`；逐项证明正性和限制不等式 | `thm:main` 最后一段 |
| `isOpen_branch_eq_of_localUniqueness` | 两连续分支在同一根的局部唯一邻域内相等，因此相等集合开 | §7 唯一性段 |
| `branches_eq_of_localUniqueness` | Hausdorff 目标中的连续分支相等集合闭，结合开性、非空和连通性得到全等 | §7 唯一性段 |
| `branches_eq_on_connectionInterval` | 上述定理专门应用于半开区间 `[0, τ)`，包括零端点 | §7 唯一性段 |
| `CapturedBranches.continuous_restrict` | 共同区间限制后仍连续 | 两次子列捕获 |
| `CapturedBranches.continuationRoot` | 捕获分支在零端点和每个正参数满足所声明的继续关系 | `prop:connection` 及端点识别 |
| `uniform_existence_of_connection` | 先在更小参数处取实际辅助根，再捕获到共同区间、到达原无解参数 | §7 存在性段 |
| `uniform_uniqueness_of_connection` | 两次抽子列，共同区间有限最小，固定质量端点相同，开闭论证排除两个不同根 | §7 唯一性段 |
| `uniform_nondegeneracy_of_connection` | 捕获分支的非退化性与命中原解等式排除退化解序列 | §7 非退化性段 |
| `main_of_chart_facts` | 上述三条**条件**链组装成统一的存在唯一与非退化 | `thm:main` 的条件组装 |

### 存在性没有向空纤维应用捕获

假设坏参数 `(pₙ, εₙ)` 的根集为空。从固定参数局部存在得到 `ℓ(pₙ) > 0`，然后使用

\[
s_n=\tfrac12\min\{\varepsilon_n,\ell(p_n)\}.
\]

Lean 证明 `0 < sₙ < εₙ`、`sₙ < ℓ(pₙ)` 和 `sₙ → 0`；最后一项直接由 `εₙ → 0` 夹逼得到。因此不需要原文另列的 `1/n` 辅助上界。对 `sₙ` 处的**实际局部根**调用捕获，获得共同 `radius > 0`。原坏参数沿严格递增子序列仍趋零，故最终位于这个区间，分支在 `εₙ` 给出根。这与空纤维矛盾。

### 两次子列与开闭区间

唯一性证明先捕获第一条坏根序列，子序列为 `c₁.subseq`；再对沿该子序列的第二条根序列捕获，子序列为 `c₂.subseq`。最终原序列指标为 `c₁.subseq (c₂.subseq n)`。两条分支分别为 `c₁.branch (c₂.subseq n)` 和 `c₂.branch n`；共同区间是

\[
[0,\tau),\qquad \tau=\min\{c_1.\mathrm{radius},c_2.\mathrm{radius}\}>0.
\]

两个端点都是 `endpoint (p (c₁.subseq (c₂.subseq n)))`，保存同一个**每步当前固定质量**。`LocalRootUniqueness` 给出的根邻域，加上分支连续性，使相等集合开；Hausdorff 性使其闭。`[0, τ)` 的连通性以及零处相等推出整区间相等。没有用“有限纤维恰好有相同基数”替代开闭连接论证。

## 真实局部分析已经实现的部分

`PotentialDerivatives.lean` 对原始 Newtonian 势能、惯量和增广势能实际求一阶及二阶 Fréchet 导数，并证明真实归一化中心构型是其临界点。`ShapeDimension.lean` 在正质量、无碰撞下证明原始形状空间恰为六维。

`HessianCorrespondence.lean` 已证明原始物理 Hessian 的径向和旋转恒等式，七维质量正交旋转切片与六维形状 Hessian 的非退化等价，并将七维切片 Hessian 的真实核条件等价转为连续线性算子 `IsInvertible`。

`LocalContinuation.lean` 现在已经证明以下真实方程结论，而非抽象接口字段：

- 独立 ambient 参数 `(ε, μ)` 中实际七个显式除质量残差的联合光滑性，以及其真实 `fderiv` Jacobian 的参数隐函数定理。
- 一个基点上的独立 ε 邻域、质量邻域和固定根球；没有 `ε=o(t)` 等关系。
- ε=0、四个单位半径处，上方块真实求导得到 `3I₄`，角向列为零。
- ε=0、单位半径时角向物理残差与奇延拓共轨方程的逐项及邻域等式；角向实际导数与 `BoundaryJacobian.lean` 的已证明导数相等。
- 正质量共轨根的实际角向块可逆，进而实际七方程 Jacobian 可逆。`coorbital_root_local_continuation` 仅以正质量比、共轨角域、单位半径和真正共轨根为输入，给出真实七方程的光滑局部唯一分支；没有假设 Hessian 或 Jacobian 可逆。
- 固定首角后的真实作用量 `sliceAction` 满足一阶导数 `DΦ = B·F`，以及真正的嵌套二阶导数 `D²Φ = B ∘ DF`；`B` 的四个径向因子为 `μᵢ`，三个角向因子为 `εμᵢ`。在正 ε、正质量下，坐标向量检验与有限维对偶证明 `B` 可逆，因此实际切片作用量 Hessian 可逆恰等价于实际七方程 Jacobian 可逆。
- 固定首角坐标切片通过实际极坐标微分及主点相对坐标线性同构，等价于原始质心变分空间中一个真正横截旋转的超平面；横截泛函在旋转方向上的值逐项算得为首卫星相对半径的平方。
- 真实作用量是原始物理增广势能复合该坐标映射后乘 `ε⁻¹`；在实际残差根处恢复真正归一化中心构型，使用二阶链式法则消去真实临界梯度项，得到真实物理 Hessian 的拉回。
- `reducedJacobian_isInvertible_iff_shape` 完成原稿 Lemma 3.1：在实际正 ε、正质量、正则残差根处，真实七方程 Jacobian 可逆恰等价于原始六维形状 Hessian 非退化；坐标转换、物理方程恢复和 Hessian 对应均已证明。
- `reducedResidual_local_product_regular_invertible` 在独立 ε 与质量邻域中保持真实无碰撞正则性及 Jacobian 可逆性，来自实际 Jacobian 的连续性和非零行列式的开性。

`CompactContinuation.lean` 的 `reducedResidual_compact_product` 现在也已完成实际紧图统一：任意紧的实际正则可逆根集合得到共同参数半径、共同根球和真正 Jacobian 逆算子范数界。返回分支在整个开参数球中光滑；粘合由每点实际 IFT 与共同根球唯一性证明。`reducedResidual_compact_product_preserving` 同时保持基紧图上的任意实际几何邻域。质量与 ε 的产品距离为最大距离，因此给出独立参数产品，没有参数大小关系。

`CompactImplicit.lean` 的 `CompactImplicit.compact_product` 为原稿 Lemma 3.2 的通用版本：实际光滑方程 `F` 定义在开域中，未知量为任意 `Fin n → ℝ`，参数为实 Banach 空间，基输入为紧的实际根图及其实际偏导可逆性。共同半径、逆界及光滑粘合均由证明得到，可供各个碰撞正则图使用。

这些结果尚不解除整个五体实例。共轨全局存在唯一、实际基点严格凸性、紧图独立参数继续及固定质量局部存在已由 CoorbitalCovering、ConvexContinuation、CoorbitalContinuation 和 PhysicalHullRelabeling 完成；仍需全部碰撞尺度图及其实际捕获、全局分类与最终接口实例化。ε=0 时角向行因子为零，所以作用量 Hessian 与除质量 Jacobian 的正 ε 等价不能直接套到 ε=0；该基点的可逆性是上面独立的三角块证明。

## 条件接口的字段与来源

### `FixedParameterLocalExistence root`

```lean
∀ p, ∃ ℓ : ℝ, 0 < ℓ ∧
  ∀ ε, 0 < ε → ε < ℓ → ∃ y, root p ε y
```

来源是 Proposition 3.3 (`prop:local`) 的固定正质量比局部存在。**整个物理固定参数实例已实现。** `PhysicalHullRelabeling.physical_fixed_parameter_local_existence` 对完整正质量单纯形和所有原始有向 hull order 证明实际严格凸中心构型局部存在，消费已经闭合的共轨全局根、实际残差 IFT、严格凸性和真实物理恢复。这里保留 `ℓ(p)` 对参数的依赖；统一性由捕获的反证链证明。

### `CapturedBranches root nondegenerate endpoint p ε y`

| 字段 | 精确用途与证明责任 | 来源 | 五体实例状态 |
|---|---|---|---|
| `subseq : ℕ → ℕ` | 抽取原实际解序列的子列 | `prop:connection` | 未实现 |
| `subseq_strictMono` | 保证抽取为真实子列、保留趋零性 | `prop:connection` | 未实现 |
| `radius`、`radius_pos` | 一次抽取后的连接区间对**全部指标统一** | `prop:connection`、`prop:chart-interface` | 未实现 |
| `parameters_lt_radius` | 每个选出的原解参数在同一个共同区间内，保证原文的分支命中有定义 | `prop:connection` | 未实现 |
| `branch : ℕ → ℝ → Y` | 参数固定质量继续分支；区间外值不参与任何结论 | `prop:connection` | 未实现 |
| `continuous` | 分支在 `[0, radius)` 上连续；原文光滑性足够 | `prop:connection` | 未实现 |
| `hits` | `branch n (ε (subseq n)) = y (subseq n)`，实际命中原解 | 图的捕获性质 | 未实现 |
| `roots` | 每个 `0 < s < radius` 的分支值是真实严格凸规范化根 | `prop:chart-interface` | 未实现 |
| `nondegenerate_at` | 每个正参数分支值的真实六维约束 Hessian 非退化 | 图 Jacobian、Lemma 3.1 | 未实现 |
| `endpoints` | 零端点等于同一正质量参数的唯一共轨根 `endpoint` | `prop:connection` 加 Theorem 2.2 的端点识别 | 未实现 |

`hits` 本身没有替代物理方程；证明只有在所用参数严格落入共同正区间时才调用 `roots` 和 `nondegenerate_at`。坏参数趋零保证最终有这样的指标。接口的 `endpoints` 包含原稿 Proposition 7.1 后、主定理证明首段的 Theorem 2.2 端点识别，因此强于仅声称“某个共轨根”的原始捕获命题。该合并必须由真正的共轨唯一性证明解除，不能暗中当成已证明事实。

### `ConnectionProperty root nondegenerate endpoint`

```lean
∀ (p : ℕ → P) (ε : ℕ → ℝ) (y : ℕ → Y),
  (∀ n, 0 < ε n) → Tendsto ε atTop (𝓝 0) →
  (∀ n, root (p n) (ε n) (y n)) →
  Nonempty (CapturedBranches root nondegenerate endpoint p ε y)
```

这保留了对**任意实际解序列**的要求。实现仍依赖 Proposition 4.1、完整二重簇／完整三重簇／嵌套尺度分类、四类正则图的实际捕获、独立参数邻域、严格凸面积因子、固定正质量零端点，以及非退化 Hessian 桥。**未实现五体实例。**

### `LocalRootUniqueness root`

局部形式不是直接假设“分支相等集合开”：对每个实际根给出目标邻域 `V ∈ 𝓝 y`，以及参数邻域中的唯一根性质：两个落在 `V` 内的同参数根相等。Lean 使用连续性将两个分支同时放入 `V`，实际证明开性。

### `LocalContinuationUniqueness root nondegenerate endpoint`

对于每个固定质量参数和每个正共同半径，它要求上述邻域形式的局部唯一，应用到继续关系：

```lean
ContinuationRoot root nondegenerate endpoint p ε y :=
  (ε = 0 ∧ y = endpoint p) ∨
  (0 < ε ∧ root p ε y ∧ nondegenerate p ε y)
```

`ContinuationRoot` 只组织分支比较，并未重新定义“中心构型”或“非退化”。零参数处需要 Proposition 3.3 的局部唯一及 Theorem 2.2 的端点识别；正参数处需要 Lemma 3.1 对真实七维残差 Jacobian 与真实六维 Hessian 的等价，以及 mathlib IFT 所需的严格可微性／连续线性同构条件。**未实现五体实例。**

## 构建与审计

本模块在锁定 Lean `4.33.1` 与 mathlib `0df444a360eaa60ab8c11dca51a86af692955474` 下实际运行：

```powershell
$env:PATH = 'C:\Users\衔月\.cache\codex-runtimes\codex-primary-runtime\dependencies\native\git\cmd;' + $env:PATH
$env:LEAN_NUM_THREADS = '2'
lake env lean DominantFiveBody/UniformThreshold.lean
```

最终该命令退出 `0`，没有警告。文件没有 `sorry`、`admit`、全局数学公理或 `native_decide`。项目专门审计模块还应记录下列声明的完整类型、正文与 `#print axioms`：

```lean
#check @DominantFiveBody.main_of_chart_facts
#print DominantFiveBody.main_of_chart_facts
#print axioms DominantFiveBody.main_of_chart_facts
#print axioms DominantFiveBody.uniformBelow_iff_no_badSequence
#print axioms DominantFiveBody.branches_eq_on_connectionInterval
```

这些检查确认的是已编写的**条件定理**及其逻辑链。它们不能解除以上未实现的数学接口，也不能将条件定理升级为无额外研究假设的 `main_uniform`。

## 2026-10-03 的实际几何连接补充

以下声明均实际使用物理定义和实际函数导数，且各模块通过
`lake env lean -DwarningAsError=true -o ...` 检查。单模块输出保留共享 mathlib 依赖，未运行 `lake update`。

| 模块／声明 | 已证明的精确范围 |
|---|---|
| `FixedAngleRows.fixedAngleDeletedJacobian_isInvertible_iff_shape` | 任意实际固定角和实际删去角向行；质量及物理配置的标签运输均显式证明，结论是原始配置的 shape Hessian |
| `PairHessian.pairChartJacobian_isInvertible_iff_shape` | 正 ε、正 t、正质量与实际正半径／正则根处，配对图真实 Jacobian 与原始六维 Hessian 非退化等价；七维坐标／行变换及双逆均明确，无 ε/t 关系 |
| `NoCollisionContinuation.noCollision_physical_local_continuation` | 闭质量单纯形上的实际分离极限根，正锚定质量，其余质量可零；独立参数分支、凸性、真实逆界、正参数原始 Hessian 与固定当前正质量的共轨零端点 |
| `NoCollisionContinuation.noCollision_actual_sequence_capture_of_regular_limit` | 实际残差根序列收敛到一个真实正则分离极限时，由连续性推出极限残差零，再推出单位半径和完整共轨方程，获得整尾段的共同区间捕获；每步 current mass 保持固定 |
| `NoCollisionCapturedBranches.endpoint_eq` | 零端点等于当前质量与排序置换决定的显式 `labelledCoorbitalEndpointSlice`；原始标签和固定角零保持一致 |
| `SimilarityNormalization.physicalHessian_positiveAffineConfiguration` | 原始真实嵌套二阶导数在平移／正尺度 a 下满足 Newtonian a⁻³ 因子，乘子相应除以 a³ |
| `RotationTransport.shapeHessianNondegenerate_rotateConfiguration_iff` | 实际 SO(2) 旋转同时运输方程、凸性、shapeSpace 与真实物理 Hessian；没有把标签置换加入相似 |
| `RotationTransport.strictConvexCC_existsUnique_normalized_gauged` | 每个原始严格凸 CC 的有向相似类中，存在唯一的质心零、乘子一、首卫星相对向量位于正横轴的规范代表 |
| `RotationTransport.geometric_oriented_uniqueness_of_gauged_normalized` | 实际正轴规范代表的 literal 唯一性推出原始有向相似类唯一性 |
| `RotationTransport.geometric_nondegeneracy_of_gauged_normalized` | 正轴规范代表的原始 shape Hessian 非退化推出任意原几何配置的 `NondegenerateCentralConfiguration`，包括真实六维维数 |
| `PhysicalHullRelabeling.normalized_physical_local_existence_all_orders` | 任意固定正质量与任意原始 hull order 的实际局部存在、严格凸性与原始 shape Hessian 非退化；同时运输质量／标签，再拉回原始标签 |
| `PhysicalHullRelabeling.physical_fixed_parameter_local_existence` | 无额外研究假设地解除 `FixedParameterLocalExistence PhysicalRoot` |

这里的无碰撞序列捕获要求“该实际根序列收敛到真实正则分离极限”。证明已从真实序列推出单位半径及共轨根条件，因此它不是基点根／Jacobian oracle。尚须由全局紧性和碰撞分类把任意原物理解序列归入无碰撞或其它完整正则图，之后才可解除整个 `ConnectionProperty`。局部已证明声明不能替代这一全局分类义务。

