# 最终主定理语义与依赖核查

日期：2026-10-03。对象是 `DominantFiveBody.main_uniform` 的最终入口、真实几何规格、实际数学依赖及第 7 节具体接口。此报告取代早期 `SEMANTIC_REVIEW.md` 对当前主链实现状态的描述。

**总体判断：证明成立。** 这一判断限定于以下主定理类型和依赖链，不表示整篇论文每一条辅助公式和中间推导已经逐项验收。

## 原命题与假设图

原稿 `thm:main`（TeX 72–76）要求：存在 `δ₀>0`，对全部严格正且和为 1 的四卫星质量比、全部 `0<ε<δ₀`、全部从主星开始的逆时针五点壳序，恰有一个严格凸中心构型相似类；相似允许平移、旋转、正缩放，排除反射；真实约束 Hessian 在六维形状空间非退化。

`Specification.lean:15` 完整保留量词顺序：

```text
∃ δ>0, ∀ μ, PositiveRatio μ → ∀ ε, 0<ε → ε<δ → ∀ σ : HullOrder,
  ∃ x, StrictConvexCentralConfiguration (masses ε μ) σ x
    ∧ (∀ y, StrictConvexCentralConfiguration ... σ y → OrientedSimilar x y)
    ∧ (∀ y, StrictConvexCentralConfiguration ... σ y → NondegenerateCentralConfiguration ... y).
```

最终类型没有质量坐标下界、预选紧质量集、`ε` 与簇尺度的比较关系、捕获假设、唯一性假设或非退化假设。`PositiveRatio` 是四个坐标严格正且和为 1；`HullOrder` 是全部保持主星首位的标签排列。已打印的最终证明体为 `main_of_orderedSlice_connection orderedSlice_connection`：条件组合引理的最后一个输入由已经证明的实际物理连接声明供应，不留在主定理参数中。

## 严格核查表

评级：A＝当前规格下有完整实际证明与内核证据；B＝文字宜补充；C＝缺少实质推导；D＝使用未给定假设；E＝疑似错误。

| 位置 → 主张 | 依赖 | 评级 | 数学理由与影响 |
|---|---|---|---|
| TeX 72–76 / Specification 15：全部正质量比统一阈值 | `main_of_orderedSlice_uniform` | A | `δ` 在 `μ,ε,σ` 之前量化；重排质量仍在完整正单纯形内，使用同一阈值。 |
| 定理域与存在结论非空泛 | 审计中的 `quarter_ratio_positive`、`main_semantic_positive_parameter_witness` | A | 内核证明四个 `1/4` 在域内；取 `ε=δ/2>0`，主定理给出完整真实五点严格凸 CC。 |
| Definitions 114：主星也是凸壳顶点 | `StrictConvexInOrder`、`orderedSliceRoot_physical`、`CollisionGeometry` | A | 五条有向边均要求其余三点严格在左侧，包含主星。极坐标半圆角序从实际几何推出，没有加到原定理作为额外假设。 |
| Definitions 124：固定标签，排除反射 | `Similarity`、`RotationTransport`、`orientedSimilar_reindex_iff` | A | 正比例、实际平面线性等距同构、行列式 1；结论逐个保持原标签。重标号只是证明中的同时变换并最终撤销。 |
| 原 CC 的乘子一规范与恢复 | `SimilarityNormalization` | A | 原正乘子 `λ` 给出正尺度 `λ^(1/3)` 并证明其三次方为 `λ`，平移至真实质心后缩放；恢复正乘子与全五点凸性。 |
| 七维规范代表与几何唯一性 | `strictConvexCC_existsUnique_normalized_gauged`、`orderedSliceRoot_of_normalized_gauged`、`orderedSlice_uniqueness_to_geometric` | A | 第一卫星规约使用真正的定向旋转；七坐标层证明等号唯一，再组合正相似、逆重排回原构型。 |
| Definitions 145,152：真实形状空间、真实二阶导数 | `PotentialDerivatives`、`ShapeDimension` | A | 真实质量质心约束、定惯量切空间、旋转正交；Hessian 为增广势实际二阶 Fréchet 导数。无碰撞域的光滑性和显式微分公式独立证明，避免全定义 `fderiv` 的空泛问题。 |
| 六维并非写入定义 | `finrank_shapeSpace` | A | 从十维构型空间，用显式平移、径向、旋转原像证明四个约束满射；正质量与无碰撞保证所需惯量为正。 |
| Lemma 3.1：七行 Jacobian 与形状 Hessian | `physicalHessian_comp_at_normalizedCC`、`rotationSliceHessian_nondegenerate_iff_shape`、`reducedJacobian_isInvertible_iff_shape`、`fixedAngleDeletedJacobian_isInvertible_iff_shape` | A | 实际临界点消去坐标曲率项；实际旋转零模及非零径向 `3 massInner` 分离；任意固定角和正质量删行均有具体证明。 |
| Proposition 3.3：固定质量真实局部根 | `coorbital_compact_physical_continuation`、`orderedSlice_fixedParameterLocalExistence` | A | 真正的残差、基图、可逆 Jacobian、共同独立邻域、根半径和逆范数界均已证明；主链用合法单点紧集实例。 |
| Proposition 7.1：每个真实根序列被捕获 | `orderedSlice_collision_subsequence`、四类 capture、`orderedSlice_connection` | A | 分类分离、单对、端点三重簇；后者再分 regular / nested。尺度来自物理方程。上端使用反射运输后精确撤销，不要求预先尺度关系或内层份额极限。 |
| Proposition 7.1：同一当前质量、共同区间、光滑零端点 | `SmoothCapturedBranches`、`orderedSlice_smooth_connection_explicit` | A | 质量为 `p(phi n)`，命中原 `y(phi n)`，正半径独立于 `n`；零端点为该当前质量的共轨点。连续实际根及零处/正点处实际 IFT 给出含零的 C∞。 |
| TeX 970–973：统一存在性 | `uniform_existence_of_connection` | A | 在坏参数下先取 `sₙ=min(εₙ,ℓ(pₙ))/2` 的真实局部根。由支配估计趋于零，捕获区间最终包含坏参数，得到矛盾；没有对空纤维应用捕获。 |
| TeX 975–984：统一唯一性 | `uniform_uniqueness_of_connection`、`branches_eq_on_connectionInterval`、`orderedSlice_localContinuationUniqueness` | A | 两次捕获保持同一进一步子序列的当前质量；共同区间内端点相等，实际局部唯一性使等值集开闭，连接性给出全区间相等。未从单点 IFT 直接跳到全局唯一性。 |
| TeX 986–991：统一非退化与原构型恢复 | `uniform_nondegeneracy_of_connection`、`main_of_chart_facts`、`orderedSlice_nondegeneracy_to_geometric` | A | 退化反例序列被捕获后违反分支实际非退化；三正阈值取最小；撤销尺度、旋转、质量/位置排列后恢复实际 Hessian、正乘子与维数 6。 |

未发现 C/D/E 问题，因此没有因实质缺口而必须降级的下游主结论。

## 最严重的问题与范围边界

本次没有发现主定理链中的实质数学缺陷。需保持清楚的三项范围边界为：

1. 主定理闭合不等于全文逐项验收。被等价证法绕开的原稿精确矩阵、行列式、面积因子仍需独立源断言绑定；不能因为 Main 通过而批量关闭全文 OPEN。
2. 本次严格入口检查读取已有依赖产物，不单独代表完整项目每个松散文件、最终构建及独立 kernel checker 的统一 receipt。
3. 旧 `SEMANTIC_REVIEW.md` 是历史快照，关于尚未实现捕获/主定理的描述已被本报告取代。

内部反射是上端三重簇的证明运输：`captured_mirrorOrderedSlice_undo` 恢复原质量与原坐标，最终相似谓词仍排除反射。

## 内核、公理和版本证据

最终 Main 已导入 `SmoothOrderedSliceConnection`。本次严格编译：

```powershell
lake env lean -DwarningAsError=true -o .lake/build/lib/lean/Audit/FinalMainSemantic.olean Audit/FinalMainSemantic.lean
```

`LEAN_NUM_THREADS=2`；session `43601`；退出码 **0**。日志：`docs/final-main-semantic-axioms-audit.log`。打印最终主定理类型/证明体，并审计主入口、实际连接、光滑连接、任意固定/删行 Hessian 等价、实际共轨紧延拓、固定质量存在、实际局部唯一性、几何恢复、六维、二阶链式法则和真实正参数见证。全部打印声明仅依赖 `propext, Classical.choice, Quot.sound`，未出现 `sorryAx` 或自定义分析/天体力学公理。

Lean 为 `leanprover/lean4:v4.33.1`；manifest 和实际 mathlib HEAD 均为 `0df444a360eaa60ab8c11dca51a86af692955474`。本次未更新或重建依赖。

以下 SHA256 在该严格入口审计后取得；后续修改需更新绑定。

| 文件 | SHA256 |
|---|---|
| Desktop 原稿 TeX | `9B080F2516C79F16B3EE1097A2C853D3FE50C9674C309C5BD7826453A52FB5E2` |
| `DominantFiveBody/Main.lean` | `E7076FFA3B666BF63592F6F8EA1F44471635C1CA1830372A19401156D24D3D83` |
| `DominantFiveBody/Specification.lean` | `D8E6EB70133A4A4582DD7EBE3AFE59C366FC85930354C10BE977F4E89E073295` |
| `DominantFiveBody/Definitions.lean` | `72D4BA0EF7DA1F64B36FA6B7C64C7F24A7EC06717AD105C2B42BC48A8FA075F1` |
| `DominantFiveBody/SmoothOrderedSliceConnection.lean` | `03AFE3522C52AA5511334264D6EA37A25AF133DDE489481EF195DF284CD081F9` |
| `Audit/FinalMainSemantic.lean` | `A74E7471B3863AD7492769CE109D3E6D361535E7CCE581627DF922C20DE2D0B3` |

后续检查位置：`docs/SECTIONS_3_7_COVERAGE_PATCH.md` 的原文逐项对应，以及总清单中的图内部精确公式。此独立补丁不修改源代理维护的 `FULL_ASSERTIONS`，不把主定理审计等同于全文验证。

后续源步骤补充：`CoorbitalSkewRank` 已独立闭合原三点支撑的秩与核维数、限制映射矛盾及正零标签核向量路线；`OrderedSliceInjectivity` 已独立证明任意正参数下原相似类恰好一个七坐标代表，未使用主统一阈值。两模块分别 strict `76860`、`77408`；13 项类型/公理 strict 审计 `98431` 退出码 0，仍仅三标准公理。详细原式对应与 SHA256 见 `docs/SKEW_RANK_AND_REPRESENTATIVES.md`。这些补充不改变以上 Main 类型、证明体或其版本 hash。
