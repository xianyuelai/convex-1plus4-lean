# 原论文对象与当前 Lean 对象的映射

> **最初实现阶段的对象映射快照。** 表中“尚无／仍需／当前没有 main_uniform”等进度描述已过时，保留用于追溯定义与证明的区别。当前完整对应与实际声明见 `FULL_ASSERTIONS.json`；主规格及真实几何桥的当前审核见 `FINAL_MAIN_SEMANTIC_AUDIT.md`。

本表以用户提供的 19 页原稿为准。`定义` 表示已准确写出数学对象，不自动表示关于该对象的论文定理已经证明。`实际已核检查引理` 只列当前 Lean 声明的实际结论；版本、成功构建与公理输出绑定到交付时统一 receipt。手工审查的 A 评级不作为本表的 Lean 证明证据。全依赖状态见 [STATUS.md](STATUS.md)。

Lean 命名空间默认是 `DominantFiveBody`；标为 `Coorbital.…` 的声明位于其子命名空间。下表没有引入额外质量下界、等质量或对称性假设。

| 论文对象 / 位置 | 当前 Lean 定义 | 实际已核检查引理 / 真实范围 | 仍需完成的转换或性质 |
|---|---|---|---|
| 五标签，主星 0，卫星 1–4；(1.1) | `Label=Fin 5`、`Satellite=Fin 4`、`Configuration=Label→Plane`；`masses ε μ` | `masses_primary`、`masses_satellite`、`masses_positive`、`totalMass_masses`。最后两个使用原质量条件，不要求统一正下界。 | 从任意未归一质量向 `m₀=1`、总卫星比 ε 的规范化；证明其对几何结论的转译。 |
| 开放正质量单纯形 `M` | `MassRatio`、`PositiveRatio`；`PhysicalParameter={μ // PositiveRatio μ}×HullOrder` | 已将所有正质量参数和所有有向壳序直接放入物理条件拼接；没有将 `M` 替换成内部紧集。 | 各个 IFT 图用局部仿射坐标表述质量参数；零质量边界单纯形、端点份额和图覆盖。 |
| 真正平面、欧氏距离 | `Plane=EuclideanSpace ℝ (Fin 2)`、`point`、`pairDistance`、`CollisionFree` | `collision_distance_pos`、`collision_distance_cube_ne_zero`；`finrank_plane`、`finrank_configuration`。 | 极坐标弦长公式 (4.3)；角域保证弦长非零；无碰撞开集上的势能光滑性。 |
| 总质量、质心、中心坐标 `x`；(3.1) | `totalMass`、`weightedPosition`、`massCenter`、`centered` | `totalMass_pos`、`totalMass_ne_zero`、`weightedPosition_translate`、`centered_weightedPosition_zero`、`centered_collisionFree`、`centered_ne_zero`。 | 中心平移对中心构型方程、实际 Hessian 与相似规范的协变性。 |
| 主星相对坐标 `qᵢ=xᵢ−x₀`、`X`；§3 | `primaryRelative`、`satellitesRelative`、`liftRelative`、`relativeAverage`、`centeredFromRelative` | `primaryRelative_primary`、`relative_distance_eq`、`weightedPosition_liftRelative`、`centered_liftRelative`、`centeredFromRelative_weightedPosition_zero`、`satellitesRelative_centeredFromRelative`。 | `vectorResidual` 与所有主星加速度差方程的精确等价；正质量且 `ε>0` 时与全 (3.1) 等价。 |
| 势能 U、惯量 I、增广势 G；(3.2) | `potential`（五体全部十对）、`inertia`、`augmentedPotential` | `massInner_self_eq_inertia`、`centered_inertia_pos` 确认实际惯量及径向分母；力的加权抵消见下一行。 | 相对势 Φ 的 (3.4) 恒等式；U、G 的真实一阶和二阶 Fréchet 导数；齐次性、Euler 恒等式。 |
| Newton 加速度、完整中心构型；(3.1) | `acceleration`、`MultiplierEquation`、`CentralConfiguration`、`NormalizedCentralConfiguration` | `weighted_acceleration_as_pair_sum`、`weighted_acceleration_zero`；`normalized_of_primary_differences` 在**碰撞自由、中心为零、总质量非零**时恢复全部乘子一方程；`normalized_is_central`。 | 任意原几何 CC 的正乘子唯一性、正尺度乘子一规范化、固定旋转代表，以及代表唯一性。代数抵消在总除法下成立不表示物理碰撞被允许。 |
| 有向壳序和严格凸；(4.4) | `HullOrder`、`orientedArea`、`StrictConvexInOrder`、`StrictConvexCentralConfiguration` | 已明确使用五标签排列、主星首位和每条边其他三点严格在左的真实支撑判据；该对象是定义，不是已证明的几何定理。 | 与凸包顶点顺序的等价；严格凸性的开性；其给出的有向角序和跨度 `<π`；各个图上所有正面积商。 |
| 允许的相似关系，不含反射 | `OrientedSimilar`：平移、正尺度、实平面线性等距同构且 `det=1` | `orientedSimilar_refl`、`orientedSimilar_symm`、`orientedSimilar_trans`、`orientedSimilar_equivalence`；`pairDistance_of_similarity_data`、`collisionFree_of_orientedSimilar`。 | 中心构型方程、严格壳序、真实约束 Hessian 的相似协变性；每相似类恰一乘子一/旋转规范代表。 |
| 质量内积、径向、旋转方向；Lemma 3.1 | `massInner`、`quarterTurn`、`rotationDirection` | `massInner_comm`、`massInner_self_pos`、`massInner_self_eq_zero_iff`；`quarterTurn_inner_self`、`quarterTurn_inner_quarterTurn`、`massInner_rotation_self`、`massInner_rotation_rotation`、`weightedPosition_rotation_eq_zero`。 | 旋转方向是**实际 Hessian** 的零模；径向 `D²G(x)x=3Mx`；相应质量正交分裂与约束 Hessian 商的桥。 |
| 六维形状空间；Lemma 3.1 | 原有几何 `shapeSpace`，仍为中心/惯量/旋转三类线性核的交；辅助 `shapeConstraints` | `mem_shapeSpace_iff`、`ker_shapeConstraints`、`shapeConstraints_surjective`、`finrank_shapeSpace`。最后一项确实证明原有空间的维数为 6，只需正质量和无碰撞；没有假定 CC、严格凸或非退化。 | 该几何切片与固定惯量切空间模旋转的等价；七维极坐标残差切片到六维 shape Hessian 的等价。维数已证不意味着 Hessian 非退化已证。 |
| 真实约束二阶变分和非退化 | `physicalHessian=(fderiv ℝ (fderiv ℝ (U+λI/2)) x) v w`；`ShapeHessianNondegenerate`、`NondegenerateCentralConfiguration` | 非退化谓词明确含 `CollisionFree`；`nondegenerateCentralConfiguration_iff` 证明正质量下六维条款自动成立，其余仍是实际 Hessian 条件。 | 无碰撞域 C²、显式矩阵、旋转核、径向正值、七行 Jacobian 与六维形状 Hessian 的双向等价。当前没有将残差 Jacobian 重新命名为 Hessian。 |
| 极坐标、F、R、T、Q；(3.3)、(3.5)–(3.8) | `polarPoint`、`polarSatellites`、`relativeField`、`vectorResidual`、`radialResidual`、`angularResidual`、`tangentialResidual`、`relativeMassMatrix` | 当前准确的显式公式为定义。物理主星差分的恢复机制由 `ForceBalance` 证明，但尚未与这些具体残差完成等价连接。 | `rᵢ>0` 与分母非零；Φ 的梯度；质量矩阵正定；离根角加权恒等式；删正质量角行后的全方程恢复；旋转切片。 |
| 开半圆有向角域；(2.1) | `CoorbitalAngleDomain` | 首卫星角为零、所有角严格递增、末角 `<π`，属于原域的具体定义。 | 与单位圆五点严格凸壳序的双向几何等价；角差始终在正确非奇区间。 |
| 正角 f、v、κ、κ′；(2.2)、(2.4) | `Coorbital.kernelF`、`pairPotential`、`kappa`、`kappaPrime` | `pairPotential_hasDerivAt`、`kernelF_hasDerivAt`、`pairPotential_second_hasDerivAt`、`kappa_hasDerivAt`；`strictAntiOn_kappa`、`kappa_h`、`kappa_pos_on_short_arc`；正/负角段 f 符号与 `f≥−1`、零点刻画。所有解析结论有明确正角域。 | `tf(t)→∞` 的碰撞渐近；多角 V 的实际梯度与 Hessian；负角分量的导数转换。κ 仅在短角区证正，不是全半圆证正。 |
| 原文奇延拓、矩阵 A、全部探针 E、共轨势 V；(2.3) | `coorbitalKernel`（显式奇延拓）、`coorbitalMatrix`、`coorbitalResidual`、`coorbitalPotential`（实际弦长） | `coorbitalKernel_neg`、`coorbitalMatrix_reverse`、`coorbitalResidual_eq_matrix_sum`、`coorbital_weightedResidual_zero`、`coorbital_recover_positive_mass_row`。最后一项显式要求被删行质量为正，其他行可为零质量探针。 | 正角标量势与实际弦长势相等；`∂ᵢV=μᵢEᵢ`、真实多角 Hessian；根存在、properness、AF 种子与根计数。 |
| Lemma 2.1 的 ℓ、b 和 Hessian 二次型 | `Coorbital.slopeCoefficient`、`positiveRemainder`、`pairForm`、`weightedAngleForm`、`coorbitalKappaForm`、`coorbitalRemainderForm` | `positiveRemainder_pos` 证明全 `0<t<π` 上 `b>0`；`pairForm_eq_zero_iff_constant`、`pairForm_pos_on_rotation_slice`；具体 κ 形式的正性定理保留显式 `hcycle`。 | 由真实角根构造平衡流；正流分解为至多四顶点的简单环；环长比较与 Cauchy；对所有 u 证明 (2.5)。不能用 scalar `b>0` 自动替代循环比较。 |
| 碰撞极限与完全双/三簇、内嵌尺度；§4 | 尚无已实现的簇定义或定理 | 无；一般加权内力取消已可用，但它没有给直径、跨度或尺度界。 | Proposition 4.1–4.4 的全部序列量词、几何支撑、当前质量平均、尺度双边界与四型穷尽分类。 |
| 四图及独立 ε/t/η/份额邻域；§5 | 物理残差已定义；尚无具体正则图 | 无具体图、无图捕获实例。mathlib 一般 IFT 是工具，不是此图实现。 | 光滑约消、边界完整 Jacobian、分母正性、紧参数 IFT、一致根球、行/坐标恢复、实际序列进入根球。 |
| 精确共线和 `t³C₁`、`t³ηC₂`；§6 | `orientedArea` 是真实面积；尚无图根面积系数 | 无。原 TeX 手工公式审查不是形式化证据。 | 等边背景慢特征方向、图的零尺度精确共线、Hadamard 因子、基值正性及共同独立产品上的全部面积正性。 |
| 全解共同区间捕获；Proposition 7.1 | `CapturedBranches`、`ConnectionProperty` 的显式条件结构 | 条件结构的区间限制、实际命中代入和终步逻辑已检查；没有五体实例。 | 由任意**实际物理解序列**证明条件结构非空；固定同质量零端点、真实严格凸与真实非退化；共同半径。 |
| 主定理统一阈值和全局唯一；§7、Theorem 1.1 | `UniformBelow`、`BadSequence`、真实 `PhysicalExistence/Uniqueness/Nondegeneracy`、`MainUniformStatement` | `uniformBelow_iff_no_badSequence`、`uniformBelow_three`、分支开闭论证；`main_of_chart_facts`、`main_of_no_bad_physical_sequences` 均有显式待证输入。 | 解除全部物理输入并实际证明 `MainUniformStatement`。当前没有名为 `main_uniform` 的定理；不能把条件定理或目标 Prop 的定义作为主定理证书。 |

语义审查、外部文献搜索与正确严格导数 IFT API 见 [SEMANTIC_REVIEW.md](SEMANTIC_REVIEW.md)。本项目当前对象定义和辅助证明已可审核，但这张映射不构成完整论文证明。
