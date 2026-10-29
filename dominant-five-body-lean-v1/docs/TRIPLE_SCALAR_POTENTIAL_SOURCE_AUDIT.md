# 原标量势路线的独立审计

审计结论：**证明成立**。范围为原 TeX 第 599–604 行的正权重标量势、除质量梯度、properness、严格凸性以及由该势得到的根存在唯一和零加权中心；本结论不代表全文验收。

原势是 `DominantFiveBody.tripleScalarPotential`，包含真实的 `D0/2 * Σ alpha_i z_i²` 和全部三对 `alpha_i alpha_j / |z_i-z_j|`。`tripleScalarPotential_source_formula` 把显式三对与原 `i<j` 有限和严格绑定。区域是全部 `z0<z1<z2`，用 `tripleScalarChamber` 表示。

该开发只在需要处要求每个 `alpha_i>0`，没有假设任何统一正下界。梯度恒等式自身对任意权重成立；除质量及 properness、严格凸性和唯一根要求正权重。证明实际上不需要额外的 sum-one 假设，所以覆盖原稿的正且和为一的权重范围。

严格凸性使用原势本身：正加权二次项满足严格 Jensen 不等式，每个正角间隙倒数满足凸 Jensen 不等式。properness 有实际拓扑声明 `tripleScalarPotential_isProperMap`，其定义域是有序区域子类型。它由所有紧子水平集得到；证明分别给出每一坐标界和每一原配对的正分离界 `alpha_i alpha_j/C`。这些界依赖固定正权重，不被错误推广为闭单纯形上的统一界。

真实 Fréchet 导数由 `tripleScalarPotential_hasFDerivAt` 证明；其值是 `Σ alpha_i * tripleScalarResidual_i * v_i`。在坐标方向除以正 `alpha_i` 得到原方程。`tripleScalarPotential_critical_iff_root` 给出实际临界点与全部原方程的等价。

原势路线的存在唯一也已独立完成。紧子水平集产生区域内极小点，Fermat 定理给出其真实导数为零；沿实际仿射线段的凸函数斜率说明任一临界点都是全局极小点，严格凸性给出唯一性。`tripleScalar_potential_root_existsUnique_centered` 最终返回有序唯一根及零加权中心。它不调用此前的五次多项式根存在定理代替这一路线。

五个源模块为 `TripleScalarPotential.lean`、`TripleScalarPotentialConvex.lean`、`TripleScalarPotentialProper.lean`、`TripleScalarPotentialGradient.lean`、`TripleScalarPotentialMinimizer.lean`。严格编译均通过；最后模块 session 49498，退出码 0。

完整实际类型通过 `info.type` 和 `Meta.ppExpr` 导出，打开 fullNames、proofs、deepTerms、coercions.types、funBinderTypes。输出是 `docs/triple-scalar-potential-types.json`，没有声明名前缀充当类型，也没有省略号。导出审计 session 33833，退出码 0。

`Audit/TripleScalarPotential.lean` 对这 21 个完整类型逐一执行 `example : type := @declaration`，并逐一打印公理。共享锁严格审计 session 88851，退出码 0。稳定日志是 `docs/triple-scalar-potential-complete-axioms-audit.log`；全部只依赖 `propext`、`Classical.choice`、`Quot.sound`。没有 sorry、admit、自定义 axiom、native_decide 或 unsafe 证明替代。

类型 JSON 的 SHA256 是 `D6B575CD7FF46939A4CE5AF468D5E047C556A09A2EAF478F533843B139B7B5E5`；完整类型重验源的 SHA256 是 `5907424D9FA9DCC418BBC699DC3C8E562F4ED6666DC514C0AF8D19FD53DC7317`；最终极小点路线源的 SHA256 是 `C30DF8C179207E9F65EE29164138279DBD4BAD5CD2011F7684A7D5AE6857D991`。

最终全表仍须统一重建所有正式模块、审核全部声明的公理并作版本匹配的 fresh kernel replay。以上独立节点审计不能替代这些全文验收步骤。
