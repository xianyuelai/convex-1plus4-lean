# 原三点支撑秩路线与七坐标代表

日期：2026-10-03。这里只记录 TeX 第 200 行的秩/限制映射子断言和第 947 行的完整坐标代表断言；不把第 200 行整个含扰动、比较下界和极限的段落自动标成已证。

## 三点支撑的原证明路线

`DominantFiveBody/CoorbitalSkewRank.lean` 已严格编译，session `76860`，退出码 0。输入均为真实的质量、角度、唯一零标签 `k`、其余质量严格正、严格有序且各两点角差小于 π，以及全部实际四行共轨方程。

`coorbitalSupportMatrix theta k` 是原实际反对称矩阵 `coorbitalMatrix theta` 在有序正支撑 `k.succAbove : Fin 3 → Fin 4` 上的原子矩阵，没有改用 Hessian 或其它抽象矩阵。

`coorbital_three_source_ranks_and_kernel_dimensions` 同时给出：

```text
rank A_PP = 2
rank A = 2
finrank (ker A) = 2
finrank (ker A_PP) = 1
```

非零二阶支撑主子式的 pivot 来自实际三源平衡根的短角性质。完整四阶矩阵的秩上界由三条实际质量根方程推出

```text
A01*A23 - A02*A13 + A03*A12 = 0,
```

然后逐条验证分解 `A=C D`，其中 `C` 为 4×2，`D` 为 2×4：

```text
C_i0 = A_i0,    C_i1 = A_i1,
D_0j = -A_1j/A_01,    D_1j = A_0j/A_01.
```

因此秩至多 2；非零二阶主子式使秩至少 2。支持块用真实非零质量核向量和三维 rank-nullity 得到秩 2、核维数 1。这一证明没有把第二个核向量或所要求的秩作为输入。

`coorbital_three_source_kernel_not_all_zero_at_missing_source` 明确构造从真实完整核到支撑核的线性限制映射。若所有完整核向量在 `k` 坐标都为零，这个映射是单射，故产生 `2 ≤ 1` 的矛盾。`coorbital_three_source_kernel_vector_by_rank` 再将所得非零 `k` 坐标正规化，得到实际 `nu k=1` 和全部原矩阵核方程，忠实保留原文的秩—限制映射路线。

完整源段的独立局部补丁为 `docs/COORBITAL_SKEW_RANK_COVERAGE_PATCH.json`。它为上述三个原子结论保存完整 Lean 类型，并将整个源段保留 PARTIAL；扰动 positivity 与 cycle-bound 极限由根代理另行绑定。

## 七极坐标的表示唯一性

`DominantFiveBody/OrderedSliceInjectivity.lean` 已严格编译，session `77408`，退出码 0。证明独立于 `main_uniform` 和任何统一小参数阈值。

`ordered_slicePhysicalConfiguration_injective` 对每个正规参数成立，只用正半径与严格有序的第一角零图。相同实际构型的主星相对位置相同；取模恢复全部半径；取第一平面坐标并消去正半径恢复 cos 值；全部角在 `[0,π]`，使用 cos 的实际单射性恢复全部角。因此七坐标相等。

`orderedSliceRoot_unique_coordinates_of_normalized_gauged` 对任意 `ε>0` 的实际规范几何 CC 给出恰好一个七坐标根。`orderedSliceRoot_existsUnique_orientedSimilar` 结合真实乘子规范、定向旋转及几何规范代表唯一性，对任意 `ε>0` 的原全五点严格凸 CC 给出

```text
∃! y, orderedSliceRoot mu eps y ∧
  OrientedSimilar x (slicePhysicalConfiguration (eps,mu.val) y).
```

这完整闭合原文第 947 行，而没有把七坐标的全局小参数根唯一性作为坐标表示唯一性的前提。独立 `SECTIONS_3_7_COVERAGE_PATCH.json` 已将该原文条目改为 VERIFIED；其余未逐项绑定的原推导保留原状态。

## 公理与版本绑定

`Audit/CoorbitalSkewRankAndSlice.lean` 对 13 个声明打印完整类型和公理，严格 session `98431`，退出码 0。日志为 `docs/coorbital-skew-rank-and-slice-axioms-audit.log`；全部声明仅依赖 `propext, Classical.choice, Quot.sound`。

| 文件 | SHA256 |
|---|---|
| 原稿 Desktop TeX | `9B080F2516C79F16B3EE1097A2C853D3FE50C9674C309C5BD7826453A52FB5E2` |
| `DominantFiveBody/CoorbitalSkewRank.lean` | `93BFA6B30CBDE6AC9C151C24781E7B9458AA6DE09AE3729D63C415EEC0700FB5` |
| `DominantFiveBody/OrderedSliceInjectivity.lean` | `849CAB3DF9E1E089A605FD493AD103546B0F66C124DAD2B2D70CD44F1534BAE7` |

该局部审计不是整项目最终构建 receipt，也不独立替代全文断言验收。
