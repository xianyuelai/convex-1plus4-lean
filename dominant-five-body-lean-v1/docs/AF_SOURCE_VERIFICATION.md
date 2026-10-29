# Albouy–Fu 实际引用命题的原文核对

核对对象为 Alain Albouy、Yanning Fu，*Relative equilibria of four identical satellites* 的完整 arXiv 源码 **0902.3215v1**。原稿书目给出 Proc. R. Soc. A 465 (2009), 2633–2645，DOI `10.1098/rspa.2009.0115`。本记录实际读取的是固定 arXiv 版本正文，不声称另行比对了期刊排印版。

已有完整源包位于 `paper-reading/albouy-fu-four-identical-satellites-arxiv-0902.3215v1/`；`source-manifest.json` 记录从 `https://arxiv.org/e-print/0902.3215v1` 于 2026-10-03 16:38:01 +08:00 下载并以 tar 解包。包中有完整 TeX 及两幅 EPS，不只保存摘要。既有 `proof-tree-notes.tex` 已记录主定理、证明树和本项目所需的较小种子。本轮又实际重读了原 TeX 的引言、主定理和角方程。

## 原文陈述与严格范围

`source/AlbouyFu_FourSatellites2.tex:93–105` 把研究对象明确为**非合并、平面、等质量**的 `1+4` 极限中心构型。原文主定理在第 139–144 行写道：

> There are exactly 3 relative equilibria of 4 separate identical satellites.

随后列出四个连续圆周角间隙：

\[
E_1=(\pi/3,2\pi/3,2\pi/3,\pi/3),\quad
E_2=(a,b,a,c),\quad
E_3=(\pi/2,\pi/2,\pi/2,\pi/2),
\]

其中 `2a+b+c=2π` 且 `0<b<a<π<c`。这不是对任意正卫星质量的唯一性定理，也不是对有限正 `m/M` 的统一五体结论；本稿只需要该等质量分类中的开放半圆种子。

四个不同圆周点落在一个开放半圆，当且仅当有一个连续圆周间隙严格大于 `π`。前三类中只有 `E_2` 满足这一条件。对 `E_2`，大间隙 `c` 唯一；其余三个占用间隙是 `(a,b,a)`，且 `2a+b=2π-c<π`。从大间隙后的第一个卫星开始沿逆时针方向排序，并把其角度旋转到零，得到本稿的唯一角域代表：

\[
(\theta_1,\theta_2,\theta_3,\theta_4)=(0,a,a+b,2a+b),
\qquad 0<\theta_2<\theta_3<\theta_4<\pi.
\]

因此 AF 的非标号形状计数在该固定有向角域中给出一根；不能只把“模反射一类”直接当成有向纤维一点。这里额外用到了 AF 主定理明示的回文占用间隙 `(a,b,a)`。反射后重新从唯一大间隙后的点开始，逆时针占用间隙仍是 `(a,b,a)`，所以按同一预定标签顺序赋值后得到同一数值角向量。这一步只是辨认 AF 形状与有向种子的对应，**没有把反射加入最终同标号 SO(2) 相似关系**。

## 方程约定和形式化状态

原 TeX 第 172–186 行使用四个正圆周间隙之和为 `2π`，并定义

\[
f_{AF}(u)=\sin u\{1-(2-2\cos u)^{-3/2}\}.
\]

本稿使用 `f=-f_AF`：正角的弦长为 `2 sin(u/2)>0`，两个表达式的分母一致；负角均按奇性延拓。全部平衡方程同时乘以 `−1`，零点不变。AF 的四颗相同小质量对应本项目和为一的质量比 `(1/4,1/4,1/4,1/4)`；公共质量因子不改变零点方程。

`DominantFiveBody.equalMass_coorbital_existsUnique` 已独立证明该规范开放半圆中实际四行共轨方程的 `∃!`，而 `equalMass_root_reversal_symmetry` 独立证明所需反序对称。它们没有把 AF 分类作为自定义公理。本次文献核对确认的是原稿引用的最低外部结论与转换范围；没有声称形式化了 AF 在全圆周上的完整三类分类。

## 固定来源的 SHA256

- 原 arXiv 完整包：`B3C5A8E943FA00AA6AAD7B013FBD00A817FF6852E46E3FD7155EA5F7254200C7`
- 实际读取的原 TeX：`DE100CB3237931A30352E8046A6C9A6E7B48504047B1394C4134C9EC751B9B20`
- 既有来源证明树笔记：`A2EC3178D0F52AA5CDE3DAB83D8B726667322EB2FC5D916A994A68DF52AC1742`

没有发现 AF 主定理在本稿该处应用中的错误。原论文、数学 Lean 源码和全文断言账本均未因本轮只读核查而改动。
