# 形式化覆盖状态

**全文尚未证明。当前交付是可编译的部分形式化项目。**

论文中的主定理没有被替换成 `axiom`、假设或占位证明。`Statements.lean` 中定义为 `Prop` 的目标，只有存在相应的证明项才算完成。`PartitionTheorem`、`QuantitativeWronskian`、`ExplicitAbsorptionTheorem`、`AbsorptionTheorem` 和 `SharpTwoAbsorption` 已有完整证明项。`SharpFiveTheorem` 和 `OptimalFiveRadius` 仍未证明。

下表用原稿的 LaTeX 标签定位，避免共享编号造成误会。

| 原稿结果 | 当前状态 | Lean 对应及剩余工作 |
|---|---|---|
| `def:cclass` | 定义及配套性质完成 | 定义、子列保持、更换主导指标判据均已完成。新版改用 region 一词；Lean 保留适用于一般开集的谓词，见 docs/REVISION_2026-09-19.md。新版删除的两个主导指标断言仍作为已证明的辅助引理保留。 |
| `thm:main` | 完整证明 | `partitionTheorem_proved`；更强的 `partition_at_recursive_radius` 保留 εₚ = rₚ₋₁^(p−1)，实际构造分组并由吸收证明归一化极限为零。 |
| `thm:sharp-five` | 仅主命题陈述，部分工具已证明 | `SharpFiveTheorem`；尚缺经典 Cartan 抽取及最终组装；两项吸收定理已完整证明。 |
| `thm:torus-zero` | 完整证明 | `torus_manifold_metric_zero_iff`；使用实际流形微分和切空间，已证明坐标圆盘与内在圆盘的双向转换及度量相等。有限 Laurent 表示与复嵌入流形数据对应原稿假设，见 docs/GEOMETRIC_MODEL.md。 |
| `lem:cartan-circle` | 完整证明 | `cartanCircleEstimate_proved : CartanCircleEstimate`；有限零点分解、Blaschke 估计、零点计数、Harnack 比较、带重数选圆和最终幂次下界均已证明，覆盖 t = 1。 |
| `prop:wronskian` | 完整证明 | `quantitativeWronskian_proved`；全部 m ≥ 1，原稿的行列式、最小组合范数、正常数及 K ≥ m。 |
| `lem:logderivative` | 完整证明 | `logDerivativeEstimate_proved`；所有阶数和允许半径，边界零点已处理，原稿估计保持不变。 |
| `lem:growth` | 完整证明 | `growthLemma_proved : GrowthLemma`。证明得到更强结果：连续与正性已足够，不需要单调性。 |
| `lem:envelope` | 完整证明 | `envelope_lemma` 保留原稿所有参数范围、8 和 64 两个常数，以及闭圆盘上的上确界。`Harmonic.lean` 从 Poisson 公式证明所用 Harnack 比较。 |
| `lem:poisson-mean` | 完整证明 | `poissonMeanEstimate_proved : PoissonMeanEstimate`，允许边界零点，保留原稿的 q 和 q²−1 系数。 |
| `thm:absorption` | 完整证明 | `explicitAbsorptionTheorem_proved` 构造有效指数序列并证明精确递推半径上的吸收；`absorptionTheorem_proved` 为存在形式推论。 |
| `cor:rank-adaptive-absorption` | 完整证明 | `rank_adaptive_absorption`；单位圆盘上限制函数的秩，有界消元及共同子列，精确半径 r_d。 |
| `lem:stabilization` | 完整证明 | `stabilization_lemma`；同时分析抽取、固定紧集上的最大值发散、实际商函数预序、极大等价类计数及下一层不可比较性均已证明。 |
| `cor:centers` | 完整证明 | `partition_at_center`；实际 C-类分割通过圆盘自同构拉回，保留同一显式半径。 |
| `lem:two-point-kernel` | 完整证明 | `two_point_harmonic`：统一正间隙、一般圆周上的 Poisson 积分和半径趋近 1 的极限均已证明，对开单位圆盘内任意正调和函数成立。 |
| `cor:geodesic-comparison` | 完整证明 | `geodesic_harmonic_comparison`；距离加法等式刻画的全部双曲测地段，严格阈值 d₀ < log 3，统一正 ε 和原稿的 2C₀，包含端点重合情形。 |
| `prop:sharp-two-absorption` | 完整证明 | `sharpTwoAbsorption_proved`；任意不连通开集及 ≤ log 3 端点，实际失败点、坐标、Wronskian 衰减和端点矛盾均已证明。 |
| `R_5 = 2 - sqrt(3)` 与尖锐反例 | 反例及上界完整证明；等式尚缺正面结论 | 实际高斯五函数反例已完整证明，覆盖每个 2−√3 < R ≤ 1 和任意子列；已证明 R₅ ≤ 2−√3，以及五函数分割和两项吸收的直径都不能超过 log 3。`OptimalFiveRadius` 的等式仍缺五函数正面结论。 |
| `prop:torus-null-set` | 完整证明 | 内在切丛中的闭性、紧集正下界和严格正下确界均已证明；`torus_manifold_null_image_eq_zeroLocus` 将全部内在零方向精确识别为显式有限多项式理想的零点集。 |
| `prop:projective-equivalence` | 完整证明 | `projective_equivalence`；真实商拓扑及一致结构、X_p 的流形全纯性、共同子列、乘积射影空间中的局部一致收敛，以及全局超平面 Hurwitz 论证均已证明。保留 p ≥ 3 与 0 < R ≤ 1。 |
| `cor:projective-zero-directions` | 完整证明 | `projective_zero_directions`：实际射影流形的内在零方向等于各可容许环面包含映射在 x 的微分像之并。环面模型与齐次分块缩放定义完全对应，包含映射全纯、拓扑嵌入且微分单射；`projectiveTorusTangentSpace_finrank_le` 保留维数 ≤ ⌊p/2⌋−1。 |

## 证明边界

- 当前证明声明总数记录于 `verification/result.json`。它们包含辅助引理，不能把数量当作论文完成比例。
- 已证明的结果直接使用实际复数、导数、行列式、紧集收敛、指数函数和 Laurent 单项式定义。
- 已证明结果以本表及 docs/PROGRESS.md 为准，中心定理的证明项由 Audit.lean 审计。未证明的目标未被作为论文专属公理引入。
- `kobayashiRoyden` 取值于非负扩展实数，使不存在符合条件的圆盘时下确界为正无穷，避免实数空集下确界误判为零。
- `LaurentData` 是有限 Laurent 多项式表示，允许重复幂向量；有限方程判据对这种表示仍成立。`TorusEquations` 构造实际共同零集，`ManifoldDiscs`、`TorusManifold` 和 `TorusTangentAlgebraic` 完成内在切丛识别。

## 后续证明依赖

分割主定理及其解析依赖已完成证明。剩余工作为经典 Cartan 抽取、五函数尖锐正面结论及半径等式。射影分割等价性现已完整证明。高斯积分反例、半径上界及两项吸收的不可改进性现已完整证明；五函数正面结论仍需经典 Cartan 抽取及组装。环面零方向定理及切丛零集的闭性、代数性与紧集严格正下界已完成；射影应用的两项结果现均有完整证明。

此文件记录尚未完成的工作，不代表这些结果已被 Lean 验证。
