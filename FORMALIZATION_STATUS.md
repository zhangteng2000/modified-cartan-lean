# 形式化覆盖状态

**全文尚未证明。当前交付是可编译的部分形式化项目。**

论文中的主定理没有被替换成 `axiom`、假设或占位证明。`Statements.lean` 中定义为 `Prop` 的目标，只有存在相应的证明项才算完成。`PartitionTheorem`、`QuantitativeWronskian`、`ExplicitAbsorptionTheorem`、`AbsorptionTheorem` 和 `SharpTwoAbsorption` 已有完整证明项。`SharpFiveTheorem` 和 `OptimalFiveRadius` 仍未证明。

下表用原稿的 LaTeX 标签定位，避免共享编号造成误会。

| 原稿结果 | 当前状态 | Lean 对应及剩余工作 |
|---|---|---|
| `def:cclass` 及两个主导指标断言 | 完整证明 | `CClass.lean` 的 `cclass_two_dominants_after_extraction` 已包含同时 Montel 抽取和 Hurwitz 步骤；仅此辅助断言要求连通性。定义、子列保持、更换主导指标判据均已完成。 |
| `thm:main` | 完整证明 | `partitionTheorem_proved`；更强的 `partition_at_recursive_radius` 保留 εₚ = rₚ₋₁^(p−1)，实际构造分组并由吸收证明归一化极限为零。 |
| `thm:sharp-five` | 仅主命题陈述，部分工具已证明 | `SharpFiveTheorem`；尚缺经典 Cartan 抽取及最终组装；两项吸收定理已完整证明。 |
| `thm:torus-zero` | 一个方向完成 | `kobayashiRoyden_zero_of_orbit` 证明轨道包含推出零伪度量，使用环境坐标中的圆盘定义。反向蕴含未证明；与抽象复流形版本的识别未形式化。 |
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
| `cor:geodesic-comparison` | 未形式化 | Harnack 比较、自同构归一化与测地段步骤未证明。 |
| `prop:sharp-two-absorption` | 完整证明 | `sharpTwoAbsorption_proved`；任意不连通开集及 ≤ log 3 端点，实际失败点、坐标、Wronskian 衰减和端点矛盾均已证明。 |
| `R_5 = 2 - sqrt(3)` 与尖锐反例 | 仅最优性目标陈述，数值恒等式已证明 | `OptimalFiveRadius` 未证明。`sharpRadius_log_diameter` 只证明对数表达式的代数值；尚未证明该表达式等于圆盘双曲直径，也没有形式化高斯积分反例。 |
| `prop:torus-null-set` | 有限方程判据完成 | `laurent_orbit_zero_iff_finite_equations`，允许重复轨道指数和任意整数单项式幂。零方向集合的代数性、闭性及补集上紧集正下界尚未证明。 |
| `prop:projective-equivalence` | 未形式化 | 尚缺射影映射、Montel/Hurwitz 及两种分割表述的等价。 |
| `cor:projective-zero-directions` | 指数和分组工具完成 | `exponentialSum_zero_iff_grouped` 已证明；射影环面切空间与零方向的最终识别、维数界未证明。 |

## 证明边界

- 当前证明声明总数记录于 `verification/result.json`。它们包含辅助引理，不能把数量当作论文完成比例。
- 已证明的结果直接使用实际复数、导数、行列式、紧集收敛、指数函数和 Laurent 单项式定义。
- 已证明结果以本表及 docs/PROGRESS.md 为准，中心定理的证明项由 Audit.lean 审计。未证明的目标未被作为论文专属公理引入。
- `kobayashiRoyden` 取值于非负扩展实数，使不存在符合条件的圆盘时下确界为正无穷，避免实数空集下确界误判为零。
- `LaurentData` 是有限 Laurent 多项式表示，允许重复幂向量；有限方程判据对这种表示仍成立。它本身不构造代数簇或切丛。

## 后续证明依赖

分割主定理及其解析依赖已完成证明。剩余工作包括五函数尖锐结论、测地段表述的识别和几何应用。五函数最优性还需要正式处理高斯积分反例。几何应用的反向蕴含和紧集正下界最后依赖分割主定理及商函数导数估计。

此文件记录尚未完成的工作，不代表这些结果已被 Lean 验证。
