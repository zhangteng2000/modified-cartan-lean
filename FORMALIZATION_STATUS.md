# 形式化覆盖状态

**全文尚未证明。当前交付是可编译的部分形式化项目。**

论文中的主定理没有被替换成 `axiom`、假设或占位证明。`Statements.lean` 中定义为 `Prop` 的目标，只有存在相应的证明项才算完成。尤其 `PartitionTheorem`、`QuantitativeWronskian`、`AbsorptionTheorem`、`SharpFiveTheorem`、`SharpTwoAbsorption` 和 `OptimalFiveRadius` 目前都没有完整证明。

下表用原稿的 LaTeX 标签定位，避免共享编号造成误会。

| 原稿结果 | 当前状态 | Lean 对应及剩余工作 |
|---|---|---|
| `def:cclass` 及两个主导指标断言 | 完整证明 | `CClass.lean` 的 `cclass_two_dominants_after_extraction` 已包含同时 Montel 抽取和 Hurwitz 步骤；仅此辅助断言要求连通性。定义、子列保持、更换主导指标判据均已完成。 |
| `thm:main` | 仅主命题陈述 | `ModifiedCartan.PartitionTheorem`。尚无分割主定理的证明。 |
| `thm:sharp-five` | 仅主命题陈述，部分工具已证明 | `SharpFiveTheorem`；尚缺 Cartan 定理、两项吸收估计及组装过程。 |
| `thm:torus-zero` | 一个方向完成 | `kobayashiRoyden_zero_of_orbit` 证明轨道包含推出零伪度量，使用环境坐标中的圆盘定义。反向蕴含未证明；与抽象复流形版本的识别未形式化。 |
| `lem:cartan-circle` | 仅命题陈述 | `CartanCircleEstimate`；零点分解、Harnack 估计及选圆平均步骤未证明。 |
| `prop:wronskian` | 单函数情形完成，一般命题仅陈述 | `quantitativeWronskian_one`；一般归纳、辅因子估计、Schur 补公式、圆弧积分和最大值原理的组合未证明。另有常数缩放及线性相关推出行列式为零的完整证明。 |
| `lem:logderivative` | 精确命题已陈述 | `AnalyticStatements.lean` 的 `LogDerivativeEstimate`；证明尚未完成。 |
| `lem:growth` | 完整证明 | `growthLemma_proved : GrowthLemma`。证明得到更强结果：连续与正性已足够，不需要单调性。 |
| `lem:envelope` | 完整证明 | `envelope_lemma` 保留原稿所有参数范围、8 和 64 两个常数，以及闭圆盘上的上确界。`Harmonic.lean` 从 Poisson 公式证明所用 Harnack 比较。 |
| `lem:poisson-mean` | 完整证明 | `poissonMeanEstimate_proved : PoissonMeanEstimate`，允许边界零点，保留原稿的 q 和 q²−1 系数。 |
| `thm:absorption` | 精确递归半径目标已陈述，半径代数已证明 | `ExplicitAbsorptionTheorem` 同时要求构造有效的 Wronskian 指数并在原稿指定半径上证明吸收。`AbsorptionTheorem` 仅为较弱的存在半径推论目标。解析证明未完成。 |
| `cor:rank-adaptive-absorption` | 未形式化 | 最大行列式选基、子列固定基和吸收定理应用未证明。 |
| `lem:stabilization` | 整数计数步骤完成 | `count_stabilization`；Montel 抽取、商函数预序、极大等价类计数和比较的完整论证未证明。 |
| `cor:centers` | 未形式化 | 需主定理与圆盘自同构的拉回。 |
| `lem:two-point-kernel` | 完整证明 | `two_point_harmonic`：统一正间隙、一般圆周上的 Poisson 积分和半径趋近 1 的极限均已证明，对开单位圆盘内任意正调和函数成立。 |
| `cor:geodesic-comparison` | 未形式化 | Harnack 比较、自同构归一化与测地段步骤未证明。 |
| `prop:sharp-two-absorption` | 仅命题陈述 | `SharpTwoAbsorption`；失败点选取、调和函数估计、避零路径和积分矛盾未证明。 |
| `R_5 = 2 - sqrt(3)` 与尖锐反例 | 仅最优性目标陈述，数值恒等式已证明 | `OptimalFiveRadius` 未证明。`sharpRadius_log_diameter` 只证明对数表达式的代数值；尚未证明该表达式等于圆盘双曲直径，也没有形式化高斯积分反例。 |
| `prop:torus-null-set` | 有限方程判据完成 | `laurent_orbit_zero_iff_finite_equations`，允许重复轨道指数和任意整数单项式幂。零方向集合的代数性、闭性及补集上紧集正下界尚未证明。 |
| `prop:projective-equivalence` | 未形式化 | 尚缺射影映射、Montel/Hurwitz 及两种分割表述的等价。 |
| `cor:projective-zero-directions` | 指数和分组工具完成 | `exponentialSum_zero_iff_grouped` 已证明；射影环面切空间与零方向的最终识别、维数界未证明。 |

## 证明边界

- 当前本地源码包含 106 个已证明定理。它们包含辅助引理，不能把数量当作论文完成比例。
- 已证明的结果直接使用实际复数、导数、行列式、紧集收敛、指数函数和 Laurent 单项式定义。
- `GrowthLemma`、调和包络、调和函数两点核和对数 Poisson 平均四个引理有完整证明项。其他中心 `Prop` 目标没有被任何已证明定理当作隐含假设引入。
- `kobayashiRoyden` 取值于非负扩展实数，使不存在符合条件的圆盘时下确界为正无穷，避免实数空集下确界误判为零。
- `LaurentData` 是有限 Laurent 多项式表示，允许重复幂向量；有限方程判据对这种表示仍成立。它本身不构造代数簇或切丛。

## 后续证明依赖

完成主定理需要先补齐定量 Wronskian 估计、局部对数导数估计、Harnack/Poisson 辅助估计和两项吸收估计，再完成一般吸收估计及预序稳定化。五函数最优性还需要正式处理高斯积分反例。几何应用的反向蕴含和紧集正下界最后依赖分割主定理及商函数导数估计。

此文件记录尚未完成的工作，不代表这些结果已被 Lean 验证。
