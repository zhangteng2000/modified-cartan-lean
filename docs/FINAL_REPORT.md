# 完整形式化验收报告

论文全部 19 项带标签的作者结果，以及最优半径、完整高斯反例、直径不可改进性和射影切空间维数结论均已有 Lean 证明项。289 个本地模块在新的构建目录中重建成功，1020 个本地定理逐一通过递归公理审计。

验收时间：2026-09-19T23:38:49.7170484Z。源码证明检查点：`e84e54567afaa9ded782f6d3da0826311407ac55`。以下结论由真实的 Lean 编译和审计输出支持；完整记录见 [result.json](../verification/result.json)、[构建日志](../verification/build.log)、[证明入口检查](../verification/manuscript-check.log)和[公理日志](../verification/axioms.log)。

## 稿件及形式化范围

本项目以 [paper.tex](../paper.tex) 为唯一稿件，SHA-256 为 `76592f6d46c40f2632eb426651fa1e062e4427c302a96ad7406b6a923835bb89`。

下表覆盖 19 项带标签结果；另有 def:cclass，对应 Basic.lean 中的 IsDominant、IsCClass 和 CPartition。实际商函数有界性、紧集一致收敛、固定主导指标和严格子列均保留。

经典 Cartan 定理只形式化本文实际需要的 p = 5 全单位圆盘版本，另已证明 p = 3、4。论文文献综述中的任意 p 历史版本、Borel/Picard 的历史叙述和 Yamanoi 结果不作为本项目新增的作者定理，也没有被作为公理导入。

## 每项主要结果及公理依赖

列出的名称均为实际定理证明项。公理列来自本次 #print axioms 输出，是递归依赖检查，不是对 Prop 定义的检查。三项标准逻辑公理 propext、Classical.choice、Quot.sound 符合用户验收要求。

| 论文标签 | 精确 Lean 名称 | 源文件与行号 | #print axioms 结果 |
|---|---|---|---|
| `thm:main` | `ModifiedCartan.partitionTheorem_proved` | [ModifiedCartan/PartitionTheorem.lean:104](../ModifiedCartan/PartitionTheorem.lean#L104) | `[propext, Classical.choice, Quot.sound]` |
| `thm:main` | `ModifiedCartan.partition_at_recursive_radius` | [ModifiedCartan/PartitionTheorem.lean:10](../ModifiedCartan/PartitionTheorem.lean#L10) | `[propext, Classical.choice, Quot.sound]` |
| `thm:sharp-five` | `ModifiedCartan.sharpFiveTheorem_proved` | [ModifiedCartan/SharpFive.lean:12](../ModifiedCartan/SharpFive.lean#L12) | `[propext, Classical.choice, Quot.sound]` |
| `thm:torus-zero` | `ModifiedCartan.torus_manifold_metric_zero_iff` | [ModifiedCartan/TorusManifold.lean:30](../ModifiedCartan/TorusManifold.lean#L30) | `[propext, Classical.choice, Quot.sound]` |
| `lem:cartan-circle` | `ModifiedCartan.cartanCircleEstimate_proved` | [ModifiedCartan/CartanCircle.lean:123](../ModifiedCartan/CartanCircle.lean#L123) | `[propext, Classical.choice, Quot.sound]` |
| `prop:wronskian` | `ModifiedCartan.quantitativeWronskian_proved` | [ModifiedCartan/QuantitativeWronskian.lean:11](../ModifiedCartan/QuantitativeWronskian.lean#L11) | `[propext, Classical.choice, Quot.sound]` |
| `lem:logderivative` | `ModifiedCartan.logDerivativeEstimate_proved` | [ModifiedCartan/LogDerivativeEstimate.lean:95](../ModifiedCartan/LogDerivativeEstimate.lean#L95) | `[propext, Classical.choice, Quot.sound]` |
| `lem:growth` | `ModifiedCartan.growthLemma_proved` | [ModifiedCartan/Growth.lean:52](../ModifiedCartan/Growth.lean#L52) | `[propext, Classical.choice, Quot.sound]` |
| `lem:envelope` | `ModifiedCartan.envelope_lemma` | [ModifiedCartan/Envelope.lean:122](../ModifiedCartan/Envelope.lean#L122) | `[propext, Classical.choice, Quot.sound]` |
| `lem:poisson-mean` | `ModifiedCartan.poissonMeanEstimate_proved` | [ModifiedCartan/LogPoisson.lean:246](../ModifiedCartan/LogPoisson.lean#L246) | `[propext, Classical.choice, Quot.sound]` |
| `thm:absorption` | `ModifiedCartan.explicitAbsorptionTheorem_proved` | [ModifiedCartan/AbsorptionTheorem.lean:72](../ModifiedCartan/AbsorptionTheorem.lean#L72) | `[propext, Classical.choice, Quot.sound]` |
| `thm:absorption` | `ModifiedCartan.absorption_at_recursive_radius` | [ModifiedCartan/AbsorptionTheorem.lean:60](../ModifiedCartan/AbsorptionTheorem.lean#L60) | `[propext, Classical.choice, Quot.sound]` |
| `cor:rank-adaptive-absorption` | `ModifiedCartan.rank_adaptive_absorption` | [ModifiedCartan/RankAdaptiveAbsorption.lean:10](../ModifiedCartan/RankAdaptiveAbsorption.lean#L10) | `[propext, Classical.choice, Quot.sound]` |
| `lem:stabilization` | `ModifiedCartan.stabilization_lemma` | [ModifiedCartan/QuotientStabilization.lean:30](../ModifiedCartan/QuotientStabilization.lean#L30) | `[propext, Classical.choice, Quot.sound]` |
| `cor:centers` | `ModifiedCartan.partition_at_center` | [ModifiedCartan/PartitionCenters.lean:63](../ModifiedCartan/PartitionCenters.lean#L63) | `[propext, Classical.choice, Quot.sound]` |
| `lem:two-point-kernel` | `ModifiedCartan.two_point_harmonic` | [ModifiedCartan/HarmonicKernel.lean:89](../ModifiedCartan/HarmonicKernel.lean#L89) | `[propext, Classical.choice, Quot.sound]` |
| `cor:geodesic-comparison` | `ModifiedCartan.geodesic_harmonic_comparison` | [ModifiedCartan/GeodesicComparison.lean:11](../ModifiedCartan/GeodesicComparison.lean#L11) | `[propext, Classical.choice, Quot.sound]` |
| `prop:sharp-two-absorption` | `ModifiedCartan.sharpTwoAbsorption_proved` | [ModifiedCartan/SharpTwoAbsorption.lean:87](../ModifiedCartan/SharpTwoAbsorption.lean#L87) | `[propext, Classical.choice, Quot.sound]` |
| `prop:torus-null-set` | `ModifiedCartan.torus_manifold_nullDirections_isClosed` | [ModifiedCartan/TorusManifold.lean:40](../ModifiedCartan/TorusManifold.lean#L40) | `[propext, Classical.choice, Quot.sound]` |
| `prop:torus-null-set` | `ModifiedCartan.torus_manifold_compact_metric_lower` | [ModifiedCartan/TorusManifold.lean:59](../ModifiedCartan/TorusManifold.lean#L59) | `[propext, Classical.choice, Quot.sound]` |
| `prop:torus-null-set` | `ModifiedCartan.torus_manifold_compact_inf_pos` | [ModifiedCartan/TorusManifold.lean:84](../ModifiedCartan/TorusManifold.lean#L84) | `[propext, Classical.choice, Quot.sound]` |
| `prop:torus-null-set` | `ModifiedCartan.torus_manifold_null_image_eq_zeroLocus` | [ModifiedCartan/TorusTangentAlgebraic.lean:51](../ModifiedCartan/TorusTangentAlgebraic.lean#L51) | `[propext, Classical.choice, Quot.sound]` |
| `prop:projective-equivalence` | `ModifiedCartan.projective_equivalence` | [ModifiedCartan/ProjectiveEquivalence.lean:78](../ModifiedCartan/ProjectiveEquivalence.lean#L78) | `[propext, Classical.choice, Quot.sound]` |
| `cor:projective-zero-directions` | `ModifiedCartan.projective_zero_directions` | [ModifiedCartan/ProjectiveTori.lean:175](../ModifiedCartan/ProjectiveTori.lean#L175) | `[propext, Classical.choice, Quot.sound]` |
| `cor:projective-zero-directions` | `ModifiedCartan.projectiveTorusTangentSpace_finrank_le` | [ModifiedCartan/ProjectiveTori.lean:197](../ModifiedCartan/ProjectiveTori.lean#L197) | `[propext, Classical.choice, Quot.sound]` |

## 补充结论和完整反例

反例使用实际的复平方根分支、全纯高斯原函数和具体五函数。a、b 通过 z 与 -z 的对称定义给出，保留 3/(4n) 上界；不只是存在某个抽象反例。无分割结论覆盖每个 2 - sqrt 3 < R <= 1 及每个严格递增子列。

| 结论组 | 精确 Lean 名称 | 源文件与行号 | #print axioms 结果 |
|---|---|---|---|
| `cartan-extraction-required-by-paper` | `ModifiedCartan.cartanExtraction_three` | [ModifiedCartan/CartanThree.lean:33](../ModifiedCartan/CartanThree.lean#L33) | `[propext, Classical.choice, Quot.sound]` |
| `cartan-extraction-required-by-paper` | `ModifiedCartan.cartanExtraction_four` | [ModifiedCartan/CartanFour.lean:10](../ModifiedCartan/CartanFour.lean#L10) | `[propext, Classical.choice, Quot.sound]` |
| `cartan-extraction-required-by-paper` | `ModifiedCartan.cartanExtraction_five` | [ModifiedCartan/CartanFive.lean:10](../ModifiedCartan/CartanFive.lean#L10) | `[propext, Classical.choice, Quot.sound]` |
| `optimal-five-radius` | `ModifiedCartan.optimalFiveRadius_proved` | [ModifiedCartan/SharpFive.lean:30](../ModifiedCartan/SharpFive.lean#L30) | `[propext, Classical.choice, Quot.sound]` |
| `optimal-five-radius` | `ModifiedCartan.partition_five_at_sharpRadius` | [ModifiedCartan/SharpFive.lean:19](../ModifiedCartan/SharpFive.lean#L19) | `[propext, Classical.choice, Quot.sound]` |
| `gaussian-holomorphic-branch` | `ModifiedCartan.fivePhi_differentiable` | [ModifiedCartan/FiveExampleFunctions.lean:34](../ModifiedCartan/FiveExampleFunctions.lean#L34) | `[propext, Classical.choice, Quot.sound]` |
| `gaussian-holomorphic-branch` | `ModifiedCartan.fiveL_differentiable` | [ModifiedCartan/FiveExampleFunctions.lean:52](../ModifiedCartan/FiveExampleFunctions.lean#L52) | `[propext, Classical.choice, Quot.sound]` |
| `gaussian-holomorphic-branch` | `ModifiedCartan.fivePhi_sq` | [ModifiedCartan/FiveExampleFunctions.lean:62](../ModifiedCartan/FiveExampleFunctions.lean#L62) | `[propext, Classical.choice, Quot.sound]` |
| `gaussian-majorants-and-sign` | `ModifiedCartan.five_majorant_positive_gap` | [ModifiedCartan/FiveMajorant.lean:51](../ModifiedCartan/FiveMajorant.lean#L51) | `[propext, Classical.choice, Quot.sound]` |
| `gaussian-majorants-and-sign` | `ModifiedCartan.fiveL_re_pos_right` | [ModifiedCartan/FiveMajorant.lean:28](../ModifiedCartan/FiveMajorant.lean#L28) | `[propext, Classical.choice, Quot.sound]` |
| `gaussian-majorants-and-sign` | `ModifiedCartan.fivePhi_re_nonpos_iff` | [ModifiedCartan/FivePhiSign.lean:56](../ModifiedCartan/FivePhiSign.lean#L56) | `[propext, Classical.choice, Quot.sound]` |
| `gaussian-majorants-and-sign` | `ModifiedCartan.fivePhi_re_nonneg_iff` | [ModifiedCartan/FivePhiSign.lean:62](../ModifiedCartan/FivePhiSign.lean#L62) | `[propext, Classical.choice, Quot.sound]` |
| `gaussian-integral-and-tail` | `ModifiedCartan.gaussianPrimitive_hasDerivAt` | [ModifiedCartan/GaussianPrimitive.lean:24](../ModifiedCartan/GaussianPrimitive.lean#L24) | `[propext, Classical.choice, Quot.sound]` |
| `gaussian-integral-and-tail` | `ModifiedCartan.gaussianTransition_left_bound` | [ModifiedCartan/GaussianContour.lean:100](../ModifiedCartan/GaussianContour.lean#L100) | `[propext, Classical.choice, Quot.sound]` |
| `gaussian-integral-and-tail` | `ModifiedCartan.gaussianTransition_right_bound` | [ModifiedCartan/GaussianContour.lean:122](../ModifiedCartan/GaussianContour.lean#L122) | `[propext, Classical.choice, Quot.sound]` |
| `gaussian-exact-ratio-estimate` | `ModifiedCartan.fivea_div_fiveA_bound` | [ModifiedCartan/FiveExampleBounds.lean:48](../ModifiedCartan/FiveExampleBounds.lean#L48) | `[propext, Classical.choice, Quot.sound]` |
| `gaussian-exact-ratio-estimate` | `ModifiedCartan.fivea_complement` | [ModifiedCartan/FiveExampleBounds.lean:69](../ModifiedCartan/FiveExampleBounds.lean#L69) | `[propext, Classical.choice, Quot.sound]` |
| `gaussian-five-units-and-zero-sum` | `ModifiedCartan.fiveCounterexample_units` | [ModifiedCartan/FiveCounterexample.lean:26](../ModifiedCartan/FiveCounterexample.lean#L26) | `[propext, Classical.choice, Quot.sound]` |
| `gaussian-five-units-and-zero-sum` | `ModifiedCartan.fiveCounterexample_zeroSum` | [ModifiedCartan/FiveCounterexample.lean:37](../ModifiedCartan/FiveCounterexample.lean#L37) | `[propext, Classical.choice, Quot.sound]` |
| `gaussian-growth-and-vanishing` | `ModifiedCartan.fiveCounterexample_grows_at_zero` | [ModifiedCartan/FiveCounterexample.lean:43](../ModifiedCartan/FiveCounterexample.lean#L43) | `[propext, Classical.choice, Quot.sound]` |
| `gaussian-growth-and-vanishing` | `ModifiedCartan.fiveA_vanishes_negative_point` | [ModifiedCartan/FiveExampleLimits.lean:32](../ModifiedCartan/FiveExampleLimits.lean#L32) | `[propext, Classical.choice, Quot.sound]` |
| `gaussian-growth-and-vanishing` | `ModifiedCartan.fivea_sub_fiveA_vanishes_negative_point` | [ModifiedCartan/FiveExampleLimits.lean:74](../ModifiedCartan/FiveExampleLimits.lean#L74) | `[propext, Classical.choice, Quot.sound]` |
| `gaussian-growth-and-vanishing` | `ModifiedCartan.fiveCounterexample_vanishing_points` | [ModifiedCartan/FiveCounterexample.lean:52](../ModifiedCartan/FiveCounterexample.lean#L52) | `[propext, Classical.choice, Quot.sound]` |
| `gaussian-no-partition-any-subsequence` | `ModifiedCartan.fiveCounterexample_no_partition` | [ModifiedCartan/FiveCounterexample.lean:71](../ModifiedCartan/FiveCounterexample.lean#L71) | `[propext, Classical.choice, Quot.sound]` |
| `disk-diameter-formula` | `ModifiedCartan.disk_hyperbolicDiameter_iff` | [ModifiedCartan/DiskDiameter.lean:81](../ModifiedCartan/DiskDiameter.lean#L81) | `[propext, Classical.choice, Quot.sound]` |
| `disk-diameter-formula` | `ModifiedCartan.sharpRadius_log_diameter` | [ModifiedCartan/Radii.lean:32](../ModifiedCartan/Radii.lean#L32) | `[propext, Classical.choice, Quot.sound]` |
| `disk-diameter-formula` | `ModifiedCartan.sharpRadius_hyperbolicDiameter` | [ModifiedCartan/AbsorptionTheorem.lean:45](../ModifiedCartan/AbsorptionTheorem.lean#L45) | `[propext, Classical.choice, Quot.sound]` |
| `sharp-diameter-obstructions` | `ModifiedCartan.five_partition_diameter_cannot_increase` | [ModifiedCartan/FiveOptimalityUpper.lean:35](../ModifiedCartan/FiveOptimalityUpper.lean#L35) | `[propext, Classical.choice, Quot.sound]` |
| `sharp-diameter-obstructions` | `ModifiedCartan.two_absorption_diameter_cannot_increase` | [ModifiedCartan/TwoAbsorptionCounterexample.lean:87](../ModifiedCartan/TwoAbsorptionCounterexample.lean#L87) | `[propext, Classical.choice, Quot.sound]` |

## 常数、假设和几何对应

- 保留 r1 = 1、r2 = 2 - sqrt 3、r_m = r_(m-1)/(1024*(K_m+m))；有效的 K_m 由已证明的 Wronskian 估计构造。
- 保留 epsilon_p = r_(p-1)^(p-1)、秩自适应半径 r_d、包络中的 8 和 64、Poisson 估计中的 q 和 q² - 1、测地比较中的 2C0。
- 五函数和两项吸收保留任意非空开集及 diameter <= log 3 的端点。没有加入连通性。
- 射影等价保留两个方向、p >= 3 和 0 < R <= 1，使用真正的射影商拓扑、乘积一致结构和流形全纯映射。
- 环面子簇使用有限 Laurent 方程的闭零集及实际复嵌入流形表示；切向量是实际流形切向量，环境坐标由嵌入的微分给出。内在 Kobayashi–Royden 度量与坐标圆盘定义的相等已经证明。代数零方向结论是整个零点集的等式，包含反向构造。详见 [几何模型](GEOMETRIC_MODEL.md)。
- 度量取值于非负扩展实数，按通常约定处理空下确界；这避免了实数空下确界错误地等于零的问题。

## mathlib 与外部依赖

Lean 工具链：`leanprover/lean4:v4.34.0-rc1`。固定依赖如下；模块数按编译器 .ilean 的完整导入闭包统计，包含 tactic 基础设施。

| 包 | 固定提交 | 导入闭包模块数 |
|---|---|---|
| mathlib | `de5ce8a9a66a4aa68a9bdbb35b63a06d34d9ca11` | 3302 |
| plausible | `38e9c3ce15cbb63c92e90bb9a92e4eb82131f669` | 13 |
| LeanSearchClient | `2bc7cf064315b26bc38dac2e9612fb581be9b75f` | 4 |
| importGraph | `978b7ec9fbbf9a535114f1de8fe5b3778b358870` | 10 |
| proofwidgets | `99e8adeea3c3cd86b6b79ba01a1383bf2d31d055` | 13 |
| aesop | `c1c4362a130f12e632d252180a6c2a31d8fd4726` | 132 |
| Qq | `3b55e9d00c6b0018e5d984eb011b6f93c09bd163` | 14 |
| batteries | `01bc479e7432594821ba3fb0ca465211941de86d` | 78 |
| Cli | `af8bc067a4cc6c6df472a68909a3f40b1c76c43e` | 0 |

此外导入 Lean/Std 核心模块 1399 个。全部 3302 个 mathlib 模块以及其他包和核心模块逐个列于本报告的[依赖附录](MATHLIB_DEPENDENCIES.md)。[机器可读清单](../verification/dependencies.json)包含所有直接导入边、传递导入闭包、固定版本以及本地源码引用的 mathlib 声明。它由 [生成脚本](../scripts/dependency-audit.mjs)读取成功构建的编译器元数据生成，不是估计列表。该导入清单与证明的逻辑公理依赖是两个不同层次；后者完整记录于 [axiom-summary.json](../verification/axiom-summary.json)。

主要复用 Poisson 表示、Cauchy 估计、解析零点与亚纯函数、紧性与 Arzelà–Ascoli、行列式、Laurent/多项式零点集、流形和射影化基础。未在固定 mathlib 中找到的 Cartan 抽取、定量估计、内在度量桥接和射影结构均在本项目证明。[库来源审计](LIBRARY_AUDIT.md)给出细节和 Cartan 原始文献来源。

## 论文与形式化的对应

[数学对应说明](MANUSCRIPT_CORRESPONDENCE.md)说明精确递推半径、内在几何模型、C-class 定义与一般开集结论、结果计数及经典 Cartan 输入的形式化。全部主要结果都有完整证明，常数、假设和结论与论文相符。

## 构建与复核

本次成功命令在项目根目录运行：

```powershell
.\verify.ps1 -Fresh
```

脚本在 `C:/Users/HUAWEI/AppData/Local/Temp/ModifiedCartan-496d74ba5f6a402e9d378ff4c76a3a59` 中工作，固定 mathlib 缓存来自 E:/Lean 4/Sendov_conjecture_explicit_n0/.lake/packages。所有本地模块从空目录重建，以至多 4 个就绪模块组成一批；随后正常执行 lake build、lake env lean ManuscriptCheck.lean 和 lake env lean Audit.lean。各包提交和工作树均检查通过。源文件与稿件哈希记录在 [source-hashes.json](../verification/source-hashes.json)。

首次不限制并发的尝试遇到库文件读取错误，改用受控批次后完整重建通过。没有修改数学陈述或降低证明检查。日志中的样式 linter 建议不属于编译错误。

在另一台电脑安装 elan 后可执行：

```text
lake exe cache get
lake build
lake env lean ManuscriptCheck.lean
lake env lean Audit.lean
```

Windows 上若使用项目自己的依赖缓存，可运行：

```powershell
.\verify.ps1 -PackageRoot (Resolve-Path '.lake/packages').Path -Fresh
```

## 最终验收值

| 项目 | 结果 |
|---|---|
| 19 项主要结果 | VERIFIED |
| 本地定理审计 | 1020 / 1020 |
| 证明入口检查 | 54 / 54 |
| sorry | 0 |
| admit | 0 |
| 论文专属公理 | 0 |
| RELATIVE_VERIFIED | 0 |
| WIP / BLOCKED | 0 / 0 |
| 编译错误 | 0 |
| 允许的标准逻辑公理 | propext, Classical.choice, Quot.sound |

完整源码、论文及验证记录见 [GitHub 仓库](https://github.com/zhangteng2000/modified-cartan-lean)。
