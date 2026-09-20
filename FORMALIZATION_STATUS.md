# 形式化覆盖状态

论文的 19 项带标签结果全部有完整 Lean 证明。下表将每个论文结果映射到实际证明项；Prop 定义本身不作为完成依据。验证脚本另行核对稿件哈希、证明入口和全部定理的递归公理依赖。

| 论文标签 | 状态 | Lean 证明及保留内容 |
|---|---|---|
| `thm:main` | VERIFIED | [partitionTheorem_proved](ModifiedCartan/PartitionTheorem.lean)；[partition_at_recursive_radius](ModifiedCartan/PartitionTheorem.lean)。All p >= 3; actual C-class partition after a common strict subsequence. The explicit radius r_(p-1)^(p-1) is proved as well. |
| `thm:sharp-five` | VERIFIED | [sharpFiveTheorem_proved](ModifiedCartan/SharpFive.lean)。Arbitrary nonempty open subset of the unit disk, including disconnected sets; diameter <= log 3, with its endpoint. |
| `thm:torus-zero` | VERIFIED | [torus_manifold_metric_zero_iff](ModifiedCartan/TorusManifold.lean)。Two-way equivalence for the intrinsic manifold Kobayashi-Royden metric. Finite Laurent equations plus an embedded complex manifold present the smooth closed subvariety; see GEOMETRIC_MODEL.md. |
| `lem:cartan-circle` | VERIFIED | [cartanCircleEstimate_proved](ModifiedCartan/CartanCircle.lean)。0 < a < b < c < 1; 0 < t <= 1 including t = 1; exact power t^gamma and radius in (b,c). |
| `prop:wronskian` | VERIFIED | [quantitativeWronskian_proved](ModifiedCartan/QuantitativeWronskian.lean)。All m >= 1, normalized coefficient sphere, actual iterated-derivative determinant, c > 0 and K >= m. |
| `lem:logderivative` | VERIFIED | [logDerivativeEstimate_proved](ModifiedCartan/LogDerivativeEstimate.lean)。All derivative orders k >= 1 and original radius intervals; exact logarithmic expression; boundary zeros allowed. |
| `lem:growth` | VERIFIED | [growthLemma_proved](ModifiedCartan/Growth.lean)。The stated positive continuous nondecreasing case is proved; the internal construction also works without monotonicity. |
| `lem:envelope` | VERIFIED | [envelope_lemma](ModifiedCartan/Envelope.lean)。Exact 8 and 64 constants, closed-disk supremum and all original parameter ranges; harmonic extension is separately constructed. |
| `lem:poisson-mean` | VERIFIED | [poissonMeanEstimate_proved](ModifiedCartan/LogPoisson.lean)。Exact q and q^2 - 1 coefficients, analytic neighborhood of the closed disk, boundary zeros allowed. |
| `thm:absorption` | VERIFIED | [explicitAbsorptionTheorem_proved](ModifiedCartan/AbsorptionTheorem.lean)；[absorption_at_recursive_radius](ModifiedCartan/AbsorptionTheorem.lean)。Actual Wronskian exponent sequence is constructed; r1 = 1, r2 = 2 - sqrt 3 and r_m = r_(m-1)/(1024*(K_m+m)). |
| `cor:rank-adaptive-absorption` | VERIFIED | [rank_adaptive_absorption](ModifiedCartan/RankAdaptiveAbsorption.lean)。Rank is the dimension of the span of restricted functions on the unit disk, for each n; exact r_d and one common subsequence. |
| `lem:stabilization` | VERIFIED | [stabilization_lemma](ModifiedCartan/QuotientStabilization.lean)。Common subsequence on every sigma^k, actual quotient preorder, compact escape in sup norm and the stated maximal-class alternative. |
| `cor:centers` | VERIFIED | [partition_at_center](ModifiedCartan/PartitionCenters.lean)。Pullback by the actual disk automorphism; same explicit epsilon_p. The partition and strict subsequence may depend on the center. |
| `lem:two-point-kernel` | VERIFIED | [two_point_harmonic](ModifiedCartan/HarmonicKernel.lean)。All positive harmonic functions on the open unit disk; uniform positive epsilon_q, exact two weights. |
| `cor:geodesic-comparison` | VERIFIED | [geodesic_harmonic_comparison](ModifiedCartan/GeodesicComparison.lean)。Entire distance-additive hyperbolic segment, including coincident endpoints; exact 2*C0 and uniform epsilon for d0 < log 3. |
| `prop:sharp-two-absorption` | VERIFIED | [sharpTwoAbsorption_proved](ModifiedCartan/SharpTwoAbsorption.lean)。Arbitrary nonempty open sets; no connectedness requirement; non-strict diameter <= log 3. |
| `prop:torus-null-set` | VERIFIED | [torus_manifold_nullDirections_isClosed](ModifiedCartan/TorusManifold.lean)；[torus_manifold_compact_metric_lower](ModifiedCartan/TorusManifold.lean)；[torus_manifold_compact_inf_pos](ModifiedCartan/TorusManifold.lean)；[torus_manifold_null_image_eq_zeroLocus](ModifiedCartan/TorusTangentAlgebraic.lean)。Closed in the actual tangent bundle, equal to an explicit polynomial zero locus in (x,x^-1,v) coordinates, with a positive infimum on every compact set in the complement. |
| `prop:projective-equivalence` | VERIFIED | [projective_equivalence](ModifiedCartan/ProjectiveEquivalence.lean)。Both directions, p >= 3 and 0 < R <= 1; genuine projective quotient topology, product uniformity and manifold holomorphic maps. |
| `cor:projective-zero-directions` | VERIFIED | [projective_zero_directions](ModifiedCartan/ProjectiveTori.lean)；[projectiveTorusTangentSpace_finrank_le](ModifiedCartan/ProjectiveTori.lean)。Exact union of differential images of actual holomorphic torus embeddings, with dimension <= floor(p/2)-1. |

`def:cclass` 对应 Basic.lean 中的 IsDominant、IsCClass 和 CPartition。主导指标属于该类，保证非空；有界性对每个紧集及所有项成立，收敛是紧集上一致收敛。该谓词适用于一般集合，其在 region 上的限制覆盖论文定义。

## 补充结果

- **cartan-extraction-required-by-paper**：`cartanExtraction_three`，`cartanExtraction_four`，`cartanExtraction_five`。
- **optimal-five-radius**：`optimalFiveRadius_proved`，`partition_five_at_sharpRadius`。
- **gaussian-holomorphic-branch**：`fivePhi_differentiable`，`fiveL_differentiable`，`fivePhi_sq`。
- **gaussian-majorants-and-sign**：`five_majorant_positive_gap`，`fiveL_re_pos_right`，`fivePhi_re_nonpos_iff`，`fivePhi_re_nonneg_iff`。
- **gaussian-integral-and-tail**：`gaussianPrimitive_hasDerivAt`，`gaussianTransition_left_bound`，`gaussianTransition_right_bound`。
- **gaussian-exact-ratio-estimate**：`fivea_div_fiveA_bound`，`fivea_complement`。
- **gaussian-five-units-and-zero-sum**：`fiveCounterexample_units`，`fiveCounterexample_zeroSum`。
- **gaussian-growth-and-vanishing**：`fiveCounterexample_grows_at_zero`，`fiveA_vanishes_negative_point`，`fivea_sub_fiveA_vanishes_negative_point`，`fiveCounterexample_vanishing_points`。
- **gaussian-no-partition-any-subsequence**：`fiveCounterexample_no_partition`。
- **disk-diameter-formula**：`disk_hyperbolicDiameter_iff`，`sharpRadius_log_diameter`，`sharpRadius_hyperbolicDiameter`。
- **sharp-diameter-obstructions**：`five_partition_diameter_cannot_increase`，`two_absorption_diameter_cannot_increase`。

经典 Cartan 的 p = 5 全单位圆盘抽取已完整证明，并已接入五函数锐定理；p = 3、4 也有证明。本文未使用的历史一般 p 版本不在完成声明中。

## 数学对应

- 递推半径的有效 Wronskian 指数由 exists_wronskianExponents 构造；不是额外分析假设。
- 一般开集不被改成连通区域，直径条件保留 ≤ log 3，射影结论保留 0 < R ≤ 1。
- 所有子列均严格递增，所有局部一致极限均使用实际紧集一致收敛。
- 几何结果使用真正的 mathlib 流形切空间、微分、射影商拓扑和乘积一致结构；有限 Laurent 方程提供闭代数子簇的坐标表示。完整说明见 docs/GEOMETRIC_MODEL.md。
- Kobayashi–Royden 度量取值于非负扩展实数，使空下确界按通常扩展值约定为正无穷。

最终计数、全量重建与公理审计见 verification/result.json 和 docs/FINAL_REPORT.md。证明数量包含辅助引理，不是论文完成比例。
