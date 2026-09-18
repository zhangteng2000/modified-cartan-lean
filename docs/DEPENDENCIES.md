# Proof dependency graph

Solid analytic nodes below are proof obligations until marked VERIFIED in PROGRESS.md. An arrow means the proof at the target uses the source.

```mermaid
flowchart TD
  Poisson[mathlib Poisson formula and kernel bounds] --> Harnack[Harnack comparison]
  Harnack --> Envelope[lem:envelope]
  Factor[mathlib zero orders and factorized rational functions] --> Circle[VERIFIED lem:cartan-circle]
  Harnack --> Circle
  Circle --> Wronskian[VERIFIED prop:wronskian]
  Cauchy[VERIFIED derivative and cofactor bounds] --> Coeff[VERIFIED derivative of Y inverse v]
  Coeff --> Variation[VERIFIED circle variation and combination bound]
  Variation --> Wronskian
  Factor --> LogDeriv[VERIFIED lem:logderivative]
  Poisson --> Mean[lem:poisson-mean including boundary zeros]
  Kernel[proved rational kernel inequalities] --> TwoPoint[lem:two-point-kernel for harmonic functions]
  Poisson --> TwoPoint
  TwoPoint --> Geodesic[cor:geodesic-comparison]
  Geodesic --> TwoAbs[prop:sharp-two-absorption]
  Envelope --> TwoAbs
  Mean --> TwoAbs
  LogDeriv --> TwoAbs
  Wronskian --> Abs[thm:absorption at the exact recursive radii]
  LogDeriv --> Abs
  Growth[VERIFIED lem:growth] --> Abs
  Envelope --> Abs
  Mean --> Abs
  TwoAbs --> Abs
  Abs --> Rank[cor:rank-adaptive-absorption]
  Normal[VERIFIED Montel and Hurwitz extraction] --> Stabilize[VERIFIED lem:stabilization]
  Counts[proved integer count stabilization] --> Stabilize
  Rank --> Main[thm:main]
  Stabilize --> Main
  Main --> Centers[cor:centers]
  Classical[classical Cartan extraction] --> Five[thm:sharp-five on arbitrary open sets]
  TwoAbs --> Five
  Five --> Optimal[optimalRadius 5 = 2 - sqrt 3]
  Gaussian[Gaussian integral counterexample] --> Optimal
  Main --> Torus[thm:torus-zero converse]
  Orbit[proved exponential orbit discs] --> Torus
  Torus --> Null[prop:torus-null-set]
  Finite[proved Laurent finite equations] --> Null
  Main --> Projective[prop:projective-equivalence]
  Normal --> Projective
  Projective --> Directions[cor:projective-zero-directions]
  Torus --> Directions
  Finite --> Directions
```

The sharp two-term absorption branch must remain independent of general absorption, avoiding a circular proof of the m = 2 base radius.

`DiskAutomorphisms + HarmonicComposition + HarmonicKernel → TwoPointHarnack` proves normalized harmonic comparison. `HyperbolicDiameter` retains the non-strict endpoint on arbitrary open sets and obtains a uniform strict bound on compact subsets. `SymmetricDiskSegments + TwoPointHarnack → DiskSegmentComparison` supplies actual paths and comparison on them. `FailurePointsAvoidZeros + MovingPointLimits` supplies the zero-free endpoint preparation. The full sharp two-term proof remains open.

## Proved absorption preparations

`HolomorphicCancellation` proves the m = 1 base case. `CombinationMinimum + Rescaling + AbsorptionLinearAlgebra → AbsorptionReduction → AbsorptionGap` proves the positive combination gap from the lower-dimensional induction hypothesis and failure of the conclusion. `FailurePoints → FiniteFailurePoints` constructs actual failure points. `PoissonExtension → HarmonicGrowth + PoissonHarnack → PoissonEnvelope` constructs and bounds the harmonic majorant. `UnitGrowth + GrowthSelection + ZeroFreeAnnulus` supplies divergence and controlled radii.

`WronskianScaling + QuantitativeWronskian → AbsorptionWronskian` supplies actual points with a uniform logarithmic lower bound. `WronskianBoundary + CircleExceptional → WronskianMean` supplies both mean upper bounds with boundary zeros allowed. `ConvergenceJets + NegligibleDerivatives → BoundaryErrorLimit` supplies a genuine little-o error. `LogPoisson + Radii → AbsorptionComparison` supplies the final numerical contradiction. `AbsorptionInduction` assembles all these results into the proved successor step with the exact η. Full absorption still depends on the sharp two-term base case.

## Completed logarithmic derivative chain

`ProximityGrowth → ZeroCount → LocalLogDerivativePoles → LogDerivativeConstants` supplies the actual finite poles and polynomial bounds. `AngularIntegrals + FractionalPowers + CircleExceptional + ProximityMoment → PoleMoments` supplies the mean estimate across boundary poles. Together with `LogarithmicGrowthAlgebra` these prove `IteratedLogDerivativeMean`. `ProximityLocal → DerivativeQuotientRecurrence`, followed by strong induction, proves the full `LogDerivativeEstimate`. The absorption proof can now use this lemma without a relative assumption.

Sharp two-term chain: FailurePointsAvoidZeros + FiniteFailurePoints + MovingPointLimits -> SharpTwoEndpoints. HyperbolicDiameter + SymmetricDiskSegments -> ScaledPseudodiameter. LogDerivativeEstimate -> InteriorDerivativeGrowth -> InteriorBoundaryError. LogPoisson + PoissonHarnack + CircleExceptional -> PoissonMajorant; WronskianMean + PoissonMajorant -> TwoWronskian. HarmonicComposition -> HarmonicNegativeNeighborhood. These are complete supporting proofs; the final sharp two-term contradiction remains open.

SharpTwoSetup constructs the entire failure-point and growth configuration. SharpTwoAnalyticBounds derives the actual negligible error and Poisson bound. DiskSegmentCompact supplies uniform interior bounds. The proposed fixed-domain endgame uses HarmonicNegativeNeighborhood -> ExponentialDecay -> QuotientDerivativeDecay -> VanishingDerivative, with ConvexZeroAvoidance proving the needed zero-free-domain preconnectedness. The missing link is still actual fixed-domain Wronskian decay under moving disk maps.

ParameterUniformConvergence -> DiskSegmentLimits; VaryingComposition transports the convergent sums through those maps. SegmentNeighborhood + HarmonicNegativeNeighborhood -> HarmonicRectangle. WronskianComposition transports actual determinant decay. SharpTwoCoordinates constructs maps and a common convergent parameter subsequence. These form the verified scaffold for the still-open sharp two-term conclusion.

Completed sharp-two chain: SharpTwoSetup → SharpTwoCoordinates/Subsequence → SharpTwoRectangleDecay → SharpTwoEndgame → SharpTwoAbsorption. Every setup object is constructed from the original hypotheses; both endpoint limits and the actual Wronskian decay are proved.

Completed thm:absorption: sharpRadius_pseudodiameter → sharpRadius_hyperbolicDiameter → absorption_two; absorption_one + absorption_two + absorption_successor + exists_wronskianExponents → absorption_at_recursive_radius → explicitAbsorptionTheorem_proved and absorptionTheorem_proved.
