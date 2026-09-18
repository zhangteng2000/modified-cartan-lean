# Proof dependency graph

Solid analytic nodes below are proof obligations until marked VERIFIED in PROGRESS.md. An arrow means the proof at the target uses the source.

```mermaid
flowchart TD
  Poisson[mathlib Poisson formula and kernel bounds] --> Harnack[Harnack comparison]
  Harnack --> Envelope[lem:envelope]
  Factor[mathlib zero orders and factorized rational functions] --> Circle[VERIFIED lem:cartan-circle]
  Harnack --> Circle
  Circle --> Wronskian[prop:wronskian]
  Factor --> LogDeriv[lem:logderivative]
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
