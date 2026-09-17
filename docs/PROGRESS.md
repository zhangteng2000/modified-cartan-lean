VERIFIED: Manuscript lem:growth, lem:envelope, lem:two-point-kernel, lem:poisson-mean, lem:stabilization, and the connected two-dominant-index assertion fully proved; declaration count in verification/result.json.
RELATIVE_VERIFIED: 0
WIP: Full manuscript; Cartan circle estimates, Wronskians, logarithmic derivatives, absorption and geometric applications.
BLOCKED: No external blocker. Unproved mathematical dependencies are recorded below.
SORRY_COUNT: 0
USER_AXIOM_COUNT: 0

# Full formalization progress

The goal is the full manuscript, with the original hypotheses, constants, explicit radii, endpoint inequalities, and equivalences. A definition of a proposition is not a proof. Declaration counts include elementary auxiliary results and do not measure a percentage of manuscript completion.

## Reproducible baseline

- Lean: `leanprover/lean4:v4.34.0-rc1`.
- mathlib: `de5ce8a9a66a4aa68a9bdbb35b63a06d34d9ca11`.
- Baseline `lake build`: success, 3397 jobs; all 59 proof declarations audited.
- Permitted axioms seen: `propext`, `Classical.choice`, `Quot.sound` only.
- `paper.tex` is the supplied manuscript. Statements are located by its LaTeX labels.

## Phase 0 — setup and audit

- [x] Read manuscript, existing project and the user's full execution requirements.
- [x] Rebuild and audit the existing proof terms.
- [x] Pin Lean/mathlib and preserve the manuscript source.
- [x] Record the dependency graph, library audit, discrepancies and blockers.
- [ ] Complete exact formal statements for every remaining manuscript result.

## Phase 1 — analytic tools

| Result | Status | Remaining proof work |
|---|---|---|
| `lem:cartan-circle` | WIP | canonical factorization, zero count, logarithmic averaging and circle selection |
| `prop:wronskian` | WIP | general induction; only m = 1 and structural determinant identities proved |
| `lem:logderivative` | WIP | exact `LogDerivativeEstimate` statement added; local bounds and pole integrability remain |
| `lem:growth` | VERIFIED | `growthLemma_proved : GrowthLemma` |
| `lem:envelope` | VERIFIED | `envelope_lemma`; exact 8δ and 64η constants and closed-disk supremum |
| `lem:poisson-mean` | VERIFIED | `poissonMeanEstimate_proved : PoissonMeanEstimate`; boundary zeros permitted |
| `lem:two-point-kernel` | VERIFIED | `two_point_harmonic`; all positive harmonic functions on the open unit disk |

## Phases 2–4 — principal results and applications

| Result | Status | Remaining proof work |
|---|---|---|
| `prop:sharp-two-absorption` | WIP | harmonic comparison, path selection and contradiction |
| `thm:absorption` | WIP | `ExplicitAbsorptionTheorem` now includes exact radii and valid Wronskian exponents; analytic induction remains |
| `cor:rank-adaptive-absorption` | WIP | minor selection and subsequence basis |
| `lem:stabilization` | VERIFIED | `stabilization_lemma`; common extraction, actual quotient preorders, maximal-class counting and incomparability |
| `thm:main`, `cor:centers` | WIP | stabilization/absorption assembly and disk automorphisms |
| `thm:sharp-five` | WIP | classical Cartan extraction and sharp absorption; arbitrary open U retained |
| optimal five-function radius | WIP | Gaussian integral counterexample and exact extremal argument |
| `thm:torus-zero` | WIP | forward direction from an orbit is proved; converse and geometric identification remain |
| `prop:torus-null-set` | WIP | finite equations proved; closedness/algebraicity and positive compact lower bounds remain |
| `prop:projective-equivalence` | WIP | projective formalism and both implications |
| `cor:projective-zero-directions` | WIP | quotient tangent-space identification and dimension bound |

Final completion requires genuine proof terms for every row, no placeholder or manuscript-specific axioms, successful full build and recursive axiom audit, and a theorem-by-theorem comparison against `paper.tex`. No final report exists yet.

## Verified analytic checkpoint

`Harmonic.lean` proves both centered Harnack inequalities directly from the library Poisson formula and proves boundary nonnegativity implies interior nonnegativity. `Envelope.lean` proves `lem:envelope` for the harmonic extension U of the positive boundary maximum. The extension is represented by `HarmonicContOnCl` plus the exact boundary-maximum equality (`IsGreatest`), matching the manuscript's given U. The origin estimate and supremum estimate have the original constants.

Git initialized in the deliverable directory; no remote is configured, so no push target exists.

`HarmonicKernel.lean` connects the real rational kernel to mathlib's complex Poisson kernel, integrates the uniform inequality on circles of radius R, and passes to R → 1 from below. Thus `two_point_harmonic` assumes no boundary continuity on the unit circle and proves the full manuscript lemma, with a single positive ε depending only on q.

`LogPoisson.lean` proves Poisson comparison for logarithmic factors with zeros in the closed disk, including boundary zeros using mathlib's integrability theorem. Finite zero-factor extraction then gives the comparison for any analytic F nonzero at the evaluation point. Integrating the upper and lower kernel bounds proves the manuscript's exact q log|F(w)| − (q²−1)m(R,F) bound. `poissonMeanEstimate_proved` has the original normalized q = (1+t)/(1−t), t = |w|/R.

`Convergence.lean` proves preservation of C-classes and partitions under subsequences, finite simultaneous extraction, transitivity of locally bounded quotients, the exact change-of-dominant-index criterion, boundedness of convergent continuous families including initial terms, and holomorphic/derivative limit interfaces. These results do not assume connectedness.

`Hurwitz.lean` proves Hurwitz nonvanishing on a connected open set, inversion of locally uniform limits, and boundedness of their reciprocals. `Montel.lean` proves locally bounded holomorphic families are equicontinuous and admits a convergent subsequence on any open subset, using Schwarz and mathlib's Arzelà–Ascoli theorem. `CClass.lean` combines simultaneous Montel extraction with Hurwitz to prove `cclass_two_dominants_after_extraction` in full. The connectedness hypothesis occurs in this auxiliary assertion, not in the C-class definition or the main/sharp targets.

`Extraction.lean` proves simultaneous holomorphic-limit-or-compact-supremum-divergence alternatives, including their equivalence to boundedness/unboundedness after extraction. `FinitePreorder.lean` counts actual maximal equivalence classes as finite sets, constructs the injection between successive maximal-class sets, and proves incomparability when the counts agree. `QuotientStabilization.lean` combines them into the full `lem:stabilization` for the manuscript radii σ^k, 0 < σ < 1, on a nonempty finite family. No analytic or order-theoretic conclusion is supplied as an extra hypothesis.
