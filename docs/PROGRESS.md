VERIFIED: 59 auxiliary theorem declarations; manuscript lem:growth fully proved.
RELATIVE_VERIFIED: 0
WIP: Full manuscript; Harnack estimates and lem:envelope are the current proof work.
BLOCKED: No external blocker. Unproved mathematical dependencies are recorded below.
SORRY_COUNT: 0
USER_AXIOM_COUNT: 0

# Full formalization progress

The goal is the full manuscript, with the original hypotheses, constants, explicit radii, endpoint inequalities, and equivalences. A definition of a proposition is not a proof. The 59 declarations include elementary auxiliary results and do not measure a percentage of manuscript completion.

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
| `lem:logderivative` | WIP | exact statement, local logarithmic derivative bounds and pole integrability |
| `lem:growth` | VERIFIED | `growthLemma_proved : GrowthLemma` |
| `lem:envelope` | WIP | derive Harnack from mathlib's Poisson formula; prove exact 8 and 64 bounds |
| `lem:poisson-mean` | WIP | logarithms at boundary zeros and subharmonic comparison |
| `lem:two-point-kernel` | WIP | rational kernel bound and uniform gap proved; harmonic integral step remains |

## Phases 2–4 — principal results and applications

| Result | Status | Remaining proof work |
|---|---|---|
| `prop:sharp-two-absorption` | WIP | harmonic comparison, path selection and contradiction |
| `thm:absorption` | WIP | exact recursive-radius target and full analytic induction |
| `cor:rank-adaptive-absorption` | WIP | minor selection and subsequence basis |
| `lem:stabilization` | WIP | Montel/Hurwitz and quotient preorder; integer-count step proved |
| `thm:main`, `cor:centers` | WIP | stabilization/absorption assembly and disk automorphisms |
| `thm:sharp-five` | WIP | classical Cartan extraction and sharp absorption; arbitrary open U retained |
| optimal five-function radius | WIP | Gaussian integral counterexample and exact extremal argument |
| `thm:torus-zero` | WIP | forward direction from an orbit is proved; converse and geometric identification remain |
| `prop:torus-null-set` | WIP | finite equations proved; closedness/algebraicity and positive compact lower bounds remain |
| `prop:projective-equivalence` | WIP | projective formalism and both implications |
| `cor:projective-zero-directions` | WIP | quotient tangent-space identification and dimension bound |

Final completion requires genuine proof terms for every row, no placeholder or manuscript-specific axioms, successful full build and recursive axiom audit, and a theorem-by-theorem comparison against `paper.tex`. No final report exists yet.
