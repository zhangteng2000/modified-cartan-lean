# Classical Cartan extraction — completed

The precise classical theorem required by the manuscript is proved by `cartanExtraction_five : CartanExtractionAt 5` in `ModifiedCartan/CartanFive.lean`. The p = 3 and p = 4 instances are also proved. The conclusion uses one common strict subsequence on the entire open unit disk: either all indices form one C-class, or there are two disjoint nonempty C-classes. No extraction theorem is postulated.

The historical theorem for arbitrary p is not needed by the paper's five-function argument and is not claimed here. Its unused initial proposition target was removed; none of the paper's theorem statements was changed.

## Proof chain

1. Montel, Hurwitz, omitted-value normality and the three-function extraction are proved from mathlib compactness, complex analysis and the project definitions.
2. Finite quotient limits and vanishing quotients give an actual zero-free annulus on which two indices can be merged. C-classes and disjointness are transferred back to the original indices; the maximum principle fills the inner disk.
3. The remaining cases give actual pair-Wronskian anchors. Radial outer-measure alternatives for the third and fourth derived fractions either force a previously excluded quotient limit or provide quantitative higher-Wronskian anchors and inverse-proximity bounds.
4. The zero-sum identity and logarithmic derivative estimates close the growth inequality. The four-function and five-function endgames prove the contradiction in the case with no earlier reduction. No auxiliary case hypothesis is retained in the unconditional local theorems.
5. An explicit holomorphic disk-to-annulus covering, open mapping and compact lifts transfer the four-function theorem to each annulus needed in the five-function reduction.
6. A nested strict diagonal subsequence, a countable exhaustion and finite stabilization of both classes and dominant indices give the full-unit-disk theorem. Bounds for finite initial terms are restored using continuity.
7. `FiveClassReduction` and the proved sharp two-term absorption combine this with the one remaining index. `sharpFiveTheorem_proved` preserves arbitrary open sets and diameter <= log 3. `optimalFiveRadius_proved` combines it with the genuine Gaussian counterexample.

## Entry points

| Result | Lean module / theorem |
|---|---|
| Three functions | CartanThree / cartanExtraction_three |
| Four functions | CartanFour / cartanExtraction_four |
| Four functions on annuli | CartanFourAnnulus / cartan_four_annulus |
| Uniform triple anchors | TripleAnchorsFromCases / eventually_uniform_triple_anchors |
| Five-function higher-Wronskian contradiction | CartanFiveWronskianEndgame / five_anchored_subfamily_impossible |
| All local five-function cases | CartanFiveLocal / cartan_five_local |
| Five functions on the entire disk | CartanFive / cartanExtraction_five |
| Sharp theorem and optimal radius | SharpFive / sharpFiveTheorem_proved, optimalFiveRadius_proved |

## Provenance

Henri Cartan, *Annales scientifiques de l'École Normale Supérieure*, 45 (1928), Theorem VII, pp. 312–315, [DOI 10.24033/asens.786](https://www.numdam.org/articles/10.24033/asens.786/). The original pages were consulted. The required mathematics is proved in local Lean modules; the reference contributes no logical assumption. The radial outer-measure argument implements the quantitative case analysis without relying on an unformalized exceptional-disk lemma.
