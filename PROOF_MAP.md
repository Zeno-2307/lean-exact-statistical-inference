# Proof Map

This is an inventory of the actual project declarations, not a claim of new statistical discoveries. All names are in `LeanStatInference`. Links point to the verified mathematical source files in this snapshot. See the [README](README.md) for the mathematical model, formulas, and build instructions.

## Definitions

| Definition | Source | Meaning |
| --- | --- | --- |
| `sampleMean` | [GaussianSampling.lean](LeanStatInference/GaussianSampling.lean#L26) | Arithmetic mean of a `Fin n` family. |
| `standardError` | [GaussianStandardization.lean](LeanStatInference/GaussianStandardization.lean#L24) | Known population standard deviation divided by the square root of the sample size. |
| `standardizedSampleMean` | [GaussianStandardization.lean](LeanStatInference/GaussianStandardization.lean#L40) | Sample mean centered at a specified mean and divided by its standard error. |
| `gaussianConfidenceInterval` | [GaussianConfidenceInterval.lean](LeanStatInference/GaussianConfidenceInterval.lean#L26) | Closed interval around the sample mean; its arguments do not include the unknown mean. |
| `gaussianCoverageEvent` | [GaussianConfidenceInterval.lean](LeanStatInference/GaussianConfidenceInterval.lean#L32) | The samples for which the random interval contains a fixed mean. |
| `gaussianTwoSidedTail` | [GaussianConfidenceInterval.lean](LeanStatInference/GaussianConfidenceInterval.lean#L36) | Standard Gaussian measure of the strict tail set `{z : ℝ \| c < \|z\|}`; values in `ℝ≥0∞`. |
| `gaussianRejectionEvent` | [GaussianHypothesisTest.lean](LeanStatInference/GaussianHypothesisTest.lean#L26) | The samples for which the absolute statistic centered at the specified null mean strictly exceeds `c`. |

## Assumptions and conclusion types

- A and B1 main theorems work on an arbitrary measurable space with `P : Measure Ω` and `[IsProbabilityMeasure P]`. They assume `0 < n`, `0 < σ`, measurable observations, `iIndepFun X P`, and common marginal distribution `gaussianReal μ (NNReal.mk σ hσ.le ^ 2)`. Their conclusions are equalities of full measures. Gaussian integrability is derived, not assumed separately.
- B2 uses that model and explicitly assumes `0 < c`. B3 uses the corresponding null model with mean `μ₀`, also with `0 < c`. Both conclusions are equalities in `ℝ≥0∞`. Their `_hc` parameter is unused by the proof: the underlying measure identities also hold for arbitrary real critical values.
- B2's pointwise membership theorem and all B4 theorems require `0 < n` and `0 < σ` but no measurable-space, measure, or distributional assumptions. B4 permits any real `c`; its boundary corollary additionally assumes equality of the absolute statistic with `c`.
- The central set uses `≤ c` and the tail uses `c <`. They are exact complements. B2 uses `prob_compl_eq_one_sub` for truncated subtraction in `ℝ≥0∞`; `gaussianTwoSidedTail_le_one` separately records the probability bound. No zero-probability boundary argument is needed.

## Theorem inventory

### A — Sampling distribution

| Theorem | Role and direct proof dependencies |
| --- | --- |
| [measurable_sampleSum](LeanStatInference/GaussianSampling.lean#L30) | Finite sums of measurable observations are measurable; uses Mathlib measurability automation. |
| [measurable_sampleMean](LeanStatInference/GaussianSampling.lean#L35) | The sample mean is measurable; finite sums and division by a constant. |
| [integrable_of_hasLaw_gaussian](LeanStatInference/GaussianSampling.lean#L44) | Gaussian law implies integrability; `memLp_id_gaussianReal`, `HasLaw.memLp`, and `memLp_one_iff_integrable`. This helper is not an extra assumption of the main theorem. |
| [hasLaw_gaussian_finset_sum](LeanStatInference/GaussianSampling.lean#L52) | Induction over a finite set; `iIndepFun.indepFun_finsetSum_of_notMem₀` and `gaussianReal_add_gaussianReal_of_indepFun`. Allows different Gaussian means and variances. The empty case uses a Dirac measure. |
| [hasLaw_gaussian_sampleSum](LeanStatInference/GaussianSampling.lean#L74) | Specializes the finite-set law to `Fin n`; the parameters become `n * μ` and `n * v`. |
| [hasLaw_gaussian_sampleMean](LeanStatInference/GaussianSampling.lean#L82) | Divides the sum by positive `n` using `gaussianReal_div_const`; simplifies mean and variance to `μ` and `v / n`. |
| [gaussian_sampleMean_distribution](LeanStatInference/GaussianSampling.lean#L101) | Main A result: packages the measurable marginal laws as `HasLaw` and extracts the sample-mean measure equality. |

### B1 — Standardization

| Theorem | Role and direct proof dependencies |
| --- | --- |
| [standardError_pos](LeanStatInference/GaussianStandardization.lean#L28) | Positive `n` and `σ` imply positive standard error; uses `Real.sqrt_pos` and `div_pos`. |
| [standardError_sq](LeanStatInference/GaussianStandardization.lean#L33) | Proves `SE² = σ² / n` using `Real.sq_sqrt`; the algebraic identity also holds with Lean's total division when `n = 0`. |
| [measurable_standardizedSampleMean](LeanStatInference/GaussianStandardization.lean#L45) | Reuses A's `measurable_sampleMean`; subtraction and division by constants preserve measurability. |
| [hasLaw_standardizedSampleMean](LeanStatInference/GaussianStandardization.lean#L54) | Invokes A's main theorem, then `gaussianReal_sub_const` and `gaussianReal_div_const`. Uses the two standard-error lemmas to obtain variance one. |
| [gaussian_standardizedSampleMean_distribution](LeanStatInference/GaussianStandardization.lean#L77) | Main B1 result: extracts the complete standard Gaussian distribution equality from the preceding `HasLaw` theorem. |

### B2 — Confidence interval coverage

| Theorem | Role and direct proof dependencies |
| --- | --- |
| [mem_gaussianConfidenceInterval_iff](LeanStatInference/GaussianConfidenceInterval.lean#L41) | Pointwise equivalence of interval membership and the non-strict absolute-value bound. Uses B1's `standardError_pos`, `abs_le`, positive-division order lemmas, and linear arithmetic. |
| [gaussianCoverageEvent_eq](LeanStatInference/GaussianConfidenceInterval.lean#L55) | Set extensionality and the preceding membership theorem identify coverage as the inverse image of the central set. |
| [measurableSet_gaussianCoverageEvent](LeanStatInference/GaussianConfidenceInterval.lean#L64) | Uses that event identity and B1's measurable standardized statistic. |
| [gaussianTwoSidedTail_le_one](LeanStatInference/GaussianConfidenceInterval.lean#L73) | Uses `prob_le_one` for the standard Gaussian probability measure. |
| [gaussianConfidenceInterval_coverage](LeanStatInference/GaussianConfidenceInterval.lean#L81) | Main B2 result: the event identity, `Measure.map_apply`, B1's distribution theorem, and `prob_compl_eq_one_sub` give `1 - gaussianTwoSidedTail c`. |

### B3 — Type I error

| Theorem | Role and direct proof dependencies |
| --- | --- |
| [measurableSet_gaussianRejectionEvent](LeanStatInference/GaussianHypothesisTest.lean#L32) | The strict absolute-value tail is measurable; its inverse image under B1's measurable statistic is the rejection event. |
| [gaussianRejectionEvent_probability_eq_map](LeanStatInference/GaussianHypothesisTest.lean#L43) | `Measure.map_apply` expresses the rejection-event measure through the statistic's distribution. No Gaussian or probability-measure assumption is required for this helper. |
| [gaussianZTest_typeIError_exact](LeanStatInference/GaussianHypothesisTest.lean#L57) | Main B3 result: the preceding measure identity, B1's distribution theorem under `hNull`, and B2's tail definition. Does not use the B2 coverage theorem. |

### B4 — Interval/test equivalence

| Theorem | Role and direct proof dependencies |
| --- | --- |
| [gaussianCI_rejection_iff](LeanStatInference/GaussianCITestEquivalence.lean#L24) | Negates B2's `mem_gaussianConfidenceInterval_iff` and rewrites with `not_le`. |
| [gaussianRejectionEvent_eq_compl_coverageEvent](LeanStatInference/GaussianCITestEquivalence.lean#L32) | Set extensionality and the preceding equivalence connect B3's rejection definition with B2's coverage definition. |
| [gaussianCI_boundary_mem_and_not_reject](LeanStatInference/GaussianCITestEquivalence.lean#L42) | Uses B2's membership equivalence and `not_lt_of_ge` to prove inclusion and non-rejection when the absolute statistic equals the critical value. |

## Import graph versus proof dependencies

The source imports form this chain:

```text
Mathlib.Probability.Distributions.Gaussian.Real
  → GaussianSampling
  → GaussianStandardization
  → GaussianConfidenceInterval
  → GaussianHypothesisTest
  → GaussianCITestEquivalence
```

The root module imports all five modules and the unchanged starter `Basic.lean`. The starter's `hello` definition has no mathematical role.

Importing a module does not mean every proof uses every theorem it contains. In particular, B3 uses B2's tail definition without invoking its coverage theorem. B4 uses the interval-membership algebra and event definitions without invoking any Gaussian distribution theorem. The README's diagram separates these dependencies.

## Mathlib foundation

The following links are pinned to the Mathlib commit in `lake-manifest.json`.

| Infrastructure or theorem | Role | Source |
| --- | --- | --- |
| `ProbabilityTheory.gaussianReal`, its probability-measure instance | Gaussian measure with mean `μ` and variance `v : ℝ≥0` | [Gaussian/Real.lean](https://github.com/leanprover-community/mathlib4/blob/9d581dfff2e41de989072ea63abf3daf69311520/Mathlib/Probability/Distributions/Gaussian/Real.lean#L217) |
| `gaussianReal_add_gaussianReal_of_indepFun` | Addition of independent Gaussian variables; adds means and variances | [Gaussian/Real.lean](https://github.com/leanprover-community/mathlib4/blob/9d581dfff2e41de989072ea63abf3daf69311520/Mathlib/Probability/Distributions/Gaussian/Real.lean#L651) |
| `gaussianReal_sub_const`, `gaussianReal_div_const` | Centering and scaling the complete distribution | [Gaussian/Real.lean](https://github.com/leanprover-community/mathlib4/blob/9d581dfff2e41de989072ea63abf3daf69311520/Mathlib/Probability/Distributions/Gaussian/Real.lean#L395) |
| `iIndepFun.indepFun_finsetSum_of_notMem₀` | Independence of an observation and a disjoint finite sum | [Independence/Basic.lean](https://github.com/leanprover-community/mathlib4/blob/9d581dfff2e41de989072ea63abf3daf69311520/Mathlib/Probability/Independence/Basic.lean#L1005); generated from the product version by `to_additive` |
| `gaussianReal_zero_var`, `Measure.map_const` | Empty sum represented as a constant with a Dirac law | [Gaussian/Real.lean](https://github.com/leanprover-community/mathlib4/blob/9d581dfff2e41de989072ea63abf3daf69311520/Mathlib/Probability/Distributions/Gaussian/Real.lean#L227), [Measure/Map.lean](https://github.com/leanprover-community/mathlib4/blob/9d581dfff2e41de989072ea63abf3daf69311520/Mathlib/MeasureTheory/Measure/Map.lean) |
| `memLp_id_gaussianReal`, `HasLaw.memLp` | Gaussian integrability and transfer along a distribution equality | [Gaussian/Real.lean](https://github.com/leanprover-community/mathlib4/blob/9d581dfff2e41de989072ea63abf3daf69311520/Mathlib/Probability/Distributions/Gaussian/Real.lean), [Probability/HasLaw.lean](https://github.com/leanprover-community/mathlib4/blob/9d581dfff2e41de989072ea63abf3daf69311520/Mathlib/Probability/HasLaw.lean) |
| `Measure.map_apply` | Probability of an inverse image equals pushforward measure of the target set | [Measure/Map.lean](https://github.com/leanprover-community/mathlib4/blob/9d581dfff2e41de989072ea63abf3daf69311520/Mathlib/MeasureTheory/Measure/Map.lean#L170) |
| `prob_compl_eq_one_sub` | Complement formula for a measurable event under a probability measure | [Typeclasses/Probability.lean](https://github.com/leanprover-community/mathlib4/blob/9d581dfff2e41de989072ea63abf3daf69311520/Mathlib/MeasureTheory/Measure/Typeclasses/Probability.lean#L155) |

The proofs also use Mathlib's finite sums, real and nonnegative-real arithmetic, square-root identities, measurable absolute value, order lemmas, and set extensionality. `HasLaw` packages almost-everywhere measurability together with the pushforward equality; the main distribution statements expose the equality directly.

Mathlib already provides `iIndepFun.hasGaussianLaw_fun_sum`, a more general Gaussian-closure theorem in [HasGaussianLaw/Independence.lean](https://github.com/leanprover-community/mathlib4/blob/9d581dfff2e41de989072ea63abf3daf69311520/Mathlib/Probability/Distributions/Gaussian/HasGaussianLaw/Independence.lean#L388). It is not the theorem used by this project's finite-set induction, which tracks explicit mean and variance parameters. Gaussian closure itself is existing library infrastructure.

## Axiom audit and reproduction

The 23 theorems listed above were each checked with `#print axioms` in the existing local environment. Every result was the same set:

```text
[propext, Classical.choice, Quot.sound]
```

These are standard Lean foundations. No `sorryAx` or project-defined axiom occurred. To repeat the checks, first run `lake build`, then use a temporary Lean file importing `LeanStatInference` with one `#print axioms LeanStatInference.<name>` command per theorem. Run it with `lake env lean <file>.lean`. For fully explicit theorem parameters, use `#check @LeanStatInference.<name>` or `#print LeanStatInference.<name>`.

The audit applies to the formal statements and their dependencies. It does not certify empirical assumptions, numerical software, authorship, or independent reproduction in another environment.
