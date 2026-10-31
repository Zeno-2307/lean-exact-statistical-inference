# Project Overview

## The question

What must be true for a familiar statistical formula to be exactly correct?

This project examines one connected example: estimating an unknown population mean from independent Gaussian observations when the population standard deviation is known. Textbooks give formulas for the sample mean, a confidence interval, and a hypothesis test. The goal here was to turn the reasoning connecting those formulas into explicit mathematical statements and proofs that a computer can check.

This is a formal verification project, not a discovery of new statistical theorems or an experiment on collected data. Its central question is whether the conclusions follow from precisely stated assumptions, for every positive finite sample size.

## What was verified

The development follows five steps:

1. **Sampling distribution.** The average of the observations has an exact Gaussian distribution, with the original population mean and variance divided by the sample size.
2. **Standardization.** Subtracting the population mean and dividing by the standard error produces the standard Gaussian distribution.
3. **Confidence interval.** An interval centered on the sample mean covers the fixed population mean with exactly the stated probability, expressed using a Gaussian tail probability.
4. **Hypothesis test.** When the specified null mean is the true mean, the chance of rejecting it is exactly that same tail probability.
5. **Agreement of the decisions.** For every sample outcome, the interval excludes a proposed mean exactly when the test rejects it. At the boundary, the closed interval includes the proposed mean and the test does not reject.

The last result needs only algebra and order, whereas the probability results require the Gaussian sampling assumptions. Distinguishing these levels is part of the formalization.

## Why the details matter

An informal instruction to “standardize the mean” hides several obligations. The divisor must be positive. Gaussian variance must be distinguished from standard deviation. Independence of a whole family must support independence of an observation from the sum of the others. Events must be measurable before applying the relevant probability identities.

The project also keeps statistical interpretation explicit. A confidence interval's coverage describes variation across samples; it is not a probability distribution on the unknown parameter after data have been observed. A null hypothesis specifies which probability model is being considered, rather than becoming a random event to condition on.

These distinctions guided the implementation and audits. They make the formal statements more informative than a list of formulas alone.

## How the proofs were checked

Lean 4 is a programming language and theorem prover. Each proof is checked against its formal statement by Lean's kernel. Mathlib, its community mathematics library, already provides measure theory, independence, Gaussian distributions, and many transformation theorems.

The project combines that infrastructure into a statistical proof chain, rather than rebuilding the library. Its five mathematics modules contain 23 named theorems, including measurability and algebraic helpers. Local compilation and axiom checks passed. The audit found only standard Lean foundational axioms, with no unfinished-proof axioms. The source and pinned dependency versions are available for inspection and reproduction; a fresh-machine reproduction has not yet been tested.

## Contribution and AI-assisted development

The project lead selected the mathematical objectives, fixed the model and scope, and specified the assumption audits and verification standards. ChatGPT/Codex provided substantial implementation assistance: finding library APIs, writing and revising Lean proofs, debugging, running verification, and preparing documentation. This work is therefore presented as an AI-assisted project, not as wholly unaided proof coding.

The project's formalization contribution is the explicit statistical definitions and the construction connecting existing results to the final distribution, coverage, error-probability, and decision-equivalence theorems. The mathematics is classical.

The formal development makes explicit which assumptions each step needs, which library theorem supplies it, and what the final statement guarantees. The repository exposes those choices so readers can examine both the reasoning and the result. Successful compilation does not establish that the statistical model fits real-world data.

For the formulas, assumptions, and verification commands, see the [README](README.md). For individual statements and dependencies, see the [proof map](PROOF_MAP.md).
