module

public import LeanStatInference.GaussianHypothesisTest

-- The Mathlib-specific copyright header convention is not a project requirement.
set_option linter.style.header false

/-!
# Pointwise equivalence of Gaussian Z intervals and tests (B4)

These results are algebraic and logical: they need neither a measurable space nor
a probability measure, independence, or Gaussian laws. Positive sample size and
standard deviation suffice, and the critical value may be any real number.
-/

@[expose] public section

namespace LeanStatInference

variable {Ω : Type*}

/-- A closed confidence interval excludes the specified null mean exactly when
the absolute Z statistic strictly exceeds the critical value. -/
theorem gaussianCI_rejection_iff {n : ℕ} (hn : 0 < n)
    {X : Fin n → Ω → ℝ} {σ : ℝ} (hσ : 0 < σ) (μ₀ c : ℝ) (ω : Ω) :
    μ₀ ∉ gaussianConfidenceInterval X σ c ω ↔
      c < |standardizedSampleMean X μ₀ σ ω| := by
  rw [mem_gaussianConfidenceInterval_iff hn hσ μ₀ c ω, not_le]

/-- Rejection and noncoverage are the same subset of the sample space, not merely
events with the same probability under a particular model. -/
theorem gaussianRejectionEvent_eq_compl_coverageEvent {n : ℕ} (hn : 0 < n)
    {X : Fin n → Ω → ℝ} {σ : ℝ} (hσ : 0 < σ) (μ₀ c : ℝ) :
    gaussianRejectionEvent X μ₀ σ c = (gaussianCoverageEvent X μ₀ σ c)ᶜ := by
  ext ω
  change (c < |standardizedSampleMean X μ₀ σ ω|) ↔
    μ₀ ∉ gaussianConfidenceInterval X σ c ω
  exact (gaussianCI_rejection_iff hn hσ μ₀ c ω).symm

/-- Equality at the critical value is included in the closed interval and does
not cause rejection. No zero-probability boundary argument is needed. -/
theorem gaussianCI_boundary_mem_and_not_reject {n : ℕ} (hn : 0 < n)
    {X : Fin n → Ω → ℝ} {σ : ℝ} (hσ : 0 < σ) (μ₀ c : ℝ) (ω : Ω)
    (hBoundary : |standardizedSampleMean X μ₀ σ ω| = c) :
    μ₀ ∈ gaussianConfidenceInterval X σ c ω ∧
      ω ∉ gaussianRejectionEvent X μ₀ σ c := by
  refine ⟨(mem_gaussianConfidenceInterval_iff hn hσ μ₀ c ω).mpr hBoundary.le, ?_⟩
  exact not_lt_of_ge hBoundary.le

end LeanStatInference
