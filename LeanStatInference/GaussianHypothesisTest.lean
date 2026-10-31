module

public import LeanStatInference.GaussianConfidenceInterval

-- The Mathlib-specific copyright header convention is not a project requirement.
set_option linter.style.header false

/-!
# Exact Type I error of the two-sided Gaussian Z test (B3)

The statistic is B1's `standardizedSampleMean X μ₀ σ`, centered at the specified
null mean. The null hypothesis is expressed by the marginal Gaussian laws under
`P`, not by conditioning on a random event. B2 supplies `gaussianTwoSidedTail`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory

namespace LeanStatInference

variable {Ω : Type*}

/-- Reject the specified null mean `μ₀` when the absolute Z statistic exceeds
the critical value. The rule does not refer to an unknown true mean. -/
def gaussianRejectionEvent {n : ℕ} (X : Fin n → Ω → ℝ) (μ₀ σ c : ℝ) : Set Ω :=
  {ω | c < |standardizedSampleMean X μ₀ σ ω|}

variable [MeasurableSpace Ω]

/-- The rejection event is measurable whenever the observations are measurable. -/
theorem measurableSet_gaussianRejectionEvent {n : ℕ} {X : Fin n → Ω → ℝ}
    (hMeas : ∀ i, Measurable (X i)) (μ₀ σ c : ℝ) :
    MeasurableSet (gaussianRejectionEvent X μ₀ σ c) := by
  have hTail : MeasurableSet {z : ℝ | c < |z|} :=
    measurableSet_lt measurable_const (by fun_prop)
  exact hTail.preimage (measurable_standardizedSampleMean hMeas μ₀ σ)

variable {P : Measure Ω}

/-- The rejection-event measure is the pushforward measure of the strict tail
set. This identity requires measurability but no distributional assumption. -/
theorem gaussianRejectionEvent_probability_eq_map {n : ℕ} {X : Fin n → Ω → ℝ}
    (hMeas : ∀ i, Measurable (X i)) (μ₀ σ c : ℝ) :
    P (gaussianRejectionEvent X μ₀ σ c) =
      (P.map (standardizedSampleMean X μ₀ σ)) {z : ℝ | c < |z|} := by
  have hTail : MeasurableSet {z : ℝ | c < |z|} :=
    measurableSet_lt measurable_const (by fun_prop)
  exact (Measure.map_apply (measurable_standardizedSampleMean hMeas μ₀ σ) hTail).symm

variable [IsProbabilityMeasure P]

/-- **Exact Type I error probability.** Under the null Gaussian model with mean
`μ₀`, rejection has probability `gaussianTwoSidedTail c` in `ℝ≥0∞`.
The requested positive critical value is explicit; the pushforward argument
itself also works for arbitrary real critical values. -/
theorem gaussianZTest_typeIError_exact {n : ℕ} (hn : 0 < n)
    {X : Fin n → Ω → ℝ} {μ₀ σ c : ℝ} (hσ : 0 < σ) (_hc : 0 < c)
    (hMeas : ∀ i, Measurable (X i)) (hIndep : iIndepFun X P)
    (hNull : ∀ i, P.map (X i) = gaussianReal μ₀ (NNReal.mk σ hσ.le ^ 2)) :
    P (gaussianRejectionEvent X μ₀ σ c) = gaussianTwoSidedTail c := by
  rw [gaussianRejectionEvent_probability_eq_map hMeas μ₀ σ c,
    gaussian_standardizedSampleMean_distribution hn hσ hMeas hIndep hNull]
  rfl

end LeanStatInference
