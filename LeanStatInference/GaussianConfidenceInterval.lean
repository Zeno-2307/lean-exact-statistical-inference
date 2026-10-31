module

public import LeanStatInference.GaussianStandardization

-- The Mathlib-specific copyright header convention is not a project requirement.
set_option linter.style.header false

/-!
# Exact coverage of a two-sided Gaussian Z confidence interval (B2)

The interval uses the sample mean, population standard deviation and critical
value, but not the unknown population mean. Coverage is a probability over the
sample space for a fixed population mean. All probabilities take values in `ℝ≥0∞`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace LeanStatInference

variable {Ω : Type*}

/-- The closed two-sided Z interval. Its endpoints do not depend on `μ`. -/
noncomputable def gaussianConfidenceInterval {n : ℕ} (X : Fin n → Ω → ℝ)
    (σ c : ℝ) (ω : Ω) : Set ℝ :=
  Set.Icc (sampleMean X ω - c * standardError σ n)
    (sampleMean X ω + c * standardError σ n)

/-- The event that the random interval covers the fixed population mean. -/
def gaussianCoverageEvent {n : ℕ} (X : Fin n → Ω → ℝ) (μ σ c : ℝ) : Set Ω :=
  {ω | μ ∈ gaussianConfidenceInterval X σ c ω}

/-- The strict two-sided tail probability of the standard Gaussian distribution. -/
noncomputable def gaussianTwoSidedTail (c : ℝ) : ℝ≥0∞ :=
  (gaussianReal 0 1) {z : ℝ | c < |z|}

/-- Coverage is equivalent to the closed absolute-value condition after
standardization. Only the positivity of the standard error is needed here. -/
theorem mem_gaussianConfidenceInterval_iff {n : ℕ} (hn : 0 < n)
    {X : Fin n → Ω → ℝ} {σ : ℝ} (hσ : 0 < σ) (μ c : ℝ) (ω : Ω) :
    μ ∈ gaussianConfidenceInterval X σ c ω ↔
      |standardizedSampleMean X μ σ ω| ≤ c := by
  have hSE := standardError_pos hn hσ
  simp only [gaussianConfidenceInterval, Set.mem_Icc, standardizedSampleMean,
    abs_le, le_div_iff₀ hSE, div_le_iff₀ hSE, neg_mul]
  constructor
  · rintro ⟨hLower, hUpper⟩
    constructor <;> linarith
  · rintro ⟨hLower, hUpper⟩
    constructor <;> linarith

/-- The coverage event is the inverse image of the standard Gaussian central set. -/
theorem gaussianCoverageEvent_eq {n : ℕ} (hn : 0 < n)
    {X : Fin n → Ω → ℝ} {σ : ℝ} (hσ : 0 < σ) (μ c : ℝ) :
    gaussianCoverageEvent X μ σ c =
      (standardizedSampleMean X μ σ) ⁻¹' {z : ℝ | |z| ≤ c} := by
  ext ω
  exact mem_gaussianConfidenceInterval_iff hn hσ μ c ω

variable [MeasurableSpace Ω] in
/-- The coverage event is measurable when the observations are measurable. -/
theorem measurableSet_gaussianCoverageEvent {n : ℕ} (hn : 0 < n)
    {X : Fin n → Ω → ℝ} {σ : ℝ} (hσ : 0 < σ)
    (hMeas : ∀ i, Measurable (X i)) (μ c : ℝ) :
    MeasurableSet (gaussianCoverageEvent X μ σ c) := by
  rw [gaussianCoverageEvent_eq hn hσ μ c]
  exact (measurableSet_le (by fun_prop) measurable_const).preimage
    (measurable_standardizedSampleMean hMeas μ σ)

/-- The tail probability is at most one, as needed to interpret `1 - α` in `ℝ≥0∞`. -/
theorem gaussianTwoSidedTail_le_one (c : ℝ) : gaussianTwoSidedTail c ≤ 1 := by
  exact prob_le_one

variable [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]

/-- **Exact coverage probability** of the two-sided Gaussian Z interval.
The requested positive-critical-value hypothesis is explicit; the complement
identity used in the proof also holds for arbitrary real critical values. -/
theorem gaussianConfidenceInterval_coverage {n : ℕ} (hn : 0 < n)
    {X : Fin n → Ω → ℝ} {μ σ c : ℝ} (hσ : 0 < σ) (_hc : 0 < c)
    (hMeas : ∀ i, Measurable (X i)) (hIndep : iIndepFun X P)
    (hLaw : ∀ i, P.map (X i) = gaussianReal μ (NNReal.mk σ hσ.le ^ 2)) :
    P (gaussianCoverageEvent X μ σ c) = 1 - gaussianTwoSidedTail c := by
  have hCentral : MeasurableSet {z : ℝ | |z| ≤ c} :=
    measurableSet_le (by fun_prop) measurable_const
  have hTail : MeasurableSet {z : ℝ | c < |z|} :=
    measurableSet_lt measurable_const (by fun_prop)
  have hComplement : {z : ℝ | |z| ≤ c} = {z : ℝ | c < |z|}ᶜ := by
    ext z
    simp only [Set.mem_ofPred_eq, Set.mem_compl_iff, not_lt]
  calc
    P (gaussianCoverageEvent X μ σ c) =
        (P.map (standardizedSampleMean X μ σ)) {z : ℝ | |z| ≤ c} := by
      rw [gaussianCoverageEvent_eq hn hσ μ c,
        Measure.map_apply (measurable_standardizedSampleMean hMeas μ σ) hCentral]
    _ = (gaussianReal 0 1) {z : ℝ | |z| ≤ c} := by
      rw [gaussian_standardizedSampleMean_distribution hn hσ hMeas hIndep hLaw]
    _ = 1 - gaussianTwoSidedTail c := by
      rw [hComplement, prob_compl_eq_one_sub hTail]
      rfl

end LeanStatInference
