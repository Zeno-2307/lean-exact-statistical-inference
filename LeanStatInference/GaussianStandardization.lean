module

public import LeanStatInference.GaussianSampling

-- The Mathlib-specific copyright header convention is not a project requirement.
set_option linter.style.header false

/-!
# Exact standardization of the Gaussian sample mean (B1)

The population standard deviation is `σ`; the standard error is `σ / sqrt n`.
The exact distribution theorem reuses Phase 1 and Gaussian affine transformations.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace LeanStatInference

/-- The standard error of a sample mean, using the population standard deviation.
The statistical interpretation requires `0 < n` and `0 < σ`. -/
noncomputable def standardError (σ : ℝ) (n : ℕ) : ℝ :=
  σ / Real.sqrt (n : ℝ)

/-- Positive sample size and population standard deviation give positive standard error. -/
theorem standardError_pos {σ : ℝ} {n : ℕ} (hn : 0 < n) (hσ : 0 < σ) :
    0 < standardError σ n := by
  exact div_pos hσ (Real.sqrt_pos.mpr (Nat.cast_pos.mpr hn))

/-- The square of the standard error is the sample-mean variance. -/
theorem standardError_sq (σ : ℝ) (n : ℕ) :
    standardError σ n ^ 2 = σ ^ 2 / (n : ℝ) := by
  rw [standardError, div_pow, Real.sq_sqrt (Nat.cast_nonneg n)]

variable {Ω : Type*} [MeasurableSpace Ω]

/-- The sample mean centered at the population mean and divided by its standard error. -/
noncomputable def standardizedSampleMean {n : ℕ} (X : Fin n → Ω → ℝ)
    (μ σ : ℝ) : Ω → ℝ :=
  fun ω ↦ (sampleMean X ω - μ) / standardError σ n

/-- Standardization preserves measurability. -/
theorem measurable_standardizedSampleMean {n : ℕ} {X : Fin n → Ω → ℝ}
    (hMeas : ∀ i, Measurable (X i)) (μ σ : ℝ) :
    Measurable (standardizedSampleMean X μ σ) := by
  exact ((measurable_sampleMean hMeas).sub measurable_const).div_const _

variable {P : Measure Ω} [IsProbabilityMeasure P]

/-- The standardized Gaussian sample mean has the standard Gaussian law.
The sample-mean law is obtained directly from the verified Phase 1 main theorem. -/
theorem hasLaw_standardizedSampleMean {n : ℕ} (hn : 0 < n)
    {X : Fin n → Ω → ℝ} {μ σ : ℝ} (hσ : 0 < σ)
    (hMeas : ∀ i, Measurable (X i)) (hIndep : iIndepFun X P)
    (hLaw : ∀ i, P.map (X i) = gaussianReal μ (NNReal.mk σ hσ.le ^ 2)) :
    HasLaw (standardizedSampleMean X μ σ) (gaussianReal 0 1) P := by
  have hMean : HasLaw (sampleMean X)
      (gaussianReal μ ((NNReal.mk σ hσ.le ^ 2) / (n : ℝ≥0))) P :=
    ⟨(measurable_sampleMean hMeas).aemeasurable,
      gaussian_sampleMean_distribution hn hσ hMeas hIndep hLaw⟩
  have hSE : standardError σ n ^ 2 ≠ 0 :=
    pow_ne_zero 2 (ne_of_gt (standardError_pos hn hσ))
  have hVar : ((NNReal.mk σ hσ.le ^ 2) / (n : ℝ≥0)) /
      NNReal.mk (standardError σ n ^ 2) (sq_nonneg _) = 1 := by
    apply NNReal.eq
    simp only [NNReal.coe_div, NNReal.coe_pow, NNReal.coe_mk,
      NNReal.coe_natCast, NNReal.coe_one]
    rw [← standardError_sq σ n, div_self hSE]
  unfold standardizedSampleMean
  simpa only [sub_self, zero_div, hVar] using
    gaussianReal_div_const (gaussianReal_sub_const hMean μ) (standardError σ n)

/-- **Exact standardization:** `(sampleMean X - μ) / (σ / sqrt n)` has
distribution `gaussianReal 0 1`, as an equality of probability measures. -/
theorem gaussian_standardizedSampleMean_distribution {n : ℕ} (hn : 0 < n)
    {X : Fin n → Ω → ℝ} {μ σ : ℝ} (hσ : 0 < σ)
    (hMeas : ∀ i, Measurable (X i)) (hIndep : iIndepFun X P)
    (hLaw : ∀ i, P.map (X i) = gaussianReal μ (NNReal.mk σ hσ.le ^ 2)) :
    P.map (standardizedSampleMean X μ σ) = gaussianReal 0 1 :=
  (hasLaw_standardizedSampleMean hn hσ hMeas hIndep hLaw).map_eq

end LeanStatInference
