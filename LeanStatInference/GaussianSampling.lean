module

public import Mathlib.Probability.Distributions.Gaussian.Real

-- The Mathlib-specific copyright header convention is not a project requirement.
set_option linter.style.header false

/-!
# Exact Gaussian sampling distribution

`gaussianReal μ v` is parametrized by its mean and **variance**. Independence
throughout is mutual independence (`iIndepFun`), not pairwise independence.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal

namespace LeanStatInference

variable {Ω : Type*} [MeasurableSpace Ω]

/-- The arithmetic mean of a finite real sample. The distribution theorem
below requires `0 < n`; the definition itself uses Lean's total division. -/
noncomputable def sampleMean {n : ℕ} (X : Fin n → Ω → ℝ) : Ω → ℝ :=
  fun ω ↦ (∑ i, X i ω) / (n : ℝ)

/-- Finite sums of measurable observations are measurable. -/
theorem measurable_sampleSum {n : ℕ} {X : Fin n → Ω → ℝ}
    (hX : ∀ i, Measurable (X i)) : Measurable (fun ω ↦ ∑ i, X i ω) := by
  fun_prop

/-- The sample mean is a measurable random variable. -/
theorem measurable_sampleMean {n : ℕ} {X : Fin n → Ω → ℝ}
    (hX : ∀ i, Measurable (X i)) : Measurable (sampleMean X) := by
  unfold sampleMean
  fun_prop

variable {P : Measure Ω}

/-- Integrability follows from the Gaussian law, so it need not be an
additional hypothesis of the sampling-distribution theorem. -/
theorem integrable_of_hasLaw_gaussian {Y : Ω → ℝ} {μ : ℝ} {v : ℝ≥0}
    (hLaw : HasLaw Y (gaussianReal μ v) P) : Integrable Y P := by
  exact memLp_one_iff_integrable.mp (hLaw.memLp (memLp_id_gaussianReal 1))

variable [IsProbabilityMeasure P]

/-- An explicit-parameter finite-sum law, proved by adjoining one independent
observation at a time. The summands need not have identical distributions. -/
theorem hasLaw_gaussian_finset_sum {ι : Type*} {X : ι → Ω → ℝ}
    {m : ι → ℝ} {v : ι → ℝ≥0} (hIndep : iIndepFun X P)
    (hLaw : ∀ i, HasLaw (X i) (gaussianReal (m i) (v i)) P) (s : Finset ι) :
    HasLaw (fun ω ↦ ∑ i ∈ s, X i ω)
      (gaussianReal (∑ i ∈ s, m i) (∑ i ∈ s, v i)) P := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      refine ⟨by simp, ?_⟩
      simp [gaussianReal_zero_var, Measure.map_const]
  | @insert i s hi ih =>
      have hIS : IndepFun (X i) (fun ω ↦ ∑ j ∈ s, X j ω) P := by
        simpa only [Finset.sum_fn] using
          (hIndep.indepFun_finsetSum_of_notMem₀ (fun j ↦ (hLaw j).aemeasurable) hi).symm
      have hAdd : HasLaw (fun ω ↦ X i ω + ∑ j ∈ s, X j ω)
          (gaussianReal (m i + ∑ j ∈ s, m j) (v i + ∑ j ∈ s, v j)) P :=
        ⟨(hLaw i).aemeasurable.add ih.aemeasurable,
          gaussianReal_add_gaussianReal_of_indepFun hIS (hLaw i) ih⟩
      simpa only [Finset.sum_insert hi] using hAdd

/-- The sum of `n` mutually independent observations with the same Gaussian
law has mean `n * μ` and variance `n * v`. This includes the empty sum. -/
theorem hasLaw_gaussian_sampleSum {n : ℕ} {X : Fin n → Ω → ℝ}
    {μ : ℝ} {v : ℝ≥0} (hIndep : iIndepFun X P)
    (hLaw : ∀ i, HasLaw (X i) (gaussianReal μ v) P) :
    HasLaw (fun ω ↦ ∑ i, X i ω) (gaussianReal ((n : ℝ) * μ) ((n : ℝ≥0) * v)) P := by
  simpa using hasLaw_gaussian_finset_sum hIndep hLaw Finset.univ

/-- Exact sample-mean law in Mathlib's variance parametrization. It also
allows zero population variance; positivity is imposed in the main theorem. -/
theorem hasLaw_gaussian_sampleMean {n : ℕ} (hn : 0 < n) {X : Fin n → Ω → ℝ}
    {μ : ℝ} {v : ℝ≥0} (hIndep : iIndepFun X P)
    (hLaw : ∀ i, HasLaw (X i) (gaussianReal μ v) P) :
    HasLaw (sampleMean X) (gaussianReal μ (v / (n : ℝ≥0))) P := by
  have hnR : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt hn)
  have hMean : (n : ℝ) * μ / (n : ℝ) = μ := by
    field_simp
  have hVar : ((n : ℝ≥0) * v) / NNReal.mk ((n : ℝ) ^ 2) (sq_nonneg _) =
      v / (n : ℝ≥0) := by
    apply NNReal.eq
    simp only [NNReal.coe_div, NNReal.coe_mul, NNReal.coe_natCast, NNReal.coe_mk]
    field_simp
  unfold sampleMean
  simpa only [hMean, hVar] using
    gaussianReal_div_const (hasLaw_gaussian_sampleSum hIndep hLaw) (n : ℝ)

/-- **Exact Gaussian sampling distribution.** For a positive sample size and
positive real population standard deviation, the law of the sample mean is
`Gaussian(μ, σ² / n)`. Equal marginal laws encode identical distribution. -/
theorem gaussian_sampleMean_distribution {n : ℕ} (hn : 0 < n)
    {X : Fin n → Ω → ℝ} {μ σ : ℝ} (hσ : 0 < σ)
    (hMeas : ∀ i, Measurable (X i)) (hIndep : iIndepFun X P)
    (hLaw : ∀ i, P.map (X i) = gaussianReal μ (NNReal.mk σ hσ.le ^ 2)) :
    P.map (sampleMean X) =
      gaussianReal μ ((NNReal.mk σ hσ.le ^ 2) / (n : ℝ≥0)) :=
  (hasLaw_gaussian_sampleMean hn hIndep
    (fun i ↦ ⟨(hMeas i).aemeasurable, hLaw i⟩)).map_eq

end LeanStatInference
