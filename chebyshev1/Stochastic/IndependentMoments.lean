import Mathlib.Probability.Independence.Integration
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Algebra.BigOperators.Pi

/-!
Square-free monomials in independent centered unit-variance variables are
orthonormal. The proof uses only first and second moments, not boundedness or
higher moments of the noise.
-/
namespace chebyshev1.Stochastic
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped BigOperators

variable {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι] [DecidableEq ι]
variable {μ : Measure Ω} [IsProbabilityMeasure μ] {z : ι → Ω → ℝ}

/-- A square-free scalar noise monomial, with the empty monomial equal to one. -/
def noiseMonomial (z : ι → Ω → ℝ) (S : Finset ι) (ω : Ω) : ℝ :=
  ∏ i, if i ∈ S then z i ω else 1

omit [Fintype ι] in
theorem independent_integrable_prod (hz : iIndepFun z μ)
    (hm : ∀ i, Measurable (z i)) (hi : ∀ i, Integrable (z i) μ) (S : Finset ι) :
    Integrable (fun ω => ∏ i ∈ S, z i ω) μ := by
  induction S using Finset.induction_on with
  | empty => simp
  | @insert i S hnot ih =>
    have hp : (∏ j ∈ S, z j) = (fun ω => ∏ j ∈ S, z j ω) := by
      funext ω
      exact Finset.prod_apply ω S z
    have ih' : Integrable (∏ j ∈ S, z j) μ := by rwa [hp]
    have h := (hz.indepFun_finsetProd_of_notMem hm hnot).symm.integrable_mul (hi i) ih'
    change Integrable (fun ω => z i ω * (∏ j ∈ S, z j) ω) μ at h
    simpa only [Finset.prod_insert hnot, Finset.prod_apply] using h

theorem integrable_noiseMonomial_mul (hz : iIndepFun z μ)
    (hm : ∀ i, Measurable (z i)) (hi : ∀ i, Integrable (z i) μ)
    (hi2 : ∀ i, Integrable (fun ω => z i ω ^ 2) μ) (S T : Finset ι) :
    Integrable (fun ω => noiseMonomial z S ω * noiseMonomial z T ω) μ := by
  let f : ι → ℝ → ℝ := fun i x =>
    (if i ∈ S then x else 1) * (if i ∈ T then x else 1)
  have hf : ∀ i, Measurable (f i) := by
    intro i
    by_cases hs : i ∈ S <;> by_cases ht : i ∈ T <;> simp [f, hs, ht] <;> fun_prop
  have hfi : ∀ i, Integrable (fun ω => f i (z i ω)) μ := by
    intro i
    by_cases hs : i ∈ S <;> by_cases ht : i ∈ T <;>
      simp [f, hs, ht, ← sq]
    all_goals first | exact hi2 i | exact hi i
  have h := independent_integrable_prod (hz.comp f hf)
    (fun i => (hf i).comp (hm i)) hfi Finset.univ
  simpa only [Function.comp_apply, f, noiseMonomial, ← Finset.prod_mul_distrib] using h

/-- Distinct subsets are orthogonal, and each monomial has squared expectation one. -/
theorem integral_noiseMonomial_mul (hz : iIndepFun z μ)
    (hm : ∀ i, Measurable (z i))
    (hmean : ∀ i, ∫ ω, z i ω ∂μ = 0)
    (hvar : ∀ i, ∫ ω, z i ω ^ 2 ∂μ = 1) (S T : Finset ι) :
    (∫ ω, noiseMonomial z S ω * noiseMonomial z T ω ∂μ) =
      if S = T then 1 else 0 := by
  let f : ι → ℝ → ℝ := fun i x =>
    (if i ∈ S then x else 1) * (if i ∈ T then x else 1)
  have hf : ∀ i, Measurable (f i) := by
    intro i
    by_cases hs : i ∈ S <;> by_cases ht : i ∈ T <;> simp [f, hs, ht] <;> fun_prop
  have h := hz.integral_fun_prod_comp (fun i => (hm i).aemeasurable)
    (fun i => (hf i).aestronglyMeasurable)
  change (∫ ω, ∏ i, f i (z i ω) ∂μ) = ∏ i, ∫ ω, f i (z i ω) ∂μ at h
  rw [show (fun ω => noiseMonomial z S ω * noiseMonomial z T ω) =
      (fun ω => ∏ i, f i (z i ω)) by
    funext ω
    simp only [noiseMonomial, f, Finset.prod_mul_distrib]]
  rw [h]
  by_cases hST : S = T
  · subst T
    simp only [ite_true]
    apply Finset.prod_eq_one
    intro i _
    by_cases hi : i ∈ S <;> simp [f, hi, ← sq, hvar]
  · simp only [hST, ite_false]
    have hn : ¬ ∀ i, i ∈ S ↔ i ∈ T := fun h => hST (Finset.ext h)
    obtain ⟨i, hi⟩ := not_forall.mp hn
    apply Finset.prod_eq_zero (Finset.mem_univ i)
    by_cases hs : i ∈ S <;> by_cases ht : i ∈ T <;>
      simp_all [f]

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
open scoped RealInnerProductSpace

/-- Parseval's identity for any finite square-free noise expansion. -/
theorem integral_noise_sum_norm_sq (hz : iIndepFun z μ)
    (hm : ∀ i, Measurable (z i)) (hi : ∀ i, Integrable (z i) μ)
    (hi2 : ∀ i, Integrable (fun ω => z i ω ^ 2) μ)
    (hmean : ∀ i, ∫ ω, z i ω ∂μ = 0)
    (hvar : ∀ i, ∫ ω, z i ω ^ 2 ∂μ = 1)
    (A : Finset (Finset ι)) (v : Finset ι → E) :
    (∫ ω, ‖∑ S ∈ A, noiseMonomial z S ω • v S‖ ^ 2 ∂μ) =
      ∑ S ∈ A, ‖v S‖ ^ 2 := by
  have hint : ∀ S T, Integrable (fun ω =>
      (noiseMonomial z S ω * noiseMonomial z T ω) * ⟪v S, v T⟫) μ := by
    intro S T
    exact (integrable_noiseMonomial_mul hz hm hi hi2 S T).mul_const _
  have heq : (fun ω => ‖∑ S ∈ A, noiseMonomial z S ω • v S‖ ^ 2) =
      (fun ω => ∑ S ∈ A, ∑ T ∈ A,
        (noiseMonomial z S ω * noiseMonomial z T ω) * ⟪v S, v T⟫) := by
    funext ω
    rw [← real_inner_self_eq_norm_sq]
    simp_rw [sum_inner, inner_sum, real_inner_smul_left, real_inner_smul_right]
    apply Finset.sum_congr rfl
    intro S _
    apply Finset.sum_congr rfl
    intro T _
    ring
  rw [heq, integral_finsetSum A (fun S _ => integrable_finsetSum A (fun T _ => hint S T))]
  apply Finset.sum_congr rfl
  intro S hS
  rw [integral_finsetSum A (fun T _ => hint S T)]
  simp_rw [integral_mul_const, integral_noiseMonomial_mul hz hm hmean hvar]
  simp [hS]

/-- Coefficients of every even noise power are sums of squares and hence nonnegative. -/
def noiseEnergyCoefficient (v : Finset ι → E) (k : ℕ) : ℝ :=
  ∑ S ∈ Finset.univ.powersetCard k, ‖v S‖ ^ 2

omit [DecidableEq ι] [InnerProductSpace ℝ E] in
theorem noiseEnergyCoefficient_nonneg (v : Finset ι → E) (k : ℕ) :
    0 ≤ noiseEnergyCoefficient v k := by
  exact Finset.sum_nonneg (fun _ _ => sq_nonneg _)

/-- Exact second-moment polynomial; no moment beyond variance enters its coefficients. -/
theorem integral_scaled_noise_sum_norm_sq (hz : iIndepFun z μ)
    (hm : ∀ i, Measurable (z i)) (hi : ∀ i, Integrable (z i) μ)
    (hi2 : ∀ i, Integrable (fun ω => z i ω ^ 2) μ)
    (hmean : ∀ i, ∫ ω, z i ω ∂μ = 0)
    (hvar : ∀ i, ∫ ω, z i ω ^ 2 ∂μ = 1)
    (v : Finset ι → E) (σ : ℝ) :
    (∫ ω, ‖∑ S ∈ Finset.univ.powerset,
      noiseMonomial z S ω • (σ ^ S.card • v S)‖ ^ 2 ∂μ) =
      ∑ k ∈ Finset.range (Fintype.card ι + 1), σ ^ (2*k) * noiseEnergyCoefficient v k := by
  rw [integral_noise_sum_norm_sq hz hm hi hi2 hmean hvar]
  rw [Finset.sum_powerset]
  apply Finset.sum_congr rfl
  intro k _
  rw [noiseEnergyCoefficient, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro S hS
  obtain ⟨_, hcard⟩ := Finset.mem_powersetCard.mp hS
  rw [norm_smul, Real.norm_eq_abs, mul_pow, sq_abs, hcard, ← pow_mul, Nat.mul_comm k 2]

section FiniteSubsets

variable {κ : Type*} [DecidableEq κ] {w : κ → Ω → ℝ}

/-- The same monomial for a finite subset of a possibly infinite time index. -/
def finiteNoiseMonomial (w : κ → Ω → ℝ) (S : Finset κ) (ω : Ω) : ℝ :=
  ∏ i ∈ S, w i ω

private def withinSubset (U S : Finset κ) : Finset U :=
  Finset.univ.filter (fun i => i.val ∈ S)

omit [MeasurableSpace Ω] in
private theorem finiteNoiseMonomial_restrict (U S : Finset κ) (hS : S ⊆ U) (ω : Ω) :
    noiseMonomial (fun i : U => w i.val) (withinSubset U S) ω =
      finiteNoiseMonomial w S ω := by
  simp only [noiseMonomial, withinSubset, Finset.mem_filter, Finset.mem_univ, true_and,
    finiteNoiseMonomial]
  rw [Finset.prod_coe_sort U (fun i => if i ∈ S then w i ω else 1),
    Finset.prod_ite_mem, Finset.inter_eq_right.mpr hS]

private theorem withinSubset_inj (U S T : Finset κ) (hS : S ⊆ U) (hT : T ⊆ U) :
    withinSubset U S = withinSubset U T ↔ S = T := by
  constructor
  · intro h
    ext i
    constructor
    · intro hi
      have hm : (⟨i, hS hi⟩ : U) ∈ withinSubset U S := by simp [withinSubset, hi]
      rw [h] at hm
      simpa only [withinSubset, Finset.mem_filter, Finset.mem_univ, true_and] using hm
    · intro hi
      have hm : (⟨i, hT hi⟩ : U) ∈ withinSubset U T := by simp [withinSubset, hi]
      rw [← h] at hm
      simpa only [withinSubset, Finset.mem_filter, Finset.mem_univ, true_and] using hm
  · exact congrArg (withinSubset U)

theorem integrable_finiteNoiseMonomial_mul (hw : iIndepFun w μ)
    (hm : ∀ i, Measurable (w i)) (hi : ∀ i, Integrable (w i) μ)
    (hi2 : ∀ i, Integrable (fun ω => w i ω ^ 2) μ) (S T : Finset κ) :
    Integrable (fun ω => finiteNoiseMonomial w S ω * finiteNoiseMonomial w T ω) μ := by
  let U := S ∪ T
  have h := integrable_noiseMonomial_mul (hw.restrict U)
    (fun i => hm i.val) (fun i => hi i.val) (fun i => hi2 i.val)
    (withinSubset U S) (withinSubset U T)
  change Integrable (fun ω => noiseMonomial (fun i : U => w i.val) (withinSubset U S) ω *
    noiseMonomial (fun i : U => w i.val) (withinSubset U T) ω) μ at h
  simpa only [finiteNoiseMonomial_restrict U S Finset.subset_union_left,
    finiteNoiseMonomial_restrict U T Finset.subset_union_right] using h

/-- Orthogonality for an arbitrary finite collection of insertion times. -/
theorem integral_finiteNoiseMonomial_mul (hw : iIndepFun w μ)
    (hm : ∀ i, Measurable (w i))
    (hmean : ∀ i, ∫ ω, w i ω ∂μ = 0)
    (hvar : ∀ i, ∫ ω, w i ω ^ 2 ∂μ = 1) (S T : Finset κ) :
    (∫ ω, finiteNoiseMonomial w S ω * finiteNoiseMonomial w T ω ∂μ) =
      if S = T then 1 else 0 := by
  let U := S ∪ T
  have h := integral_noiseMonomial_mul (hw.restrict U)
    (fun i => hm i.val) (fun i => hmean i.val) (fun i => hvar i.val)
    (withinSubset U S) (withinSubset U T)
  change (∫ ω, noiseMonomial (fun i : U => w i.val) (withinSubset U S) ω *
    noiseMonomial (fun i : U => w i.val) (withinSubset U T) ω ∂μ) = _ at h
  simpa only [finiteNoiseMonomial_restrict U S Finset.subset_union_left,
    finiteNoiseMonomial_restrict U T Finset.subset_union_right,
    withinSubset_inj U S T Finset.subset_union_left Finset.subset_union_right] using h

theorem integral_finiteNoiseMonomial (hw : iIndepFun w μ)
    (hm : ∀ i, Measurable (w i))
    (hmean : ∀ i, ∫ ω, w i ω ∂μ = 0)
    (hvar : ∀ i, ∫ ω, w i ω ^ 2 ∂μ = 1) (S : Finset κ) :
    (∫ ω, finiteNoiseMonomial w S ω ∂μ) = if S = ∅ then 1 else 0 := by
  simpa only [finiteNoiseMonomial, Finset.prod_empty, mul_one] using
    integral_finiteNoiseMonomial_mul hw hm hmean hvar S ∅

/-- The expected square-free expansion is its deterministic empty-subset coefficient. -/
theorem integral_finiteNoise_sum [CompleteSpace E] (hw : iIndepFun w μ)
    (hm : ∀ i, Measurable (w i)) (hi : ∀ i, Integrable (w i) μ)
    (hmean : ∀ i, ∫ ω, w i ω ∂μ = 0)
    (hvar : ∀ i, ∫ ω, w i ω ^ 2 ∂μ = 1)
    (A : Finset (Finset κ)) (hA : ∅ ∈ A) (v : Finset κ → E) :
    (∫ ω, ∑ S ∈ A, finiteNoiseMonomial w S ω • v S ∂μ) = v ∅ := by
  have hv : ∀ S, Integrable (fun ω => finiteNoiseMonomial w S ω • v S) μ := by
    intro S
    exact (independent_integrable_prod hw hm hi S).smul_const (v S)
  rw [integral_finsetSum A (fun S _ => hv S)]
  simp_rw [integral_smul_const, integral_finiteNoiseMonomial hw hm hmean hvar]
  simp [hA]

/-- Parseval's identity for finitely many subsets of an unrestricted time index. -/
theorem integral_finiteNoise_sum_norm_sq (hw : iIndepFun w μ)
    (hm : ∀ i, Measurable (w i)) (hi : ∀ i, Integrable (w i) μ)
    (hi2 : ∀ i, Integrable (fun ω => w i ω ^ 2) μ)
    (hmean : ∀ i, ∫ ω, w i ω ∂μ = 0)
    (hvar : ∀ i, ∫ ω, w i ω ^ 2 ∂μ = 1)
    (A : Finset (Finset κ)) (v : Finset κ → E) :
    (∫ ω, ‖∑ S ∈ A, finiteNoiseMonomial w S ω • v S‖ ^ 2 ∂μ) =
      ∑ S ∈ A, ‖v S‖ ^ 2 := by
  have hint : ∀ S T, Integrable (fun ω =>
      (finiteNoiseMonomial w S ω * finiteNoiseMonomial w T ω) * ⟪v S, v T⟫) μ := by
    intro S T
    exact (integrable_finiteNoiseMonomial_mul hw hm hi hi2 S T).mul_const _
  have heq : (fun ω => ‖∑ S ∈ A, finiteNoiseMonomial w S ω • v S‖ ^ 2) =
      (fun ω => ∑ S ∈ A, ∑ T ∈ A,
        (finiteNoiseMonomial w S ω * finiteNoiseMonomial w T ω) * ⟪v S, v T⟫) := by
    funext ω
    rw [← real_inner_self_eq_norm_sq]
    simp_rw [sum_inner, inner_sum, real_inner_smul_left, real_inner_smul_right]
    apply Finset.sum_congr rfl
    intro S _
    apply Finset.sum_congr rfl
    intro T _
    ring
  rw [heq, integral_finsetSum A (fun S _ => integrable_finsetSum A (fun T _ => hint S T))]
  apply Finset.sum_congr rfl
  intro S hS
  rw [integral_finsetSum A (fun T _ => hint S T)]
  simp_rw [integral_mul_const, integral_finiteNoiseMonomial_mul hw hm hmean hvar]
  simp [hS]

/-- Removing the empty subset centers the expansion exactly. -/
theorem integral_finiteNoise_centered_sum_norm_sq (hw : iIndepFun w μ)
    (hm : ∀ i, Measurable (w i)) (hi : ∀ i, Integrable (w i) μ)
    (hi2 : ∀ i, Integrable (fun ω => w i ω ^ 2) μ)
    (hmean : ∀ i, ∫ ω, w i ω ∂μ = 0)
    (hvar : ∀ i, ∫ ω, w i ω ^ 2 ∂μ = 1)
    (A : Finset (Finset κ)) (hA : ∅ ∈ A) (v : Finset κ → E) :
    (∫ ω, ‖(∑ S ∈ A, finiteNoiseMonomial w S ω • v S) - v ∅‖ ^ 2 ∂μ) =
      ∑ S ∈ A.erase ∅, ‖v S‖ ^ 2 := by
  have heq : ∀ ω, (∑ S ∈ A, finiteNoiseMonomial w S ω • v S) - v ∅ =
      ∑ S ∈ A.erase ∅, finiteNoiseMonomial w S ω • v S := by
    intro ω
    rw [← Finset.sum_erase_add _ _ hA]
    simp [finiteNoiseMonomial]
  simp_rw [heq]
  exact integral_finiteNoise_sum_norm_sq hw hm hi hi2 hmean hvar _ _

end FiniteSubsets

end
end chebyshev1.Stochastic
