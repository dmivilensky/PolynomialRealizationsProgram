import chebyshev1.Stochastic.MatrixQuadraticCovariance
import Mathlib.Probability.ConditionalExpectation
import Mathlib.Probability.Independence.Integration

/-! Fresh independent random matrices with only second moments. -/
set_option backward.isDefEq.respectTransparency false
namespace chebyshev1.Stochastic
noncomputable section
open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators

variable {Ω E : Type*} [mΩ : MeasurableSpace Ω]
variable [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
variable {μ : Measure Ω} [IsProbabilityMeasure μ]

omit [IsProbabilityMeasure μ] in
theorem indepFun_of_fresh {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    {m q : MeasurableSpace Ω} (hfresh : Indep q m μ)
    {X : Ω → α} {Y : Ω → β} (hX : Measurable[q] X) (hY : Measurable[m] Y) :
    IndepFun X Y μ := by
  let : MeasurableSpace Ω := mΩ
  rw [IndepFun_iff]
  intro A B hA hB
  exact (Indep_iff q m μ).mp hfresh A B (hX.comap_le A hA) (hY.comap_le B hB)

omit [CompleteSpace E] [IsProbabilityMeasure μ] in
theorem fresh_smul_integrable {m q : MeasurableSpace Ω} (hfresh : Indep q m μ)
    {X : Ω → E} {f : Ω → ℝ} (hX : StronglyMeasurable[q] X)
    (hf : StronglyMeasurable[m] f) (hiX : Integrable X μ) (hif : Integrable f μ) :
    Integrable (fun ω => f ω • X ω) μ := by
  let : MeasurableSpace Ω := mΩ
  borelize E
  exact (indepFun_of_fresh hfresh hX.measurable hf.measurable).symm.integrable_smul hif hiX

omit [CompleteSpace E] [IsProbabilityMeasure μ] in
/-- Independence makes the product L² using second moments of the two factors only. -/
theorem fresh_smul_memLp {m q : MeasurableSpace Ω} (hm : m ≤ mΩ) (hq : q ≤ mΩ)
    (hfresh : Indep q m μ) {X : Ω → E} {f : Ω → ℝ}
    (hX : StronglyMeasurable[q] X) (hf : StronglyMeasurable[m] f)
    (hX2 : MemLp X 2 μ) (hf2 : MemLp f 2 μ) :
    MemLp (fun ω => f ω • X ω) 2 μ := by
  let : MeasurableSpace Ω := mΩ
  have hiX := hX2.integrable_norm_pow (by norm_num : (2 : ℕ) ≠ 0)
  have hif := hf2.integrable_sq
  have hh := (indepFun_of_fresh hfresh (hX.norm.pow 2).measurable
    (hf.pow 2).measurable).symm.integrable_mul hif hiX
  apply (memLp_two_iff_integrable_sq_norm
    (((hf.mono hm).aestronglyMeasurable).smul (hX.mono hq).aestronglyMeasurable)).mpr
  convert hh using 1
  funext ω
  simp [norm_smul, Real.norm_eq_abs, mul_pow, sq_abs]

/-- Pulling a past factor out of the fresh conditional expectation. -/
theorem fresh_smul_condExp {m q : MeasurableSpace Ω} (hm : m ≤ mΩ) (hq : q ≤ mΩ)
    (hfresh : Indep q m μ) {X : Ω → E} {f : Ω → ℝ}
    (hX : StronglyMeasurable[q] X) (hf : StronglyMeasurable[m] f)
    (hiX : Integrable X μ) (hif : Integrable f μ) :
    μ[fun ω => f ω • X ω | m] =ᵐ[μ] (fun ω => f ω • (∫ x, X x ∂μ)) := by
  let : MeasurableSpace Ω := mΩ
  have hh := condExp_smul_of_aestronglyMeasurable_left hf.aestronglyMeasurable
    (fresh_smul_integrable hfresh hX hf hiX hif) hiX
  have hcond := condExp_indep_eq hq hm hX hfresh
  change μ[fun ω => f ω • X ω | m] =ᵐ[μ]
    (fun ω => f ω • μ[X | m] ω) at hh
  filter_upwards [hh, hcond] with ω hh hc
  simpa only [hc] using hh

end
end chebyshev1.Stochastic

namespace chebyshev1.Stochastic
noncomputable section
open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators RealInnerProductSpace
variable {Ω d : Type*} [mΩ : MeasurableSpace Ω] [Fintype d] [DecidableEq d]
variable {μ : Measure Ω}

def randomMatrixColumn (Z : Ω → Matrix d d ℝ) (j : d) (ω : Ω) : EuclideanSpace ℝ d :=
  WithLp.toLp 2 (fun i => Z ω i j)

def randomMatrixApply (Z : Ω → Matrix d d ℝ) (x : EuclideanSpace ℝ d) (ω : Ω) :
    EuclideanSpace ℝ d := WithLp.toLp 2 ((Z ω).mulVec (WithLp.ofLp x))

omit [DecidableEq d] in
theorem randomMatrixColumn_memLp (Z : Ω → Matrix d d ℝ)
    (hZ2 : ∀ i j, MemLp (fun ω => Z ω i j) 2 μ) (j : d) :
    MemLp (randomMatrixColumn Z j) 2 μ := by
  have h : MemLp (fun ω i => Z ω i j) 2 μ := MemLp.of_eval (fun i => hZ2 i j)
  exact h.continuousLinearMap_comp
    (PiLp.continuousLinearEquiv 2 ℝ (fun _ : d => ℝ)).symm.toContinuousLinearMap

omit [DecidableEq d] in
theorem randomMatrixColumn_stronglyMeasurable (Z : Ω → Matrix d d ℝ)
    (hZ : ∀ i j, StronglyMeasurable (fun ω => Z ω i j)) (j : d) :
    StronglyMeasurable (randomMatrixColumn Z j) := by
  have h : StronglyMeasurable (fun ω i => Z ω i j) :=
    (Measurable.of_eval (fun i => (hZ i j).measurable)).stronglyMeasurable
  exact (PiLp.continuousLinearEquiv 2 ℝ (fun _ : d => ℝ)).symm.continuous.comp_stronglyMeasurable h

omit mΩ [DecidableEq d] in
theorem randomMatrixApply_eq_sum (Z : Ω → Matrix d d ℝ) (x : EuclideanSpace ℝ d) (ω : Ω)
    (T : EuclideanSpace ℝ d →L[ℝ] EuclideanSpace ℝ d) :
    T (randomMatrixApply Z x ω) =
      ∑ j, WithLp.ofLp x j • T (randomMatrixColumn Z j ω) := by
  simp_rw [← map_smul]
  rw [← map_sum]
  congr 1
  apply WithLp.ofLp_injective
  ext i
  simp [randomMatrixApply, randomMatrixColumn, Matrix.mulVec, dotProduct,
    WithLp.ofLp_sum, mul_comm]

omit mΩ [DecidableEq d] in
theorem randomMatrixApply_norm_sq (Z : Ω → Matrix d d ℝ) (x : EuclideanSpace ℝ d) (ω : Ω)
    (T : EuclideanSpace ℝ d →L[ℝ] EuclideanSpace ℝ d) :
    ‖T (randomMatrixApply Z x ω)‖^2 = ∑ i, ∑ j,
      (WithLp.ofLp x i * WithLp.ofLp x j) *
        ⟪T (randomMatrixColumn Z i ω), T (randomMatrixColumn Z j ω)⟫ := by
  rw [randomMatrixApply_eq_sum, ← real_inner_self_eq_norm_sq]
  simp_rw [sum_inner, inner_sum, real_inner_smul_left, real_inner_smul_right]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

/-- The scalar quadratic observation of the covariance of `Z*x`, including correlated entries. -/
def independentMatrixObservation (Z : Ω → Matrix d d ℝ)
    (T : EuclideanSpace ℝ d →L[ℝ] EuclideanSpace ℝ d) :
    QuadraticForm ℝ (EuclideanSpace ℝ d) :=
  ∑ i, ∑ j, (∫ ω, ⟪T (randomMatrixColumn Z i ω), T (randomMatrixColumn Z j ω)⟫ ∂μ) •
    QuadraticMap.linMulLin (PiLp.proj (𝕜 := ℝ) 2 (fun _ : d => ℝ) i).toLinearMap
      (PiLp.proj (𝕜 := ℝ) 2 (fun _ : d => ℝ) j).toLinearMap

omit [DecidableEq d] in
theorem independentMatrixObservation_apply (Z : Ω → Matrix d d ℝ)
    (T : EuclideanSpace ℝ d →L[ℝ] EuclideanSpace ℝ d) (x : EuclideanSpace ℝ d) :
    independentMatrixObservation (μ := μ) Z T x = ∑ i, ∑ j,
      (WithLp.ofLp x i * WithLp.ofLp x j) *
        (∫ ω, ⟪T (randomMatrixColumn Z i ω), T (randomMatrixColumn Z j ω)⟫ ∂μ) := by
  simp [independentMatrixObservation, mul_comm]

omit [DecidableEq d] in
/-- The observation is the actual expected squared matrix response, with only second moments. -/
theorem independentMatrixObservation_eq_integral (Z : Ω → Matrix d d ℝ)
    (hZ2 : ∀ i j, MemLp (fun ω => Z ω i j) 2 μ)
    (T : EuclideanSpace ℝ d →L[ℝ] EuclideanSpace ℝ d) (x : EuclideanSpace ℝ d) :
    independentMatrixObservation (μ := μ) Z T x =
      ∫ ω, ‖T (randomMatrixApply Z x ω)‖^2 ∂μ := by
  have hint : ∀ i j, Integrable (fun ω => (WithLp.ofLp x i * WithLp.ofLp x j) *
      ⟪T (randomMatrixColumn Z i ω), T (randomMatrixColumn Z j ω)⟫) μ := by
    intro i j
    exact (integrable_inner_of_memLp_two
      ((randomMatrixColumn_memLp Z hZ2 i).continuousLinearMap_comp T)
      ((randomMatrixColumn_memLp Z hZ2 j).continuousLinearMap_comp T)).const_mul _
  simp_rw [randomMatrixApply_norm_sq]
  rw [integral_finsetSum _ (fun i _ => integrable_finsetSum _ (fun j _ => hint i j))]
  rw [independentMatrixObservation_apply]
  apply Finset.sum_congr rfl
  intro i _
  rw [integral_finsetSum _ (fun j _ => hint i j)]
  simp_rw [integral_const_mul]

omit [DecidableEq d] in
theorem independentMatrixObservation_nonneg (Z : Ω → Matrix d d ℝ)
    (hZ2 : ∀ i j, MemLp (fun ω => Z ω i j) 2 μ)
    (T : EuclideanSpace ℝ d →L[ℝ] EuclideanSpace ℝ d) (x : EuclideanSpace ℝ d) :
    0 ≤ independentMatrixObservation (μ := μ) Z T x := by
  rw [independentMatrixObservation_eq_integral Z hZ2 T x]
  exact integral_nonneg (fun _ => sq_nonneg _)

omit [DecidableEq d] in
theorem randomMatrixColumn_mean_zero [IsFiniteMeasure μ] (Z : Ω → Matrix d d ℝ)
    (hZ2 : ∀ i j, MemLp (fun ω => Z ω i j) 2 μ)
    (hmean : ∀ i j, (∫ ω, Z ω i j ∂μ) = 0) (j : d) :
    (∫ ω, randomMatrixColumn Z j ω ∂μ) = 0 := by
  apply WithLp.ofLp_injective
  ext i
  change (PiLp.proj (𝕜 := ℝ) 2 (fun _ : d => ℝ) i)
    (∫ ω, randomMatrixColumn Z j ω ∂μ) = 0
  rw [← (PiLp.proj (𝕜 := ℝ) 2 (fun _ : d => ℝ) i).integral_comp_comm
    ((randomMatrixColumn_memLp Z hZ2 j).integrable (by norm_num))]
  exact hmean i j

omit [DecidableEq d] in
theorem randomMatrixApply_stronglyMeasurable (Z : Ω → Matrix d d ℝ)
    (hZ : ∀ i j, StronglyMeasurable (fun ω => Z ω i j))
    (v : Ω → EuclideanSpace ℝ d) (hv : StronglyMeasurable v) :
    StronglyMeasurable (fun ω => randomMatrixApply Z (v ω) ω) := by
  have h : StronglyMeasurable (fun ω => ∑ j, WithLp.ofLp (v ω) j • randomMatrixColumn Z j ω) := by
    apply Finset.stronglyMeasurable_fun_sum
    intro j _
    exact ((PiLp.proj (𝕜 := ℝ) 2 (fun _ : d => ℝ) j).continuous.comp_stronglyMeasurable hv).smul
      (randomMatrixColumn_stronglyMeasurable Z hZ j)
  convert h using 1
  funext ω
  simpa only [ContinuousLinearMap.id_apply] using
    (randomMatrixApply_eq_sum Z (v ω) ω (ContinuousLinearMap.id ℝ _))

variable [IsProbabilityMeasure μ]

omit [DecidableEq d] [IsProbabilityMeasure μ] in
/-- A fresh L² matrix acting on a past L² vector is L² without bounded entries. -/
theorem randomMatrixApply_memLp (Z : Ω → Matrix d d ℝ)
    (m q : MeasurableSpace Ω) (hm : m ≤ mΩ) (hq : q ≤ mΩ) (hfresh : Indep q m μ)
    (hZ : ∀ i j, StronglyMeasurable[q] (fun ω => Z ω i j))
    (hZ2 : ∀ i j, MemLp (fun ω => Z ω i j) 2 μ)
    (v : Ω → EuclideanSpace ℝ d) (hv : StronglyMeasurable[m] v) (hv2 : MemLp v 2 μ) :
    MemLp (fun ω => randomMatrixApply Z (v ω) ω) 2 μ := by
  let : MeasurableSpace Ω := mΩ
  have hsum : MemLp (fun ω => ∑ j, WithLp.ofLp (v ω) j • randomMatrixColumn Z j ω) 2 μ := by
    apply memLp_finsetSum
    intro j _
    exact fresh_smul_memLp hm hq hfresh (randomMatrixColumn_stronglyMeasurable (mΩ := q) Z hZ j)
      ((PiLp.proj (𝕜 := ℝ) 2 (fun _ : d => ℝ) j).continuous.comp_stronglyMeasurable hv)
      (randomMatrixColumn_memLp Z hZ2 j)
      (hv2.continuousLinearMap_comp (PiLp.proj (𝕜 := ℝ) 2 (fun _ : d => ℝ) j))
  convert hsum using 1
  funext ω
  simpa only [ContinuousLinearMap.id_apply] using
    (randomMatrixApply_eq_sum Z (v ω) ω (ContinuousLinearMap.id ℝ _))

omit [DecidableEq d] in
/-- Exact conditional moments of a fresh centered random matrix at the actual past state. -/
theorem randomMatrixApply_conditional_moments (Z : Ω → Matrix d d ℝ)
    (m q : MeasurableSpace Ω) (hm : m ≤ mΩ) (hq : q ≤ mΩ) (hfresh : Indep q m μ)
    (hZ : ∀ i j, StronglyMeasurable[q] (fun ω => Z ω i j))
    (hZ2 : ∀ i j, MemLp (fun ω => Z ω i j) 2 μ)
    (hmean : ∀ i j, (∫ ω, Z ω i j ∂μ) = 0)
    (v : Ω → EuclideanSpace ℝ d) (hv : StronglyMeasurable[m] v) (hv2 : MemLp v 2 μ)
    (T : EuclideanSpace ℝ d →L[ℝ] EuclideanSpace ℝ d) :
    μ[fun ω => T (randomMatrixApply Z (v ω) ω) | m] =ᵐ[μ] 0 ∧
    μ[fun ω => ‖T (randomMatrixApply Z (v ω) ω)‖^2 | m] =ᵐ[μ]
      (fun ω => independentMatrixObservation (mΩ := mΩ) (μ := μ) Z T (v ω)) := by
  let : MeasurableSpace Ω := mΩ
  let U := fun j ω => T (randomMatrixColumn Z j ω)
  let f := fun j ω => WithLp.ofLp (v ω) j
  have hU (j : d) : StronglyMeasurable[q] (U j) :=
    T.continuous.comp_stronglyMeasurable (randomMatrixColumn_stronglyMeasurable (mΩ := q) Z hZ j)
  have hU2 (j : d) : MemLp (U j) 2 μ :=
    (randomMatrixColumn_memLp Z hZ2 j).continuousLinearMap_comp T
  have hf (j : d) : StronglyMeasurable[m] (f j) :=
    (PiLp.proj (𝕜 := ℝ) 2 (fun _ : d => ℝ) j).continuous.comp_stronglyMeasurable hv
  have hf2 (j : d) : MemLp (f j) 2 μ :=
    hv2.continuousLinearMap_comp (PiLp.proj (𝕜 := ℝ) 2 (fun _ : d => ℝ) j)
  have hterm2 (j : d) : MemLp (fun ω => f j ω • U j ω) 2 μ :=
    fresh_smul_memLp hm hq hfresh (hU j) (hf j) (hU2 j) (hf2 j)
  have htermint (j : d) : Integrable (fun ω => f j ω • U j ω) μ :=
    (hterm2 j).integrable (by norm_num)
  have hUmean (j : d) : (∫ ω, U j ω ∂μ) = 0 := by
    rw [T.integral_comp_comm ((randomMatrixColumn_memLp Z hZ2 j).integrable (by norm_num)),
      randomMatrixColumn_mean_zero Z hZ2 hmean, map_zero]
  have htermcond (j : d) : μ[fun ω => f j ω • U j ω | m] =ᵐ[μ] 0 := by
    have h := fresh_smul_condExp hm hq hfresh (hU j) (hf j)
      ((hU2 j).integrable (by norm_num)) ((hf2 j).integrable (by norm_num))
    simpa only [hUmean, smul_zero, Pi.zero_def] using h
  constructor
  · have hh := condExp_finsetSum (s := Finset.univ) (fun j _ => htermint j) m
    have heq : (fun ω => T (randomMatrixApply Z (v ω) ω)) =
        ∑ j, (fun ω => f j ω • U j ω) := by
      funext ω
      simp only [Finset.sum_apply, U, f]
      exact randomMatrixApply_eq_sum Z (v ω) ω T
    rw [heq]
    filter_upwards [hh, ae_all_iff.mpr htermcond] with ω hh hall
    rw [hh]
    simp only [Finset.sum_apply]
    exact Finset.sum_eq_zero (fun j _ => hall j)
  · have hcint (i j : d) : Integrable (fun ω => ⟪U i ω, U j ω⟫) μ :=
      integrable_inner_of_memLp_two (hU2 i) (hU2 j)
    have hpint (i j : d) : Integrable (fun ω => f i ω*f j ω) μ :=
      (hf2 i).integrable_mul (hf2 j)
    have hint (i j : d) : Integrable (fun ω => (f i ω*f j ω)*⟪U i ω,U j ω⟫) μ :=
      fresh_smul_integrable hfresh ((hU i).inner (hU j)) ((hf i).mul (hf j))
        (hcint i j) (hpint i j)
    have hcond (i j : d) :
        μ[fun ω => (f i ω*f j ω)*⟪U i ω,U j ω⟫ | m] =ᵐ[μ]
          (fun ω => (f i ω*f j ω)*(∫ x, ⟪U i x,U j x⟫ ∂μ)) :=
      fresh_smul_condExp hm hq hfresh ((hU i).inner (hU j)) ((hf i).mul (hf j))
        (hcint i j) (hpint i j)
    have heq : (fun ω => ‖T (randomMatrixApply Z (v ω) ω)‖^2) =
        ∑ i, ∑ j, (fun ω => (f i ω*f j ω)*⟪U i ω,U j ω⟫) := by
      funext ω
      simp only [Finset.sum_apply, f, U]
      exact randomMatrixApply_norm_sq Z (v ω) ω T
    rw [heq]
    have ho := condExp_finsetSum (s := Finset.univ)
      (f := fun i => ∑ j, (fun ω => (f i ω*f j ω)*⟪U i ω,U j ω⟫))
      (fun i _ => integrable_finsetSum' Finset.univ (fun j _ => hint i j)) m
    have hi (i : d) := condExp_finsetSum (s := Finset.univ) (fun j _ => hint i j) m
    filter_upwards [ho, ae_all_iff.mpr hi,
      ae_all_iff.mpr (fun i => ae_all_iff.mpr (hcond i))] with ω ho hi hp
    rw [ho]
    simp only [Finset.sum_apply]
    simp_rw [hi]
    simp only [Finset.sum_apply]
    simp_rw [hp]
    exact (independentMatrixObservation_apply Z T (v ω)).symm

end
end chebyshev1.Stochastic
