import chebyshev1.Stochastic.IndependentMoments

/-! Square-free noise moments using only the samples before the supplied horizon. -/
namespace chebyshev1.Stochastic
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped BigOperators RealInnerProductSpace
variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
variable {z : ℕ → Ω → ℝ} {N : ℕ}

private def restrictedSubset (U S : Finset ℕ) : Finset U :=
  Finset.univ.filter (fun i => i.val∈S)

omit [MeasurableSpace Ω] in
private theorem monomial_restricted (U S : Finset ℕ) (hS : S⊆U) (ω : Ω) :
    noiseMonomial (fun i : U => z i.val) (restrictedSubset U S) ω =
      finiteNoiseMonomial z S ω := by
  simp only [noiseMonomial,restrictedSubset,Finset.mem_filter,Finset.mem_univ,true_and,
    finiteNoiseMonomial]
  rw [Finset.prod_coe_sort U (fun i => if i∈S then z i ω else 1),
    Finset.prod_ite_mem,Finset.inter_eq_right.mpr hS]

private theorem restrictedSubset_inj (U S T : Finset ℕ) (hS : S⊆U) (hT : T⊆U) :
    restrictedSubset U S=restrictedSubset U T ↔ S=T := by
  constructor
  · intro he
    ext i
    constructor
    · intro hi
      have hh : (⟨i,hS hi⟩ : U)∈restrictedSubset U S := by simp [restrictedSubset,hi]
      rw [he] at hh
      simpa only [restrictedSubset,Finset.mem_filter,Finset.mem_univ,true_and] using hh
    · intro hi
      have hh : (⟨i,hT hi⟩ : U)∈restrictedSubset U T := by simp [restrictedSubset,hi]
      rw [←he] at hh
      simpa only [restrictedSubset,Finset.mem_filter,Finset.mem_univ,true_and] using hh
  · exact congrArg (restrictedSubset U)

omit [IsProbabilityMeasure μ] in
private theorem independent_restrict_upto
    (hz : iIndepFun (fun s : Fin N => z s.val) μ) (U : Finset ℕ)
    (hU : U⊆Finset.range N) : iIndepFun (fun i : U => z i.val) μ := by
  let f : U → Fin N := fun i => ⟨i.val,Finset.mem_range.mp (hU i.property)⟩
  have hi : Function.Injective f := by
    intro i j hij
    apply Subtype.ext
    exact congrArg Fin.val hij
  exact hz.precomp hi

theorem integrable_finiteNoiseMonomial_mul_upto
    (hz : iIndepFun (fun s : Fin N => z s.val) μ)
    (hm : ∀ s<N, Measurable (z s)) (hi : ∀ s<N, Integrable (z s) μ)
    (hi2 : ∀ s<N, Integrable (fun ω => z s ω ^ 2) μ)
    (S T : Finset ℕ) (hS : S⊆Finset.range N) (hT : T⊆Finset.range N) :
    Integrable (fun ω => finiteNoiseMonomial z S ω*finiteNoiseMonomial z T ω) μ := by
  let U := S∪T
  have hU : U⊆Finset.range N := Finset.union_subset hS hT
  have hh := integrable_noiseMonomial_mul (independent_restrict_upto hz U hU)
    (fun i => hm i.val (Finset.mem_range.mp (hU i.property)))
    (fun i => hi i.val (Finset.mem_range.mp (hU i.property)))
    (fun i => hi2 i.val (Finset.mem_range.mp (hU i.property)))
    (restrictedSubset U S) (restrictedSubset U T)
  simpa only [monomial_restricted U S Finset.subset_union_left,
    monomial_restricted U T Finset.subset_union_right] using hh

theorem integral_finiteNoiseMonomial_mul_upto
    (hz : iIndepFun (fun s : Fin N => z s.val) μ)
    (hm : ∀ s<N, Measurable (z s))
    (hmean : ∀ s<N, ∫ ω, z s ω ∂μ=0) (hvar : ∀ s<N, ∫ ω, z s ω^2 ∂μ=1)
    (S T : Finset ℕ) (hS : S⊆Finset.range N) (hT : T⊆Finset.range N) :
    (∫ ω, finiteNoiseMonomial z S ω*finiteNoiseMonomial z T ω ∂μ) =
      if S=T then 1 else 0 := by
  let U := S∪T
  have hU : U⊆Finset.range N := Finset.union_subset hS hT
  have hh := integral_noiseMonomial_mul (independent_restrict_upto hz U hU)
    (fun i => hm i.val (Finset.mem_range.mp (hU i.property)))
    (fun i => hmean i.val (Finset.mem_range.mp (hU i.property)))
    (fun i => hvar i.val (Finset.mem_range.mp (hU i.property)))
    (restrictedSubset U S) (restrictedSubset U T)
  simpa only [monomial_restricted U S Finset.subset_union_left,
    monomial_restricted U T Finset.subset_union_right,
    restrictedSubset_inj U S T Finset.subset_union_left Finset.subset_union_right] using hh

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem integral_finiteNoise_sum_upto [CompleteSpace E]
    (hz : iIndepFun (fun s : Fin N => z s.val) μ)
    (hm : ∀ s<N, Measurable (z s)) (hi : ∀ s<N, Integrable (z s) μ)
    (hi2 : ∀ s<N, Integrable (fun ω => z s ω ^ 2) μ)
    (hmean : ∀ s<N, ∫ ω, z s ω ∂μ=0) (hvar : ∀ s<N, ∫ ω, z s ω^2 ∂μ=1)
    (A : Finset (Finset ℕ)) (hA : ∅∈A) (hAN : ∀ S∈A, S⊆Finset.range N)
    (v : Finset ℕ → E) :
    (∫ ω, ∑ S∈A, finiteNoiseMonomial z S ω • v S ∂μ)=v ∅ := by
  have hv (S : Finset ℕ) (hS : S∈A) : Integrable
      (fun ω => finiteNoiseMonomial z S ω • v S) μ := by
    have hh := integrable_finiteNoiseMonomial_mul_upto hz hm hi hi2 S ∅ (hAN S hS)
      (Finset.empty_subset _)
    simpa only [finiteNoiseMonomial,Finset.prod_empty,mul_one] using hh.smul_const (v S)
  have hmom (S : Finset ℕ) (hS : S∈A) :
      (∫ ω, finiteNoiseMonomial z S ω ∂μ) = if S=∅ then 1 else 0 := by
    simpa only [finiteNoiseMonomial,Finset.prod_empty,mul_one] using
      integral_finiteNoiseMonomial_mul_upto hz hm hmean hvar S ∅ (hAN S hS)
        (Finset.empty_subset _)
  rw [integral_finsetSum A hv]
  simp_rw [integral_smul_const]
  calc
    _ = ∑ S∈A, (if S=∅ then (1:ℝ) else 0) • v S :=
      Finset.sum_congr rfl (fun S hS => congrArg (fun x : ℝ => x • v S) (hmom S hS))
    _ = _ := by simp [hA]

theorem integral_finiteNoise_sum_norm_sq_upto
    (hz : iIndepFun (fun s : Fin N => z s.val) μ)
    (hm : ∀ s<N, Measurable (z s)) (hi : ∀ s<N, Integrable (z s) μ)
    (hi2 : ∀ s<N, Integrable (fun ω => z s ω ^ 2) μ)
    (hmean : ∀ s<N, ∫ ω, z s ω ∂μ=0) (hvar : ∀ s<N, ∫ ω, z s ω^2 ∂μ=1)
    (A : Finset (Finset ℕ)) (hAN : ∀ S∈A, S⊆Finset.range N) (v : Finset ℕ → E) :
    (∫ ω, ‖∑ S∈A, finiteNoiseMonomial z S ω • v S‖^2 ∂μ) =
      ∑ S∈A, ‖v S‖^2 := by
  have hint (S) (hS : S∈A) (T) (hT : T∈A) : Integrable (fun ω =>
      (finiteNoiseMonomial z S ω*finiteNoiseMonomial z T ω)*⟪v S,v T⟫) μ :=
    (integrable_finiteNoiseMonomial_mul_upto hz hm hi hi2 S T (hAN S hS) (hAN T hT)).mul_const _
  have heq (ω) : ‖∑ S∈A, finiteNoiseMonomial z S ω • v S‖^2 =
      ∑ S∈A, ∑ T∈A, (finiteNoiseMonomial z S ω*finiteNoiseMonomial z T ω)*⟪v S,v T⟫ := by
    rw [← real_inner_self_eq_norm_sq]
    simp_rw [sum_inner,inner_sum,real_inner_smul_left,real_inner_smul_right]
    apply Finset.sum_congr rfl
    intro S _
    apply Finset.sum_congr rfl
    intro T _
    ring
  simp_rw [heq]
  rw [integral_finsetSum A (fun S hS => integrable_finsetSum A (fun T hT => hint S hS T hT))]
  apply Finset.sum_congr rfl
  intro S hS
  rw [integral_finsetSum A (fun T hT => hint S hS T hT)]
  simp_rw [integral_mul_const]
  have hpair (T) (hT : T∈A) := integral_finiteNoiseMonomial_mul_upto hz hm hmean hvar
    S T (hAN S hS) (hAN T hT)
  rw [Finset.sum_congr rfl (fun T hT =>
    congrArg (fun x : ℝ => x*⟪v S,v T⟫) (hpair T hT))]
  simp [hS]

theorem integral_finiteNoise_centered_sum_norm_sq_upto
    (hz : iIndepFun (fun s : Fin N => z s.val) μ)
    (hm : ∀ s<N, Measurable (z s)) (hi : ∀ s<N, Integrable (z s) μ)
    (hi2 : ∀ s<N, Integrable (fun ω => z s ω ^ 2) μ)
    (hmean : ∀ s<N, ∫ ω, z s ω ∂μ=0) (hvar : ∀ s<N, ∫ ω, z s ω^2 ∂μ=1)
    (A : Finset (Finset ℕ)) (hA : ∅∈A) (hAN : ∀ S∈A, S⊆Finset.range N)
    (v : Finset ℕ → E) :
    (∫ ω, ‖(∑ S∈A, finiteNoiseMonomial z S ω • v S)-v ∅‖^2 ∂μ) =
      ∑ S∈A.erase ∅, ‖v S‖^2 := by
  have he (ω) : (∑ S∈A, finiteNoiseMonomial z S ω • v S)-v ∅ =
      ∑ S∈A.erase ∅, finiteNoiseMonomial z S ω • v S := by
    rw [← Finset.sum_erase_add _ _ hA]
    simp [finiteNoiseMonomial]
  simp_rw [he]
  exact integral_finiteNoise_sum_norm_sq_upto hz hm hi hi2 hmean hvar _
    (fun S hS => hAN S (Finset.mem_of_mem_erase hS)) v

end
end chebyshev1.Stochastic
