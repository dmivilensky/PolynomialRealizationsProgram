import krylov.XR.ConditionalRealization
import krylov.XR.PhysicalVariation

/-!
Article: main_krylov, prop:cond, original arbitrary-dimensional upper bounds.
Use: normalize the actual conjugate two-column physical window and its
true operator increments; identify the hidden entry by the proved flag
identity, then apply the attained scalar fibre theorem. Source: Loewner
compression, chronological flags and exact Schur-complement completion.
-/
namespace krylov.XR
noncomputable section
open Matrix Finset krylov.Secant
open scoped Matrix.Norms.L2Operator BigOperators

/-- A symmetric two-dimensional matrix is its actual three-entry
conditional completion. Article: main_krylov, prop:cond. -/
theorem conditionalMatrix_of_isSymm (K : Matrix (Fin 2) (Fin 2) ℝ) (hK : K.IsSymm) :
    K=conditionalMatrix (K 0 0) (K 0 1) (K 1 1) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [conditionalMatrix,hK.apply 0 1]

/-- The original two-pair flag error, whitened in any genuinely diagonal
positive correction base, is precisely the hidden old entry plus the
actual fresh increment. No output-error identity is an assumption.
Article: main_krylov, prop:cond(a,b). -/
theorem conditional_normalized_error (C : ℕ → Matrix (Fin 2) (Fin 2) ℝ)
    (hC : ∀ k,(C k).IsSymm) (d : Fin 2 → ℝ) (hG : (diagonal d).PosDef) :
    relativeOperator (diagonal d) (C 2-latest (observed C))=
      conditionalHiddenError (relativeOperator (diagonal d) (C 1-C 0) 0 0)+
        relativeOperator (diagonal d) (C 2-C 1) := by
  have hp : prefixProjection 2 1=1 := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [prefixProjection]
  rw [model_error_eq_sum_compressions C hC]
  simp only [sum_range_succ,sum_range_zero,zero_add,Nat.reduceAdd]
  rw [hp,one_mul,mul_one]
  have hadd (A B : Matrix (Fin 2) (Fin 2) ℝ) :
      relativeOperator (diagonal d) (A+B)=relativeOperator (diagonal d) A+
        relativeOperator (diagonal d) B := by simp only [relativeOperator,Matrix.mul_add,Matrix.add_mul]
  rw [hadd,relative_flag_compression _ _ hG,
    transportedFlag_eq_of_diagonal d hG, (prefixProjection_isSymm 2 0).eq]
  congr 1
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [prefixProjection,conditionalHiddenError,Matrix.mul_apply,Fin.sum_univ_two]

/-- The exact known-base radius bounds every actual two-column observed
operator sequence in every ambient dimension after genuine compression.
Article: main_krylov, prop:cond(a), upper-bound clause. -/
theorem conditional_compressed_known_upper (C : ℕ → Matrix (Fin 2) (Fin 2) ℝ)
    (hC : ∀ k,(C k).IsSymm) (d : Fin 2 → ℝ) (hG : (diagonal d).PosDef)
    (ω fresh : ℝ) (hω : 0<ω) (hfresh : 0≤fresh)
    (hbudget : relativeBudget (diagonal d) (C 1-C 0)≤ω)
    (hfreshbudget : relativeBudget (diagonal d) (C 2-C 1)≤fresh) :
    let K := relativeOperator (diagonal d) (C 1-C 0)
    relativeBudget (diagonal d) (C 2-latest (observed C))≤
      knownConditionalRadius ω (K 0 1) (K 1 1) fresh := by
  let K := relativeOperator (diagonal d) (C 1-C 0)
  have hK : K.IsSymm := relativeOperator_isSymm _ _ ((hC 1).sub (hC 0))
  have hb : ‖conditionalMatrix (K 0 0) (K 0 1) (K 1 1)‖≤ω := by
    rw [←conditionalMatrix_of_isSymm K hK]
    exact hbudget
  have hf := conditionalMatrix_column_feasible (K 0 0) (K 0 1) (K 1 1) ω hω.le hb
  have hh := (knownConditionalRadius_isGreatest hω hf hfresh).2
    ⟨K 0 0,relativeOperator (diagonal d) (C 2-C 1),hb,
      relativeOperator_isSymm _ _ ((hC 2).sub (hC 1)),hfreshbudget,rfl⟩
  change ‖relativeOperator _ _‖≤_
  rw [conditional_normalized_error C hC d hG]
  exact hh

/-- The same actual normalized error satisfies the data-only radius,
with its signed observed cross ratio. Consistency of those observations
is derived from the genuine old spectral budget. Article: prop:cond(b). -/
theorem conditional_compressed_unknown_upper (C : ℕ → Matrix (Fin 2) (Fin 2) ℝ)
    (hC : ∀ k,(C k).IsSymm) (d : Fin 2 → ℝ) (hG : (diagonal d).PosDef)
    (ω fresh : ℝ) (hω : 0<ω) (hω₁ : ω<1) (hfresh : 0≤fresh)
    (hbudget : relativeBudget (diagonal d) (C 1-C 0)≤ω)
    (hfreshbudget : relativeBudget (diagonal d) (C 2-C 1)≤fresh) :
    let K := relativeOperator (diagonal d) (C 1-C 0)
    let δobs := K 0 1/Real.sqrt (1+K 1 1)
    0<1+K 1 1 ∧ δobs^2≤2-2*Real.sqrt (1-ω^2) ∧
      relativeBudget (diagonal d) (C 2-latest (observed C))≤
        unknownConditionalRadius ω δobs fresh := by
  let K := relativeOperator (diagonal d) (C 1-C 0)
  let δobs := K 0 1/Real.sqrt (1+K 1 1)
  have hK : K.IsSymm := relativeOperator_isSymm _ _ ((hC 1).sub (hC 0))
  have hb : ‖conditionalMatrix (K 0 0) (K 0 1) (K 1 1)‖≤ω := by
    rw [←conditionalMatrix_of_isSymm K hK]
    exact hbudget
  have hf := conditionalMatrix_column_feasible (K 0 0) (K 0 1) (K 1 1) ω hω.le hb
  obtain ⟨_,hkabs,hroot⟩ := conditional_feasible_diagonal hω.le hf
  have hk : 0<1+K 1 1 := by linarith [neg_abs_le (K 1 1)]
  have hs : (K 0 1)^2=δobs^2*(1+K 1 1) := by
    dsimp only [δobs]
    rw [div_pow,Real.sq_sqrt hk.le]
    exact (div_mul_cancel₀ _ hk.ne').symm
  have hconsistent : δobs^2≤2-2*Real.sqrt (1-ω^2) := by
    apply conditional_feasibility_necessary hω hω₁ hk
    nlinarith only [hf,hs]
  have hh := (unknownConditionalRadius_isGreatest hω hω₁ hconsistent hfresh).2
    ⟨K 0 0,relativeOperator (diagonal d) (C 2-C 1),⟨K 0 1,K 1 1,hs,hb⟩,
      relativeOperator_isSymm _ _ ((hC 2).sub (hC 1)),hfreshbudget,rfl⟩
  refine ⟨hk,hconsistent,?_⟩
  change ‖relativeOperator _ _‖≤_
  rw [conditional_normalized_error C hC d hG]
  exact hh

/-- The original ambient-dimensional operators and genuine conjugate
step columns satisfy both sharp conditional upper bounds. Supplying more
vector observations only restricts the same admissible source histories.
Article: main_krylov, prop:cond(a,b), physical correspondence. -/
theorem physical_conditional_upper {n : ℕ} (S : Matrix (Fin n) (Fin 2) ℝ)
    (A : ℕ → Matrix (Fin n) (Fin n) ℝ) (hA : ∀ k,(A k).IsSymm)
    (hbase : (A 0).PosDef) (hS : Function.Injective S.mulVec)
    (d : Fin 2 → ℝ) (hdiag : Sᵀ*A 0*S=diagonal d)
    (ω fresh : ℝ) (hω : 0<ω) (hω₁ : ω<1) (hfresh : 0≤fresh)
    (hold : relativeBudget (A 0) (A 1-A 0)≤ω)
    (hnew : relativeBudget (A 0) (A 2-A 1)≤fresh) :
    let K := relativeOperator (diagonal d) (Sᵀ*(A 1-A 0)*S)
    let err := relativeBudget (diagonal d) (Sᵀ*A 2*S-latest (Sᵀ*pairImages S A))
    let δobs := K 0 1/Real.sqrt (1+K 1 1)
    err≤knownConditionalRadius ω (K 0 1) (K 1 1) fresh ∧
      0<1+K 1 1 ∧ δobs^2≤2-2*Real.sqrt (1-ω^2) ∧
      err≤unknownConditionalRadius ω δobs fresh := by
  let C := fun k=>Sᵀ*A k*S
  have hc (k : ℕ) : (C k).IsSymm := by
    simp only [C,IsSymm,transpose_mul,transpose_transpose,(hA k).eq,Matrix.mul_assoc]
  have hg : (diagonal d).PosDef := hdiag ▸ physical_gram_posDef S (A 0) hbase hS
  have hb := physical_compressed_budget S (A 0) (A 1-A 0) hbase
    ((hA 1).sub (hA 0)) hS ω hold
  have hn := physical_compressed_budget S (A 0) (A 2-A 1) hbase
    ((hA 2).sub (hA 1)) hS fresh hnew
  rw [hdiag] at hb hn
  have hb' : relativeBudget (diagonal d) (C 1-C 0)≤ω := by
    simpa only [C,Matrix.mul_sub,Matrix.sub_mul] using hb
  have hn' : relativeBudget (diagonal d) (C 2-C 1)≤fresh := by
    simpa only [C,Matrix.mul_sub,Matrix.sub_mul] using hn
  have hknown := conditional_compressed_known_upper C hc d hg ω fresh hω hfresh hb' hn'
  have hunknown := conditional_compressed_unknown_upper C hc d hg ω fresh hω hω₁ hfresh hb' hn'
  dsimp only
  simpa only [C,Matrix.mul_sub,Matrix.sub_mul,observed_compression] using And.intro hknown hunknown

end
end krylov.XR
