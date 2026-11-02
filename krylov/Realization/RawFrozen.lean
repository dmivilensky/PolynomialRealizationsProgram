import krylov.Realization.RawTail
import krylov.Realization.FixedInjections

/-!
Article: main_krylov, prop:dict(i) and s6:frozen, actual raw frozen recurrence.
Use: derive real positive pivot ratios and momentum coefficients from the
supplied physical tridiagonal matrix, then identify its genuine queried
physical recurrence with independent additive oracle injections.
Source: the proved raw determinant dictionary and existing real Jacobi
normalization recurrence; standard positive tridiagonal LDL pivot identities
are attributed to Meurant and Golub--Meurant.
-/

namespace krylov.Realization
noncomputable section
open Matrix chebyshev1
open scoped BigOperators
variable {N : ℕ}

/-- The true positive-pivot reciprocal constructed from consecutive actual leading determinants.
Use: supplies the real step coefficient of the supplied matrix realization.
Article: main_krylov, prop:dict(i), α_s. -/
def rawAlpha (T : Matrix (Fin N) (Fin N) ℝ) (s : ℕ) : ℝ :=
  (rawJacobi T).den dictionaryInterval s/(rawJacobi T).den dictionaryInterval (s+1)
/-- The actual squared adjacent LDL coupling formed from the genuine raw matrix and leading-pivot ratio.
Use: supplies the source frozen-CG momentum data, with the terminal unused extension totalized.
Article: main_krylov, prop:dict(i), β_s. -/
def rawBeta (T : Matrix (Fin N) (Fin N) ℝ) (s : ℕ) : ℝ :=
  (rawJacobi T).aSq (s+1)*(rawAlpha T s)^2
/-- The actual frozen recurrence momentum, including the causal zero initial coefficient.
Use: handles the first physical query separately from the two-term memory updates.
Article: main_krylov, s6:frozen, α_s β_(s−1)/α_(s−1). -/
def rawMomentum (T : Matrix (Fin N) (Fin N) ℝ) (s : ℕ) : ℝ :=
  if s=0 then 0 else rawAlpha T s*rawBeta T (s-1)/rawAlpha T (s-1)

/-- Every actual used raw pivot reciprocal is positive.
Use: all frozen recurrence and LDL coupling denominators are genuinely nonzero.
Article: main_krylov, prop:dict(i).
Proof: the true leading determinants of the supplied positive matrix are strictly positive. -/
theorem rawAlpha_pos (T : Matrix (Fin N) (Fin N) ℝ) (hT : T.PosDef)
    (htri : ∀ i j : Fin N, i.val+1 < j.val ∨ j.val+1 < i.val → T i j=0)
    (hneg : ∀ i j : Fin N, i.val+1=j.val → T i j < 0) (s : ℕ) (hs : s<N) :
    0<rawAlpha T s := by
  have ha := rawJacobi_admissible T hT htri hneg
  exact div_pos (ha s hs.le) (ha (s+1) (by omega))

/-- Every constructed actual squared LDL coupling is nonnegative.
Use: justify the genuine real coupling square root, including zero extensions.
Article: main_krylov, prop:dict(i).
Proof: both the genuine squared Jacobi coupling and the pivot square are nonnegative. -/
theorem rawBeta_nonneg (T : Matrix (Fin N) (Fin N) ℝ) (s : ℕ) : 0≤rawBeta T s :=
  mul_nonneg (rawJacobi_aSq_nonneg T (s+1)) (sq_nonneg _)

/-- The actual constructed Jacobi realization uses precisely the genuine raw pivot reciprocal as its query step coefficient.
Use: the auxiliary affine normalization leaves no physical scale factor.
Article: main_krylov, s6:frozen.
Proof: the true auxiliary interval has width two, cancelling the old normalization factor. -/
theorem raw_method_gamma (T : Matrix (Fin N) (Fin N) ℝ) (s : ℕ) :
    ((rawJacobi T).method dictionaryInterval).gamma s=rawAlpha T s := by
  norm_num [JacobiData.method,dictionaryInterval,SpectralInterval.delta,rawAlpha]

/-- The actual preceding-memory coefficient is the negative genuine raw frozen momentum.
Use: identify the real fixed recurrence coefficient with its physical LDL data.
Article: main_krylov, s6:frozen.
Proof: the initial coupling is zero. At a later real step, substitute the
actual pivot ratios and cancel only proved positive leading determinants. -/
theorem raw_method_b (T : Matrix (Fin N) (Fin N) ℝ) (hT : T.PosDef)
    (htri : ∀ i j : Fin N, i.val+1 < j.val ∨ j.val+1 < i.val → T i j=0)
    (hneg : ∀ i j : Fin N, i.val+1=j.val → T i j < 0) (s : ℕ) (hs : s<N) :
    ((rawJacobi T).method dictionaryInterval).b s= -rawMomentum T s := by
  -- All actual denominator cancellations are justified by the supplied matrix's true positive leading minors.
  have ha := rawJacobi_admissible T hT htri hneg
  by_cases hz : s=0
  · subst s
    simp [JacobiData.method,rawJacobi,rawMomentum]
  · simp only [rawMomentum,ite_eq_right hz,rawAlpha,rawBeta,JacobiData.method]
    simp only [show s-1+1=s by omega]
    field_simp [(ha (s-1) (by omega)).ne',(ha s hs.le).ne',(ha (s+1) (by omega)).ne']

/-- The actual current-memory coefficient is one plus the genuine raw frozen momentum.
Use: the resulting physical recurrence preserves constants and has the printed CG displacement form.
Article: main_krylov, s6:frozen.
Proof: the actual first leading determinant gives the initial coefficient;
for later steps the existing true Jacobi normalization identity and the proved
preceding-memory formula give the result. -/
theorem raw_method_a (T : Matrix (Fin N) (Fin N) ℝ) (hT : T.PosDef)
    (htri : ∀ i j : Fin N, i.val+1 < j.val ∨ j.val+1 < i.val → T i j=0)
    (hneg : ∀ i j : Fin N, i.val+1=j.val → T i j < 0) (s : ℕ) (hs : s<N) :
    ((rawJacobi T).method dictionaryInterval).a s=1+rawMomentum T s := by
  -- All actual denominator cancellations are justified by the supplied matrix's true positive leading minors.
  have ha := rawJacobi_admissible T hT htri hneg
  by_cases hz : s=0
  · subst s
    simp only [rawMomentum,ite_true,add_zero,JacobiData.method,JacobiData.den_zero]
    rw [← JacobiData.den_one]
    exact one_div_mul_cancel (ha 1 (by omega)).ne'
  · have hp := (rawJacobi T).fixed_point dictionaryInterval (s-1)
      (by rw [show s-1+2=s+1 by omega]; exact (ha (s+1) (by omega)).ne')
    simp only [show s-1+1=s by omega] at hp
    rw [raw_method_b T hT htri hneg s hs] at hp
    linarith


/-- The actual raw query step coefficient is exactly the ratio of the true consecutive leading physical determinants.
Use: identifies the constructed reciprocal pivots with the supplied matrix minors.
Article: main_krylov, prop:dict(i).
Proof: substitute both proved genuine physical leading determinant normalizations. -/
theorem rawAlpha_det (T : Matrix (Fin N) (Fin N) ℝ) (hT : T.PosDef)
    (htri : ∀ i j : Fin N, i.val+1 < j.val ∨ j.val+1 < i.val → T i j=0)
    (hneg : ∀ i j : Fin N, i.val+1=j.val → T i j < 0) (s : ℕ) (hs : s<N) :
    rawAlpha T s=(rawBlock T 0 s (by omega)).det/(rawBlock T 0 (s+1) (by omega)).det := by
  rw [rawAlpha,raw_den_det T hT.1.isSymm htri hneg s hs.le,
    raw_den_det T hT.1.isSymm htri hneg (s+1) (by omega)]

/-- The real adjacent raw LDL coupling is the square of the actual negative physical edge times its genuine pivot reciprocal.
Use: tie β to the supplied original matrix rather than independent recurrence data.
Article: main_krylov, prop:dict(i).
Proof: the genuine adjacent index selects that physical squared edge in the actual raw Jacobi construction. -/
theorem rawBeta_edge (T : Matrix (Fin N) (Fin N) ℝ) (i j : Fin N) (hij : i.val+1=j.val) :
    rawBeta T i.val=(T i j*rawAlpha T i.val)^2 := by
  have hbound : 0 < i.val+1 ∧ i.val+1 < N := by have := j.isLt; omega
  simp only [rawBeta,rawJacobi,dite_eq_left hbound]
  have hi : (⟨i.val+1-1,by have := i.isLt; omega⟩ : Fin N)=i := Fin.ext (by dsimp only; omega)
  have hj : (⟨i.val+1,by omega⟩ : Fin N)=j := Fin.ext hij
  rw [hi,hj,mul_pow]

/-- The actual negative square-root LDL coupling equals the genuine physical edge times its positive reciprocal pivot.
Use: fixes the true source lower-factor sign from the supplied negative off-diagonal entries.
Article: main_krylov, prop:dict(i).
Proof: the proved square formula, true negative edge and genuine positive
pivot determine the real square-root sign uniquely. -/
theorem rawLower_edge (T : Matrix (Fin N) (Fin N) ℝ) (hT : T.PosDef)
    (htri : ∀ i j : Fin N, i.val+1 < j.val ∨ j.val+1 < i.val → T i j=0)
    (hneg : ∀ i j : Fin N, i.val+1=j.val → T i j < 0) (i j : Fin N) (hij : i.val+1=j.val) :
    -Real.sqrt (rawBeta T i.val)=T i j*rawAlpha T i.val := by
  rw [rawBeta_edge T i j hij,Real.sqrt_sq_eq_abs,
    abs_of_neg (mul_neg_of_neg_of_pos (hneg i j hij) (rawAlpha_pos T hT htri hneg i.val i.isLt)),neg_neg]

/-- The actual raw matrix diagonal has the genuine reciprocal-pivot plus preceding-coupling LDL expression.
Use: supplies the real diagonal identity for the constructed physical bidiagonal factorization.
Article: main_krylov, prop:dict(i), T=LDLᵀ.
Proof: the actual leading determinant recurrence is the true scalar LDL
pivot recurrence. Substitute the real pivot and coupling ratios and cancel
proved positive determinants; the first site uses its genuine one-site minor. -/
theorem raw_ldl_diagonal (T : Matrix (Fin N) (Fin N) ℝ) (hT : T.PosDef)
    (htri : ∀ i j : Fin N, i.val+1 < j.val ∨ j.val+1 < i.val → T i j=0)
    (hneg : ∀ i j : Fin N, i.val+1=j.val → T i j < 0) (i : Fin N) :
    (rawAlpha T i.val)⁻¹+(if 0 < i.val then rawBeta T (i.val-1)/rawAlpha T (i.val-1) else 0)=T i i := by
  -- All actual denominator cancellations are justified by the supplied matrix's true positive leading minors.
  have ha := rawJacobi_admissible T hT htri hneg
  by_cases hi : 0 < i.val
  · have hr := (rawJacobi T).den_add_two dictionaryInterval (i.val-1)
    rw [show i.val-1+2=i.val+1 by omega,show i.val-1+1=i.val by omega] at hr
    have hb : dictionaryInterval.eta-(rawJacobi T).b i.val=T i i := by
      rw [dictionaryInterval_eta]
      simp only [rawJacobi,dite_eq_left i.isLt,Fin.eta,sub_sub_cancel]
    rw [hb] at hr
    simp only [ite_eq_left hi,rawBeta,rawAlpha,show i.val-1+1=i.val by omega,inv_div]
    rw [hr]
    field_simp [(ha i.val i.isLt.le).ne',(ha (i.val-1) (by omega)).ne']
    ring
  · have hi0 : i.val=0 := by omega
    rw [ite_eq_right hi,add_zero,rawAlpha,inv_div,hi0]
    simp only [Nat.zero_add,JacobiData.den_zero,JacobiData.den_one,div_one,dictionaryInterval_eta]
    have hb : (rawJacobi T).b 0=2-T i i := by
      dsimp only [rawJacobi]
      rw [dite_eq_left (show 0 < N by have := i.isLt; omega)]
      have he : (⟨0,by have := i.isLt; omega⟩ : Fin N)=i := Fin.ext hi0.symm
      rw [he]
    rw [hb,sub_sub_cancel]

variable {E : Type*} [AddCommGroup E] [Module ℝ E]


/-- The actual first physical query of any true two-term realization is its causal gradient step with its real additive injection.
Use: no fictitious previous state enters the initial update.
Article: main_krylov, s6:frozen.
Proof: execute the actual first memory update and simplify its real causal initial and query vectors. -/
theorem twoTerm_injected_zero (S : TwoTerm) (Q : E →ₗ[ℝ] E) (input : ℕ → E) (initial : E) :
    injectedFixedRun S.realization Q input initial 1 0=initial-S.gamma 0 • (Q initial+input 0) := by
  rw [injectedFixedRun_succ S.realization Q input initial 0 0]
  simp [TwoTerm.realization,Fin.sum_univ_two,injectedFixedRun,affineRun]

/-- The actual second memory coordinate of every real two-term update is exactly the preceding first coordinate.
Use: the printed previous physical iterate is a proved property of the genuine memory executor.
Article: main_krylov, s6:frozen.
Proof: the actual second transition row is the first-coordinate selector and its true injection coefficient is zero. -/
theorem twoTerm_injected_previous (S : TwoTerm) (Q : E →ₗ[ℝ] E) (input : ℕ → E)
    (initial : E) (s : ℕ) :
    injectedFixedRun S.realization Q input initial (s+1) 1=
      injectedFixedRun S.realization Q input initial s 0 := by
  rw [injectedFixedRun_succ]
  by_cases hs : s=0 <;> simp [TwoTerm.realization,hs,Fin.sum_univ_two]

/-- The supplied positive raw tridiagonal realization executes the printed frozen-CG physical recurrence with every actual independent additive oracle injection.
Use: the conclusion concerns the true queried affine memory run in arbitrary real vector spaces, with the actual previous iterate and positive constructed pivot coefficients.
Article: main_krylov, prop:dict(i) and s6:frozen.
Proof: execute the true first memory row, use the proved actual previous
memory-coordinate identity, and substitute the genuine raw coefficients.
Collect the physical displacement and momentum terms by module algebra. -/
theorem raw_injected_frozen (T : Matrix (Fin N) (Fin N) ℝ) (hT : T.PosDef)
    (htri : ∀ i j : Fin N, i.val+1 < j.val ∨ j.val+1 < i.val → T i j=0)
    (hneg : ∀ i j : Fin N, i.val+1=j.val → T i j < 0)
    (Q : E →ₗ[ℝ] E) (input : ℕ → E) (initial : E) (s : ℕ) (hs : s+1<N) :
    let v := injectedFixedRun ((rawJacobi T).realization dictionaryInterval) Q input initial
    v (s+2) 0=v (s+1) 0-rawAlpha T (s+1) • (Q (v (s+1) 0)+input (s+1))+
      rawMomentum T (s+1) • (v (s+1) 0-v s 0) := by
  -- Both memory coordinates are those of the true physical queried recurrence.
  let S := (rawJacobi T).method dictionaryInterval
  have hp := twoTerm_injected_previous S Q input initial s
  have hrow (v : Fin 2 → E) :
      (∑ j, S.realization.P (s+1) 0 j • v j)-S.realization.g (s+1) 0 •
        (Q (∑ j, S.realization.q (s+1) j • v j)+input (s+1))=
      S.a (s+1) • v 0+S.b (s+1) • v 1-S.gamma (s+1) • (Q (v 0)+input (s+1)) := by
    simp [TwoTerm.realization,Fin.sum_univ_two]
  let v := injectedFixedRun S.realization Q input initial
  change v (s+2) 0=v (s+1) 0-rawAlpha T (s+1) • (Q (v (s+1) 0)+input (s+1))+
    rawMomentum T (s+1) • (v (s+1) 0-v s 0)
  have hnext : v (s+2) 0=S.a (s+1) • v (s+1) 0+S.b (s+1) • v (s+1) 1-
      S.gamma (s+1) • (Q (v (s+1) 0)+input (s+1)) :=
    (injectedFixedRun_succ S.realization Q input initial (s+1) 0).trans (hrow (v (s+1)))
  rw [hnext]
  rw [show S.a (s+1)=1+rawMomentum T (s+1) from raw_method_a T hT htri hneg _ hs,
    show S.b (s+1)= -rawMomentum T (s+1) from raw_method_b T hT htri hneg _ hs,
    show S.gamma (s+1)=rawAlpha T (s+1) from raw_method_gamma T _]
  have hprev : v (s+1) 1=v s 0 := hp
  rw [hprev]
  module
end
end krylov.Realization
