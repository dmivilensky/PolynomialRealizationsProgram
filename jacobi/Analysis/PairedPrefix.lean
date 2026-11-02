import jacobi.Analysis.PairedQuadratic
import Mathlib.Logic.Equiv.Fin.Basic

/-!
Article: jacobi, Appendix C.4 (uniform Gram limit and coercivity).
The physical half prefix is embedded into complete adjacent pairs.
If its length is odd, the last additional coordinate is genuinely zero.
Finite sums and quadratic forms are preserved exactly by this padding.
Use: pairIndex covers every physical half index and satisfies the actual 4L<=N+4 cell condition in the original coercivity argument.
-/
namespace jacobi.Analysis
noncomputable section

/-- Number of adjacent pairs needed to contain the physical matrix half.
Use: pairIndex covers every physical half index and satisfies the actual
4L<=N+4 cell condition in the original coercivity argument.
Article: jacobi, Appendix C.4 (uniform Gram limit and coercivity).
-/
def pairCount (n:ℕ) : ℕ := (n+1)/4+1

/-- The original matrix index of one coordinate in the padded pair array.
Use: pairIndex_sum and pairIndex_quadratic preserve the complete actual
physical-prefix forms, including the optional zero padded coordinate.
Article: jacobi, Appendix C.4 (uniform Gram limit and coercivity).
-/
def pairIndex (n:ℕ) (hn:1≤n) (p:Fin (pairCount n) × Fin 2) : Fin (n+1) :=
  ⟨2*p.1.val+p.2.val,by
    have hl := p.1.isLt
    have he := p.2.isLt
    dsimp [pairCount] at hl
    omega⟩

/-- Distinct padded pair coordinates are distinct actual matrix indices.
Use: finite sum transport introduces no multiplicity in the Gram form.
Article: jacobi, Appendix C.4 (uniform Gram limit and coercivity).
Proof: quotient and remainder on division by two recover both coordinates. -/
theorem pairIndex_injective (n:ℕ) (hn:1≤n) : Function.Injective (pairIndex n hn) := by
  intro p q hpq
  have he := congrArg Fin.val hpq
  dsimp [pairIndex] at he
  have hp := p.2.isLt
  have hq := q.2.isLt
  apply Prod.ext <;> apply Fin.ext <;> omega

/-- The true physical half is covered by the padded adjacent pairs.
Use: every original nonzero half-supported coordinate is retained when
the coercivity proof regroups the actual finite sums.
Article: jacobi, Appendix C.4 (uniform Gram limit and coercivity).
Proof: choose the original index quotient and remainder on division by
two; the physical half bound gives the required pair-count bound. -/
theorem pairIndex_covers (n:ℕ) (hn:1≤n) (i:Fin (n+1)) (hi:2*i.val≤n+1) :
    i∈Set.range (pairIndex n hn) := by
  refine ⟨(⟨i.val/2,?_⟩,⟨i.val%2,Nat.mod_lt _ (by norm_num)⟩),?_⟩
  · dsimp [pairCount]
    omega
  · apply Fin.ext
    dsimp [pairIndex]
    omega

/-- Pairing preserves every finite sum supported in the actual physical
matrix half; the optional extra coordinate contributes exactly zero.
Use: pairIndex_quadratic and the norm identity identify the original
finite form with the paired continuum comparison form.
Article: jacobi, Appendix C.4 (uniform Gram limit and coercivity).
Proof: use the genuine injective finite sum transport. Every omitted
index is outside the physical half and therefore has zero summand. -/
theorem pairIndex_sum (n:ℕ) (hn:1≤n) (f:Fin (n+1)→ℝ)
    (hf:∀i, n+1<2*i.val → f i=0) :
    (∑ p:Fin (pairCount n) × Fin 2, f (pairIndex n hn p)) = ∑ i, f i := by
  apply Fintype.sum_of_injective (pairIndex n hn) (pairIndex_injective n hn)
  · intro i hi
    apply hf i
    by_contra h
    exact hi (pairIndex_covers n hn i (by omega))
  · intro p
    rfl

/-- Pairing with true zero padding preserves the whole original finite
matrix quadratic form, including all cross terms.
Use: the cell-compressed lower bound applies to the same actual physical
Gram form, rather than to a smaller even prefix.
Article: jacobi, Appendix C.4 (uniform Gram limit and coercivity).
Proof: apply the exact supported finite sum transport to both indices;
each omitted row or column has a genuinely zero vector coordinate. -/
theorem pairIndex_quadratic (n:ℕ) (hn:1≤n) (A:Fin (n+1)→Fin (n+1)→ℝ)
    (v:Fin (n+1)→ℝ) (hv:∀i, n+1<2*i.val → v i=0) :
    (∑ p:Fin (pairCount n) × Fin 2, ∑ q:Fin (pairCount n) × Fin 2,
      A (pairIndex n hn p) (pairIndex n hn q)*v (pairIndex n hn p)*v (pairIndex n hn q)) =
      ∑ i, ∑ j, A i j*v i*v j := by
  have hinner (i:Fin (n+1)) := pairIndex_sum n hn
    (fun j => A i j*v i*v j) (fun j hj => by rw [hv j hj,mul_zero])
  simp_rw [hinner]
  apply pairIndex_sum n hn (fun i => ∑ j, A i j*v i*v j)
  intro i hi
  simp only [hv i hi,mul_zero,zero_mul,Finset.sum_const_zero]

end
end jacobi.Analysis
