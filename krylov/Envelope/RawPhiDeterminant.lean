import krylov.Envelope.RawPhiTransfer
import krylov.Realization.ConstantSuffixTransfer
import krylov.Realization.RawContinuation

set_option autoImplicit false
/-!
Article: main_krylov, prop:phi(a), actual continuation determinant.
Use: identify the true finite continuation of the supplied matrix with its genuine partially shifted determinant.
Source: actual two-memory suffix transfer, finite variation of constants and the proved diagonal insertion determinant identity.
-/

namespace krylov.Envelope
noncomputable section
open krylov.Reference krylov.Realization chebyshev1 Matrix Polynomial
open scoped BigOperators
variable {N : ℕ}

/-- The genuine measured continuation equals the true partially shifted matrix determinant divided by its actual determinant.
Use: The genuine measured continuation equals the true partially shifted matrix determinant divided by its actual determinant.
Article: main_krylov, prop:phi(a), actual continuation determinant.
Proof: The real constant state gives a variation of constants identity; identify its actual injection sum with the true determinant insertion formula. -/
theorem raw_phi_suffix_determinant (T : Matrix (Fin N) (Fin N) ℝ) (hT : T.PosDef)
    (htri : ∀ i j : Fin N,i.val+1 < j.val ∨ j.val+1 < i.val → T i j=0)
    (hneg : ∀ i j : Fin N,i.val+1=j.val → T i j<0) (j : ℕ) (hj : j≤N) (lam : ℝ) :
    (phi (rawAlpha T) (rawBeta T) j (N-j)).eval lam=(rawSuffixShift T j lam).det/T.det := by
  -- The actual scalar realization preserves the constant state on every true suffix index.
  let S := (rawJacobi T).method dictionaryInterval
  let R := S.realization
  have hP (i : ℕ) (hi : i<N-j) : R.P (j+i) *ᵥ ![1,1]=![1,1] := by
    change (if j+i=0 then !![1,0;1,0] else !![S.a (j+i),S.b (j+i);1,0]) *ᵥ ![1,1]=![1,1]
    by_cases hz : j+i=0
    · rw [ite_eq_left hz]
      ext a
      fin_cases a <;> norm_num [Matrix.mulVec,dotProduct,Fin.sum_univ_two]
    · have hsum : S.a (j+i)+S.b (j+i)=1 := by
        dsimp only [S]
        rw [raw_method_a T hT htri hneg (j+i) (by omega),raw_method_b T hT htri hneg (j+i) (by omega)]
        ring
      rw [ite_eq_right hz]
      ext a
      fin_cases a <;> simp [Matrix.mulVec,dotProduct,Fin.sum_univ_two,hsum]
  have hq (i : ℕ) (_ : i<N-j) : R.q (j+i) ⬝ᵥ ![1,1]=1 := by
    simp [R,TwoTerm.realization,dotProduct,Fin.sum_univ_two]
  -- Variation of constants recovers the genuine homogeneous suffix from its actual independent injections.
  have h := congrArg (fun v : Fin 2 → ℝ => v 0) (scalar_suffix_constant R j (N-j) ![1,1] lam hP hq)
  simp only [Pi.sub_apply,Pi.smul_apply,smul_eq_mul,Finset.sum_apply,Matrix.cons_val_zero] at h
  have hfirst := raw_phi_suffix_transfer T hT htri hneg j (N-j) (by omega) lam
  change (orderedProduct (fun i => R.scalarStep (j+i) lam) (N-j) *ᵥ ![1,1]) 0=
    (phi (rawAlpha T) (rawBeta T) j (N-j)).eval lam at hfirst
  rw [hfirst] at h
  -- Shift the true chronological injection sum without altering its physical terminal transfer.
  have hsum : (∑ s∈Finset.range (N-j),
      (orderedProduct (fun i => R.scalarStep (j+s+1+i) lam) (N-j-(s+1)) *ᵥ R.g (j+s)) 0)=
      -∑ s∈Finset.Ico j N,(injectionPolynomial R N s).eval lam := by
    rw [Finset.sum_Ico_eq_sum_range,← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro s hs
    have hlen : N-j-(s+1)=N-(j+s+1) := by omega
    rw [injectionPolynomial_eval,neg_neg,hlen]
    simp [R,TwoTerm.realization,dotProduct,Fin.sum_univ_two]
  rw [hsum] at h
  -- The proved insertion determinant is exactly this genuine continuation sum.
  have hd := raw_continuation_eval T hT htri hneg j hj lam
  change (rawSuffixShift T j lam).det/T.det=1+lam*∑ s∈Finset.Ico j N,(injectionPolynomial R N s).eval lam at hd
  rw [hd]
  linarith
end
end krylov.Envelope
