import krylov.Envelope.TwoTermSuffixPhi
import krylov.Realization.RawFrozen

set_option autoImplicit false
/-!
Article: main_krylov, prop:phi(a), genuine supplied-matrix continuation suffix.
Use: identify the actual raw-matrix frozen continuation with the true two-memory realization suffix formed from the same real matrix.
Source: proved genuine positive raw pivots, actual measured step/momentum coefficient identities and the real continuation/two-term suffix theorem.
-/

namespace krylov.Envelope
noncomputable section
open krylov.Reference krylov.Realization chebyshev1 Matrix Polynomial
open scoped BigOperators
variable {N : ℕ}

/-- The actual positive tridiagonal matrix continuation is exactly the genuine first-coordinate constant-state suffix transfer of its true raw realization.
Use: The actual positive tridiagonal matrix continuation is exactly the genuine first-coordinate constant-state suffix transfer of its true raw realization.
Article: main_krylov, prop:phi(a), genuine supplied-matrix continuation suffix.
Proof: Derive the real nonzero pivot, query coefficient, constant-preserving and momentum identities from the genuine supplied matrix, then apply the actual continuation suffix theorem. -/
theorem raw_phi_suffix_transfer (T : Matrix (Fin N) (Fin N) ℝ) (hT : T.PosDef)
    (htri : ∀ i j : Fin N,i.val+1 < j.val ∨ j.val+1 < i.val → T i j=0)
    (hneg : ∀ i j : Fin N,i.val+1=j.val → T i j<0) (j k : ℕ) (hjk : j+k≤N) (lam : ℝ) :
    (orderedProduct (fun i => ((rawJacobi T).realization dictionaryInterval).scalarStep (j+i) lam) k *ᵥ ![1,1]) 0=
      (phi (rawAlpha T) (rawBeta T) j k).eval lam := by
  -- Every true suffix coefficient comes from the actual supplied positive tridiagonal matrix and its genuine pivot dictionary.
  let S := (rawJacobi T).method dictionaryInterval
  have ha (i : ℕ) (hi : i<k) : rawAlpha T (j+i)≠0 :=
    (rawAlpha_pos T hT htri hneg (j+i) (by omega)).ne'
  have hgamma (i : ℕ) (_ : i<k) : S.gamma (j+i)=rawAlpha T (j+i) := raw_method_gamma T (j+i)
  have hfix (i : ℕ) (hi : i<k) : S.a (j+i)+S.b (j+i)=1 := by
    dsimp only [S]
    rw [raw_method_a T hT htri hneg (j+i) (by omega),raw_method_b T hT htri hneg (j+i) (by omega)]
    ring
  have hb (i : ℕ) (hi : i<k) (hip : 0 < i) :
      S.b (j+i)= -rawAlpha T (j+i)*rawBeta T (j+i-1)/rawAlpha T (j+i-1) := by
    dsimp only [S]
    rw [raw_method_b T hT htri hneg (j+i) (by omega),rawMomentum,ite_eq_right (show j+i≠0 by omega)]
    ring
  -- Read the actual first memory coordinate only after identifying the genuine complete suffix transfer.
  have h := congrArg (fun v : Fin 2 → ℝ => v 0)
    (phi_twoTerm_suffix (rawAlpha T) (rawBeta T) S j k ha hgamma hfix hb lam)
  simpa only [S,JacobiData.realization,Matrix.cons_val_zero] using h
end
end krylov.Envelope
