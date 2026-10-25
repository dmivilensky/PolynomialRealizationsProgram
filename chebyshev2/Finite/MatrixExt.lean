import chebyshev2.Finite.Horizon

/-!
Article: chebyshev2, Theorem A.1.
Nonnegative couplings and canonical tails make the actual matrix representation injective.
Use: `chebyshev2.Jacobi.matrix_injective` feeds `chebyshev2.Centering.lift_compression`
(lift compression).
Proof chain: `chebyshev2.centeringEquiv` — chebyshev2, Theorem A.1; Centering lift,
contractivity, odd Green entries and characteristic polynomial.
-/
namespace chebyshev2.Jacobi
noncomputable section
open chebyshev1 Matrix
set_option backward.isDefEq.respectTransparency false
variable {N : ℕ}

/--
Nonnegative couplings and canonical tails make the actual matrix representation injective.

The precise assertion is `Function.Injective (matrix : Jacobi N → Matrix (Fin N) (Fin N) ℝ)`.

Use: `chebyshev2.Centering.lift_compression` uses this assertion to establish exact
identity `(compression C).lift = C`.

Article: chebyshev2, Theorem A.1 via `chebyshev2.centeringEquiv`.

Proof: Separate `n < N` from its negation; prove the goal under each of these mutually
exclusive hypotheses. Prove equality of functions by evaluating both sides at an arbitrary
argument.
-/
theorem matrix_injective : Function.Injective (matrix : Jacobi N → Matrix (Fin N) (Fin N) ℝ) := by
  -- Separate `n < N` from its negation; prove the goal under each of these mutually exclusive
  -- hypotheses.
  intro J K h
  apply Jacobi.ext
  apply Horizon.jacobiData_ext
  · funext n
    by_cases hn : n < N
    · have he := congrArg (fun A => A ⟨n,hn⟩ ⟨n,hn⟩) h
      simpa [matrix, JacobiData.matrix_apply] using he
    · rw [J.diagonal_tail n (by omega), K.diagonal_tail n (by omega)]
  · funext n
    by_cases h0 : n = 0
    · subst n; rw [J.coupling_zero,K.coupling_zero]
    · by_cases hn : n < N
      · let p : Fin N := ⟨n-1,by omega⟩
        let q : Fin N := ⟨n,hn⟩
        have hpq : p ≠ q := by
          intro he
          have hh := congrArg Fin.val he
          change n-1 = n at hh
          omega
        have ha : p.val+1 = q.val := by dsimp [p,q]; omega
        have he := congrArg (fun A => (A p q)^2) h
        simpa [matrix, JacobiData.matrix_apply, hpq, ha, p, q,
          Real.sq_sqrt (J.coupling_nonneg n), Real.sq_sqrt (K.coupling_nonneg n)] using he
      · rw [J.coupling_tail n (by omega), K.coupling_tail n (by omega)]

end
end chebyshev2.Jacobi
