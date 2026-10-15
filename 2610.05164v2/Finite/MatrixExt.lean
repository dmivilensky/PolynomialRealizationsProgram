import «2610.05164v2».Finite.Horizon

/-!
Article: 2610.05164v2, Theorem A.1.
Nonnegative couplings and canonical tails make the actual matrix representation injective.
Use: `«2610.05164v2».Jacobi.matrix_injective` feeds `«2610.05164v2».Centering.lift_compression`
(lift compression).
Proof chain: `«2610.05164v2».centeringEquiv` — 2610.05164v2, Theorem A.1; Centering lift,
contractivity, odd Green entries and characteristic polynomial.
-/
namespace «2610.05164v2».Jacobi
noncomputable section
open «2606.16671v2» Matrix
set_option backward.isDefEq.respectTransparency false
variable {N : ℕ}

/--
Nonnegative couplings and canonical tails make the actual matrix representation injective.

The precise assertion is `Function.Injective (matrix : Jacobi N → Matrix (Fin N) (Fin N) ℝ)`.

Use: `«2610.05164v2».Centering.lift_compression` uses this assertion to establish exact
identity `(compression C).lift = C`.

Article: 2610.05164v2, Theorem A.1 via `«2610.05164v2».centeringEquiv`.

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
end «2610.05164v2».Jacobi
