import chebyshev2.Green.Forward

/-!
Article: chebyshev2, Proposition 1.
Markov.
Use: `chebyshev2.Jacobi.green_entry_pos` feeds `chebyshev2.Jacobi.position_difference`
(position difference).
Proof chain: `chebyshev2.Packing.exists_representation` — chebyshev2, Theorem 2.3; Block
packing, exact masses/energy and spectral distance.
-/
namespace chebyshev2.Jacobi
noncomputable section
open Matrix
open scoped Matrix
set_option backward.isDefEq.respectTransparency false
variable {N : ℕ} (J : Jacobi N)

/--
Exact identity `J.green j i = J.green i j`.

Use: `chebyshev2.Jacobi.green_entry_pos` rewrites with this identity to establish the
stated quantitative bound `0 < J.green i j`.

Article: chebyshev2, Theorem 2.3 via `chebyshev2.Packing.exists_representation`.

Proof: Rewrite the definitions and library identities explicitly named in the proof, then
discharge the resulting algebraic or order relation.
-/
theorem green_symmetric (hm : (1-J.matrix).PosDef) (i j : Fin N) :
    J.green j i = J.green i j := by simpa [green] using hm.inv.isHermitian.apply i j

/--
Exact identity `J.green i k*J.green j j = J.green i j*J.green j k`.

Use: `chebyshev2.Jacobi.green_neighbor_minor` uses this identity to establish exact
identity `sqrt (J.data.aSq j.val)*(J.green i i*J.green j j-J.green i j^2) = J.green i j`.

Article: chebyshev2, Theorem 2.3 via `chebyshev2.Packing.exists_representation`.

Proof: Induct on `n`; the recursive step uses the previous-stage assertion.
-/
theorem green_markov (hm : (1-J.matrix).PosDef) (i j k : Fin N)
    (hij : i.val ≤ j.val) (hjk : j.val ≤ k.val) :
    J.green i k*J.green j j = J.green i j*J.green j k := by
  -- Induct on `n`; the recursive step uses the previous-stage assertion.
  have he : ∀ n, ∀ i : Fin N, i.val+n = j.val →
      J.green i k*J.green j j = J.green i j*J.green j k := by
    intro n
    induction n with
    | zero =>
      intro i hi
      have hi' : i = j := Fin.ext (by simpa using hi)
      subst i; ring
    | succ n ih =>
      intro i hi
      have hij' : i.val < j.val := by omega
      have hik : i.val < k.val := by omega
      let p : Fin N := ⟨i.val+1,by omega⟩
      have hh := ih p (by dsimp [p]; omega)
      rw [J.green_forward hm i k hik, J.green_forward hm i j hij']
      change (J.forwardRatio i*J.green p k)*J.green j j =
        (J.forwardRatio i*J.green p j)*J.green j k
      linear_combination J.forwardRatio i*hh
  exact he (j.val-i.val) i (by omega)

/--
The stated quantitative bound `0 < J.green i j`.

Use: `chebyshev2.Jacobi.green_entry_pos` uses this bound to establish the stated
quantitative bound `0 < J.green i j`.

Article: chebyshev2, Theorem 2.3 via `chebyshev2.Packing.exists_representation`.

Proof: Induct on `n`; the recursive step uses the previous-stage assertion.
-/
theorem green_entry_pos_of_le (hm : (1-J.matrix).PosDef) (hir : J.Irreducible)
    (i j : Fin N) (hij : i.val ≤ j.val) : 0 < J.green i j := by
  -- Induct on `n`; the recursive step uses the previous-stage assertion.
  have he : ∀ n, ∀ i : Fin N, i.val+n = j.val → 0 < J.green i j := by
    intro n
    induction n with
    | zero =>
      intro i hi
      have hi' : i = j := Fin.ext (by simpa using hi)
      subst i; exact hm.inv.diag_pos
    | succ n ih =>
      intro i hi
      have hij : i.val < j.val := by omega
      rw [J.green_forward hm i j hij]
      apply mul_pos (J.forwardRatio_pos hm hir i (by omega))
      exact ih ⟨i.val+1,by omega⟩ (by change i.val+1+n = j.val; omega)
  exact he (j.val-i.val) i (by omega)

/--
The stated quantitative bound `0 < J.green i j`.

Use: `chebyshev2.Jacobi.edgeFlow_pos` uses this bound to establish the stated quantitative
bound `0 < J.edgeFlow i`.

Article: chebyshev2, Theorem 2.3 via `chebyshev2.Packing.exists_representation`.

Proof: Separate `i.val ≤ j.val` from its negation; prove the goal under each of these mutually
exclusive hypotheses.
-/
theorem green_entry_pos (hm : (1-J.matrix).PosDef) (hir : J.Irreducible) (i j : Fin N) :
    0 < J.green i j := by
  by_cases hij : i.val ≤ j.val
  · exact J.green_entry_pos_of_le hm hir i j hij
  · rw [J.green_symmetric hm j i]
    exact J.green_entry_pos_of_le hm hir j i (by omega)

end
end chebyshev2.Jacobi
