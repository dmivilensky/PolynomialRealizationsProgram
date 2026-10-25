import chebyshev2.Finite.Basic
import chebyshev1.SineJacobi.Terminal

/-!
Article: chebyshev2, Section 4.1, finite sine chain and terminal polynomial.
Use: the matrix spectrum and packing constructions use chain and terminal;
SineJacobi.Finite adds the energy and gain results on this same chain.
Source: chebyshev1, Appendix E, the explicit sine--Jacobi chain.
-/
namespace chebyshev2
noncomputable section
open chebyshev1 Polynomial Polynomial.Chebyshev
namespace SineJacobi

/--
Constructs `chain` of type `Jacobi N` by the displayed record fields. Data fields specify the
construction; proof fields discharge its required properties.

Use: `chebyshev2.SineJacobi.energy_eq` rewrites with this definition to establish exact
identity `(chain N).energy = ∑ s ∈ Finset.range N, chebyshev1.SineJacobi.greenWeight N
s^2`.

Article: chebyshev2, Theorem 1.2 via `chebyshev2.Optimal.greenConstant_le_sine`.
-/
def chain (N : ℕ) : Jacobi N where
  data := chebyshev1.SineJacobi.data N
  coupling_nonneg := chebyshev1.SineJacobi.data_aSq_nonneg N
  coupling_zero := chebyshev1.SineJacobi.data_aSq_zero N
  diagonal_tail _ _ := rfl
  coupling_tail i hi := by   simp [chebyshev1.SineJacobi.data, show ¬(0 < i ∧ i < N) by omega]

/--
The precise assertion is `(chain N).Terminal`.

Use: `chebyshev2.SineJacobi.fiber` uses this assertion in the displayed construction of
`fiber`. Its inputs and component formulas are fixed by that definition.

Article: chebyshev2, Theorem 2.5 via `chebyshev2.SineJacobi.gain_exact`.

Proof: Use the identities/estimates `chebyshev2.fiberPolynomial_eq`,
`chebyshev1.SineJacobi.terminal` with the arguments shown in the proof.
-/
theorem terminal (N : ℕ) (hN : 0 < N) : (chain N).Terminal := by
  change (chebyshev1.SineJacobi.data N).leading N = fiberPolynomial N
  rw [fiberPolynomial_eq N hN]
  exact chebyshev1.SineJacobi.terminal N hN

end SineJacobi
end
end chebyshev2
