import Mathlib.Algebra.Polynomial.Sequence
import Mathlib.LinearAlgebra.LinearIndependent.Basic
import Mathlib.Tactic

/-!
Article: bezout, Theorem 2.1, constructive converse in Appendix A.
Graded finite polynomial families and their unique coordinate expansions.
Use: synthesis expands each divided query and the divided terminal in exactly
the causally available earlier queries. The zero polynomial is included through
the degree inequality, so the initial query needs no exceptional coefficient.
Proof: extend a finite graded family by monomials, apply the polynomial-sequence
span theorem, and restrict its linear independence back to the finite horizon.
-/

namespace bezout
noncomputable section
open Polynomial Module
open scoped BigOperators

/-- A degree-ordered family of exactly `N` nonzero real polynomials.
Use: records the causal degree order in the realization converse of Theorem 2.1. -/
structure GradedFamily (N : ℕ) where
  poly : Fin N → ℝ[X]
  degree_eq : ∀ s, (poly s).degree = (s.val : WithBot ℕ)

namespace GradedFamily
variable {N : ℕ} (Q : GradedFamily N)

/-- Extend the given finite family by ordinary monomials.
Use: imports the general polynomial-sequence basis theorem without adding
normalization hypotheses outside the prescribed horizon. -/
def sequence : Polynomial.Sequence ℝ where
  elems' n := if h : n < N then Q.poly ⟨n, h⟩ else X ^ n
  degree_eq' n := by
    split_ifs with h
    · exact Q.degree_eq ⟨n, h⟩
    · exact Polynomial.degree_X_pow n

/-- The infinite extension agrees with each prescribed query polynomial.
Use: transfers both spanning and linear independence to `Fin N`. -/
@[simp] theorem sequence_fin (s : Fin N) : Q.sequence s = Q.poly s := by
  simp [sequence, s.isLt]

/-- The prescribed family is linearly independent.
Use: makes all synthesized history coefficients and Bezoutian factors unique. -/
theorem linearIndependent : LinearIndependent ℝ Q.poly := by
  have h := Q.sequence.linearIndependent.comp (fun s : Fin N => s.val) Fin.val_injective
  convert h using 1
  funext s
  exact (Q.sequence_fin s).symm

/-- The given finite queries span exactly the degree-bounded polynomial space.
Use: proves existence of each row and output-weight expansion in Theorem 2.1. -/
theorem span_eq_degreeLT :
    Submodule.span ℝ (Set.range Q.poly) = Polynomial.degreeLT ℝ N := by
  have hrange : Set.range Q.poly = Q.sequence '' Set.Iio N := by
    ext p
    constructor
    · rintro ⟨s, rfl⟩
      exact ⟨s.val, s.isLt, Q.sequence_fin s⟩
    · rintro ⟨s, hs, rfl⟩
      exact ⟨⟨s, hs⟩, (Q.sequence_fin ⟨s, hs⟩).symm⟩
  rw [hrange]
  exact Q.sequence.span_degreeLT (fun i _ => isUnit_iff_ne_zero.mpr
    (Polynomial.leadingCoeff_ne_zero.mpr (Q.sequence.ne_zero i)))

/-- Every polynomial below the horizon has exactly one finite coordinate vector.
Use: constructive reconstruction of the unique causal history from its graded basis. -/
theorem existsUnique_expansion (p : ℝ[X]) (hp : p.degree < (N : WithBot ℕ)) :
    ∃! c : Fin N → ℝ, ∑ s, c s • Q.poly s = p := by
  have hmem : p ∈ Submodule.span ℝ (Set.range Q.poly) := by
    rw [Q.span_eq_degreeLT]
    exact Polynomial.mem_degreeLT.mpr hp
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun ℝ).mp hmem
  refine ⟨c, hc, fun d hd => ?_⟩
  exact Q.linearIndependent.fintypeLinearCombination_injective (by
    simpa only [Fintype.linearCombination_apply] using hd.trans hc.symm)

/-- The unique coordinate vector of a degree-bounded polynomial.
Use: provides actual coefficients for the synthesized history, rather than
an existence assumption in its defining structure. -/
def coordinates (p : ℝ[X]) (hp : p.degree < (N : WithBot ℕ)) : Fin N → ℝ :=
  (Q.existsUnique_expansion p hp).choose

/-- Reassembling the synthesized coordinates recovers the original polynomial.
Use: the row and output identities of the realization converse. -/
theorem sum_coordinates (p : ℝ[X]) (hp : p.degree < (N : WithBot ℕ)) :
    ∑ s, Q.coordinates p hp s • Q.poly s = p :=
  (Q.existsUnique_expansion p hp).choose_spec.1

/-- An expansion in a graded family has unique coefficients, without degree hypotheses.
Use: compares the actual history recurrence with the synthesized recurrence. -/
theorem expansion_unique (c d : Fin N → ℝ)
    (h : ∑ s, c s • Q.poly s = ∑ s, d s • Q.poly s) : c = d :=
  Q.linearIndependent.fintypeLinearCombination_injective (by
    simpa only [Fintype.linearCombination_apply] using h)

/-- Restrict the degree-ordered family to an earlier causal prefix.
Use: row `s` may depend only on the first `s` query polynomials. -/
def restrict (m : ℕ) (hm : m ≤ N) : GradedFamily m where
  poly s := Q.poly (s.castLE hm)
  degree_eq s := Q.degree_eq (s.castLE hm)

/-- Prefix restriction preserves the displayed query polynomial.
Use: rewrites row expansions into the full horizon's indexing convention. -/
@[simp] theorem prefix_poly (m : ℕ) (hm : m ≤ N) (s : Fin m) :
    (Q.restrict m hm).poly s = Q.poly (s.castLE hm) := rfl

end GradedFamily
end
end bezout
