import krylov.Envelope.SelectionDualSupport

set_option autoImplicit false
/-!
Article: main_krylov, thm:select, attained actual nuclear-norm selection formula.
Use: identify the real common-tilt minimax value with the attained
printed nuclear support maximum over actual source unit polynomials.
Source: compact actual increment maximizers, polynomial flag coverage,
real Cauchy--Schwarz and the proved attained directional spectral/nuclear duality.
-/

namespace krylov.Envelope
noncomputable section
open krylov.Reference krylov.Methods krylov.LinearAlgebra Polynomial Matrix Set
open scoped BigOperators Matrix.Norms.L2Operator NNReal
variable {n : ℕ}

/-- The actual common-tilt selection value equals the attained maximum of the printed weighted nuclear support over the genuine source unit polynomial set, including all degenerate budgets.
Use: The actual common-tilt selection value equals the attained maximum of the printed weighted nuclear support over the genuine source unit polynomial set, including all degenerate budgets.
Article: main_krylov, thm:select, attained actual nuclear-norm selection formula.
Proof: Every unit polynomial support is bounded by the true selection value. Normalize an actual nonzero maximizing tilt and cover it by a real degree-bounded polynomial for the reverse inequality. If the true value is zero, any actual unit polynomial attains zero. -/
theorem selection_nuclear_dual (base : Matrix (Fin n) (Fin n) ℝ) (hb : base.PosDef)
    (g : EuclideanSpace ℝ (Fin n)) (N : ℕ) (hN : 2≤N) (hcount : N≤referenceAtomCount base hb g)
    (ω : Fin (N-1) → ℝ≥0) :
    IsGreatest (selectionSupport base g N ω '' unitPolynomialSet base g N) (selectionValue base g N ω) := by
  -- The true upper bound is uniform over all actual unit polynomial directions; an actual maximizing tilt constructs a direction attaining equality.
  have hupper : ∀ p∈unitPolynomialSet base g N,
      selectionSupport base g N ω p≤selectionValue base g N ω :=
    fun p hp => selectionSupport_le_value base hb g N hN hcount ω p hp
  refine ⟨?_,by rintro r ⟨p,hp,rfl⟩;exact hupper p hp⟩
  -- Zero budgets require no normalization of a zero response: genuine nonempty unit directions and nonnegative supports settle that case.
  by_cases hz : selectionValue base g N ω=0
  · obtain ⟨p,hp⟩ := unitPolynomialSet_nonempty base hb g N (by omega) hcount
    refine ⟨p,hp,?_⟩
    exact le_antisymm (hupper p hp) (by rw [hz];exact selectionSupport_nonneg base hb g N hN hcount ω p hp.1)
  · obtain ⟨E,hE,hval⟩ := (selectionValue_attained base g N ω).1
    dsimp only at hval
    let v := canonicalTiltLinear base g N E
    have hv : v≠0 := by
      intro he
      apply hz
      rw [← hval,show canonicalTiltLinear base g N E=0 from he,_root_.norm_zero]
    let u := NormedSpace.normalize v
    have humem : u∈exploredFlag base g N :=
      Submodule.smul_mem _ _ (canonicalTiltLinear_mem_flag base g N E)
    obtain ⟨p,hp,hpu⟩ := canonicalPolynomialVector_covers base hb g N (by omega) hcount u humem
    have hpunit : p∈unitPolynomialSet base g N := ⟨hp,hpu ▸ NormedSpace.norm_normalize hv⟩
    refine ⟨p,hpunit,le_antisymm (hupper p hpunit) ?_⟩
    have hlo := (selection_polynomial_support base hb g N hN hcount ω p hp).2 ⟨E,hE,rfl⟩
    change inner ℝ (canonicalPolynomialVector base g p) v≤_ at hlo
    rw [hpu,real_inner_comm,inner_normalize] at hlo
    rw [← hval]
    exact hlo
end
end krylov.Envelope
