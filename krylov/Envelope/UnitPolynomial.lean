import krylov.Envelope.PolynomialCoverage

set_option autoImplicit false
/-!
Article: main_krylov, thm:select, actual unit polynomial directions.
Use: impose the true source polynomial degree and unit canonical-vector
constraints, and prove their genuine nonemptiness on an active prefix.
Source: actual orthonormal CG steps and genuine polynomial flag coverage.
-/

namespace krylov.Envelope
noncomputable section
open krylov.Reference Polynomial
variable {n : ℕ}

/-- The true source set of degree-admissible polynomials with actual unit canonical polynomial vector.
Use: The true source set of degree-admissible polynomials with actual unit canonical polynomial vector.
Article: main_krylov, thm:select, actual unit polynomial directions.
Proof: Impose the real strict degree bound and the genuine canonical-vector norm equality. -/
def unitPolynomialSet (base : Matrix (Fin n) (Fin n) ℝ) (g : EuclideanSpace ℝ (Fin n)) (N : ℕ) : Set ℝ[X] :=
  {p | p.natDegree<N ∧ ‖canonicalPolynomialVector base g p‖=1}

/-- The actual source unit polynomial set is nonempty on every positive true active reference prefix.
Use: The actual source unit polynomial set is nonempty on every positive true active reference prefix.
Article: main_krylov, thm:select, actual unit polynomial directions.
Proof: Take the genuine first normalized CG step, use actual orthonormality, and represent it by the proved degree-bounded source polynomial. -/
theorem unitPolynomialSet_nonempty (base : Matrix (Fin n) (Fin n) ℝ) (hb : base.PosDef)
    (g : EuclideanSpace ℝ (Fin n)) (N : ℕ) (hN : 0<N) (hcount : N≤referenceAtomCount base hb g) :
    (unitPolynomialSet base g N).Nonempty := by
  let u := canonicalCGUnitStep base g 0
  have hu : u∈exploredFlag base g N := Submodule.subset_span ⟨⟨0,hN⟩,rfl⟩
  have hn : ‖u‖=1 := (canonicalCGUnitStep_orthonormal base hb g N
    (fun i hi => cg_nonstagnation base hb g i (hi.trans_le hcount))).norm_eq_one ⟨0,hN⟩
  obtain ⟨p,hp,he⟩ := canonicalPolynomialVector_covers base hb g N hN hcount u hu
  exact ⟨p,hp,he ▸ hn⟩
end
end krylov.Envelope
