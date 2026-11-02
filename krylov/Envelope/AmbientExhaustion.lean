import krylov.Envelope.CanonicalFiltration

set_option autoImplicit false
/-!
Article: main_krylov, thm:E, genuine full ambient exhaustion boundary.
Use: identify the actual complete explored flag and vanishing genuine
unexplored response when the true active count fills the ambient space.
Source: actual orthonormal CG frame and the genuine finite-dimensional
independent full-cardinality spanning theorem.
-/

namespace krylov.Envelope
noncomputable section
open krylov.Reference krylov.Methods krylov.Secant krylov.Stability krylov.Variation Matrix
variable {n : ℕ}

/-- If the genuine active CG atom count equals the actual ambient dimension, the true full explored flag is the entire real space.
Use: If the genuine active CG atom count equals the actual ambient dimension, the true full explored flag is the entire real space.
Article: main_krylov, thm:E, genuine full ambient exhaustion boundary.
Proof: The actual nonstagnating CG prefix is orthonormal with true full ambient cardinality, hence spans; the genuine zero-dimensional case is included. -/
theorem exploredFlag_ambient_exhaustion (base : Matrix (Fin n) (Fin n) ℝ) (hb : base.PosDef)
    (g : EuclideanSpace ℝ (Fin n)) (hfull : referenceAtomCount base hb g=n) :
    exploredFlag base g n=⊤ := by
  cases n with
  | zero => exact Subsingleton.elim _ _
  | succ n =>
    have hq := canonicalCGUnitStep_orthonormal base hb g (n+1)
      (fun i hi => cg_nonstagnation base hb g i (by omega))
    exact hq.linearIndependent.span_eq_top_of_card_eq_finrank (by simp)

/-- The genuine common unexplored response vanishes at true full ambient exhaustion.
Use: The genuine common unexplored response vanishes at true full ambient exhaustion.
Article: main_krylov, thm:E, genuine full ambient exhaustion boundary.
Proof: The actual explored flag is the whole real space, so its genuine orthogonal projection fixes the true frozen response. -/
theorem commonTransverseResponse_ambient_exhaustion (base : Matrix (Fin n) (Fin n) ℝ) (hb : base.PosDef)
    (g : EuclideanSpace ℝ (Fin n)) (hfull : referenceAtomCount base hb g=n)
    (A : ℝ → ℕ → EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)) :
    commonTransverseResponse base g A n=0 := by
  unfold commonTransverseResponse
  have hmem : canonicalFrozenResponse base g A n∈exploredFlag base g n := by
    rw [exploredFlag_ambient_exhaustion base hb g hfull]
    trivial
  rw [(exploredFlag base g n).starProjection_eq_self_iff.mpr hmem,sub_self]
end
end krylov.Envelope
