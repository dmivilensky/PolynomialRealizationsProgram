import krylov.Envelope.RawSchurInverse
import krylov.LinearAlgebra.PrincipalInverseBounds
set_option autoImplicit false
/-!
Article: main_krylov, prop:phi(a), actual Schur Ritz interval.
Use: enclose true continuation zeros by the genuine original finite compression spectrum.
Source: the actual suffix principal inverse identity and genuine positive principal inverse spectral bounds.
-/

namespace krylov.Envelope
noncomputable section
open krylov.Realization krylov.LinearAlgebra Matrix
variable {N : ℕ}

/-- Every true prefix Schur eigenvalue lies in any actual positive spectral interval of the original physical matrix.
Use: Every true prefix Schur eigenvalue lies in any actual positive spectral interval of the original physical matrix.
Article: main_krylov, prop:phi(a), actual Schur Ritz interval.
Proof: Use the actual injective physical suffix inclusion and the proved genuine Schur inverse principal block identity. -/
theorem rawSchur_spectral_interval (T : Matrix (Fin N) (Fin N) ℝ) (hT : T.PosDef)
    (j : ℕ) (hj : j≤N) (a b : ℝ) (ha : 0 < a) (hb : 0 < b)
    (hlo : ∀ i,a≤hT.1.eigenvalues i) (hhi : ∀ i,hT.1.eigenvalues i≤b) :
    ∀ i,a≤(rawSchurComplement_posDef T hT j hj).1.eigenvalues i ∧
      (rawSchurComplement_posDef T hT j hj).1.eigenvalues i≤b := by
  -- The true contiguous suffix inclusion is injective even at the empty boundary.
  let f : Fin (N-j) → Fin N := fun i => ⟨j+i.val,by omega⟩
  have hf : Function.Injective f := by
    intro i l h
    apply Fin.ext
    have hval := congrArg Fin.val h
    dsimp only [f] at hval
    omega
  exact principal_inverse_spectral_interval T hT _ (rawSchurComplement_posDef T hT j hj) f hf
    (rawSchur_inverse T hT j hj).symm a b ha hb hlo hhi
end
end krylov.Envelope
