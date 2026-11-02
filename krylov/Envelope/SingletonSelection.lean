import krylov.Envelope.SingletonSelectionProduct
import krylov.Envelope.SingletonCoefficient

set_option autoImplicit false
/-!
Article: main_krylov, thm:select, exact positive actual last-singleton selection constant.
Use: identify the genuine last meaningful singleton minimax coefficient
with precisely the printed true horizon indices and prove actual positivity.
Source: proved genuine attained rank-two singleton selection product
and actual measured CG energy/beta normalization and positive active domains.
-/

namespace krylov.Envelope
noncomputable section
open krylov.Reference krylov.Methods krylov.Secant krylov.Stability Matrix
open scoped Matrix.Norms.L2Operator NNReal
variable {n : ℕ}

/-- The actual last-nontrivial singleton selection value equals exactly the printed beta and three-energy formula at the genuine source horizon indices.
Use: The actual last-nontrivial singleton selection value equals exactly the printed beta and three-energy formula at the genuine source horizon indices.
Article: main_krylov, thm:select, exact positive actual last-singleton selection constant.
Proof: Combine the true attained symmetric two-plane selection product with the actual measured CG scalar identity and identify the genuine predecessor indices. -/
theorem selectionValue_last_singleton (base : Matrix (Fin n) (Fin n) ℝ) (hb : base.PosDef)
    (g : EuclideanSpace ℝ (Fin n)) (N : ℕ) (hN : 3≤N) (hcount : N<referenceAtomCount base hb g) :
    selectionValue base g N (Pi.single ⟨N-3,by omega⟩ 1)=
      CG.beta (cgOperator base) g (N-1)*Real.sqrt
        (cgEnergy base g (N-2)*(cgEnergy base g (N-1)+cgEnergy base g N)/cgEnergy base g N) := by
  obtain ⟨k,rfl⟩ : ∃ k, N=k+3 := ⟨N-3,by omega⟩
  simpa only [show k+3-3=k by omega,show k+3-2=k+1 by omega,show k+3-1=k+2 by omega] using
    (selectionValue_last_singleton_product base hb g k hcount).trans (singleton_tilt_coefficient base hb g k hcount)

/-- The genuine actual last-nontrivial singleton selection value is strictly positive before true active exhaustion.
Use: The genuine actual last-nontrivial singleton selection value is strictly positive before true active exhaustion.
Article: main_krylov, thm:select, exact positive actual last-singleton selection constant.
Proof: The proved actual singleton value equals the genuine positive measured beta/energy coefficient. -/
theorem selectionValue_last_singleton_pos (base : Matrix (Fin n) (Fin n) ℝ) (hb : base.PosDef)
    (g : EuclideanSpace ℝ (Fin n)) (N : ℕ) (hN : 3≤N) (hcount : N<referenceAtomCount base hb g) :
    0<selectionValue base g N (Pi.single ⟨N-3,by omega⟩ 1) := by
  obtain ⟨k,rfl⟩ : ∃ k, N=k+3 := ⟨N-3,by omega⟩
  have hp := singleton_tilt_coefficient_pos base hb g k hcount
  rw [← singleton_tilt_coefficient base hb g k hcount,← selectionValue_last_singleton_product base hb g k hcount] at hp
  simpa only [show k+3-3=k by omega] using hp
end
end krylov.Envelope
