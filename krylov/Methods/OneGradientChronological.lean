import krylov.Methods.VirtualCoordinates
set_option autoImplicit false
/-!
Article: main_krylov, thm:E1, actual chronological virtual-solve coefficients.
Use: express the real newest-first stored-window virtual solve in the original chronological query coordinates before forming actual injections and output segments.
Source: the exact full-memory finite-array identity and genuine finite reversal equivalence.
-/

namespace krylov.Methods
noncomputable section
open Matrix
open scoped BigOperators
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The actual computed full-memory virtual-solve coefficients in genuine chronological evaluated-query order.
Use: The actual computed full-memory virtual-solve coefficients in genuine chronological evaluated-query order.
Article: main_krylov, thm:E1, actual chronological virtual-solve coefficients.
Proof: Read the native newest-age model coefficients at the reversed actual finite index. -/
def oneGradientVirtualCoefficients (m : OneGradientMethod E) (A : ℕ → E →L[ℝ] E) (g : E) (k : ℕ) : Fin k → ℝ :=
  fun i => modelCoefficients
    (fun j : Fin k => oneGradientStep m A g (k-1-j.val))
    (pairModel (fun j : Fin k => oneGradientStep m A g (k-1-j.val))
      (fun j : Fin k => A (k-1-j.val) (oneGradientStep m A g (k-1-j.val))))
    (oneGradientGradient m A g k) i.rev

/-- Reversing genuine newest-age combination indices gives the exact original chronological physical sum.
Use: Reversing genuine newest-age combination indices gives the exact original chronological physical sum.
Article: main_krylov, thm:E1, actual chronological virtual-solve coefficients.
Proof: Use the actual finite reversal equivalence and its true chronological index identity. -/
theorem combine_reverse_chronological (v : ℕ → E) (k : ℕ) (c : Fin k → ℝ) :
    combine (fun i : Fin k => v (k-1-i.val)) c=∑ i : Fin k,c i.rev • v i.val := by
  have he (i : Fin k) : k-1-i.rev.val=i.val := by simp only [Fin.val_rev];omega
  have h := Equiv.sum_comp (Fin.revPerm (n := k)) (fun i : Fin k => c i • v (k-1-i.val))
  simpa only [Fin.revPerm_apply,he,combine] using h.symm

/-- The actual full-memory correction and effective gradient have the genuine chronological coefficient formulas on the true evaluated query transcript.
Use: The actual full-memory correction and effective gradient have the genuine chronological coefficient formulas on the true evaluated query transcript.
Article: main_krylov, thm:E1, actual chronological virtual-solve coefficients.
Proof: Reindex both native physical combinations by the same actual finite reversal. -/
theorem oneGradient_chronological_virtual (m : OneGradientMethod E) (A : ℕ → E →L[ℝ] E) (g : E) (k : ℕ) :
    let H := oneGradientRun m A g k
    virtualCorrection (selectedWindow fullMemory H) H.gradient=
      ∑ i : Fin k,oneGradientVirtualCoefficients m A g k i • oneGradientStep m A g i.val ∧
    virtualGradient (selectedWindow fullMemory H) H.gradient=H.gradient+
      ∑ i : Fin k,oneGradientVirtualCoefficients m A g k i • A i.val (oneGradientStep m A g i.val) := by
  have h := oneGradient_full_virtual_coordinates m A g k
  dsimp only at h ⊢
  rw [h.1,h.2,combine_reverse_chronological,
    combine_reverse_chronological (fun i => A i (oneGradientStep m A g i)) k]
  exact ⟨rfl,rfl⟩
end
end krylov.Methods
