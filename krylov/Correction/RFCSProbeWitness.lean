import krylov.Correction.RFCSSource
import krylov.Correction.CompactScenarioBounds

/-!
Article: main_krylov, thm:RFCS, sharp actual finite-source probe bound.
Use: one real quadratic remainder tube covers every original finite
increment and independent probe-defect scenario; actual final isotropic
probe witnesses attain the sharp first-order coefficient.
Source: genuine independent-probe execution and full terminal expansion,
actual finite symmetric source coordinates and original spectral budgets.
-/

namespace krylov.Correction
noncomputable section
open Matrix Filter Asymptotics Topology krylov.Methods krylov.Reference krylov.Stability krylov.LinearAlgebra krylov.Envelope krylov.Variation
open scoped Matrix.Norms.L2Operator InnerProductSpace
variable {k : ℕ}

/-- The actual admissible finite source whose sole perturbation is the last isotropic probe mismatch.
Use: attain the first-order source coefficient without any earlier increment or probe defect.
Article: main_krylov, thm:RFCS, Eᵖ_last=qI and all other defects zero. -/
def rfcsLastProbeScenario (k : ℕ) (q : ℝ) : symmetricScenarios (k+1) (k+1) :=
  ⟨(0,fun i => if i.val=k then q • (1 : Matrix (Fin (k+1)) (Fin (k+1)) ℝ) else 0),by
    -- Every actual source coordinate is either a real symmetric scalar identity or zero.
    constructor
    · intro i
      exact Matrix.isSymm_zero
    · intro i
      change (if i.val=k then q • (1 : Matrix (Fin (k+1)) (Fin (k+1)) ℝ) else 0).IsSymm
      split_ifs
      · exact Matrix.isSymm_one.smul _
      · exact Matrix.isSymm_zero⟩

/-- The real isotropic last-probe witness satisfies every original finite spectral budget with maximum at most |q| and has exactly the stated actual terminal mismatch.
Use: the sharp RFC-S coefficient is attained by a genuine source scenario, including the zero profile.
Article: main_krylov, thm:RFCS, actual last-probe witness admissibility.
Proof: all actual increment slots and nonterminal probes vanish. The one
real terminal mismatch is qI, whose genuine spectral norm is exactly |q|;
the finite source extension reads that original last coordinate exactly. -/
theorem rfcsLastProbeScenario_spec (k : ℕ) (q : ℝ) :
    ‖rfcsLastProbeScenario k q‖≤|q| ∧
      matrixSequenceExtension (k+1) (rfcsLastProbeScenario k q).val.2 k=q • (1 : Matrix (Fin (k+1)) (Fin (k+1)) ℝ) := by
  -- Check the true finite product budget and actual final probe coordinate directly.
  refine ⟨?_,?_⟩
  · apply symmetricScenario_norm_le _ (abs_nonneg q)
    · intro i
      simpa only [rfcsLastProbeScenario,Pi.zero_apply,norm_zero] using abs_nonneg q
    · intro i
      change ‖if i.val=k then q • (1 : Matrix (Fin (k+1)) (Fin (k+1)) ℝ) else 0‖≤|q|
      split_ifs
      · simp only [norm_smul,Real.norm_eq_abs,norm_one,mul_one,le_refl]
      · simpa only [norm_zero] using abs_nonneg q
  · simp only [matrixSequenceExtension,dite_eq_left (Nat.lt_succ_self k),rfcsLastProbeScenario,ite_true]

end
end krylov.Correction
