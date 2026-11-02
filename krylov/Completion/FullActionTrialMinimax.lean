import krylov.Completion.PhysicalTrialMinimax
import krylov.Completion.FullActionSchurRange
set_option autoImplicit false
/-!
Article: main_krylov, thm:radau, unique full-action physical trial minimax.
Use: retain every original observed action column and optimize the actual
trial over the genuine physical completion class, including singular endpoints.
Source: constructed true full-action Loewner extrema, actual positive spectral
band and the proved attained physical searched-step minimax.
-/

namespace krylov.Completion
noncomputable section
open Matrix
variable {n p : ℕ}

/-- The original physical completion family preserving the entire observed action.
Use: full-action minimax uncertainty has real matrices and the exact original AS.
Article: main_krylov, thm:radau. -/
def fullActionCompletions (A : Matrix (Fin n) (Fin n) ℝ) (S : Matrix (Fin n) (Fin p) ℝ)
    (mu L : ℝ) : Set (Matrix (Fin n) (Fin n) ℝ) :=
  {C | (C-mu • 1).PosSemidef ∧ (L • 1-C).PosSemidef ∧ C*S=A*S}

/-- The genuine full-action physical trial problem has its exact attained
midpoint-curvature minimax value, with a unique minimizing real trial.
Use: the actual physical endpoint matrices preserve the complete original
observed action, rather than just its compressed Gram; their source Schur
curvature formulas are supplied by full_action_schur_curvature_range.
Article: main_krylov, thm:radau, full-action minimax.
Proof: actual shorted-form endpoints are feasible Loewner extrema and their
affine segment attains every curvature. The positive spectral lower bound and
the actual nonzero direction derive the strictly positive endpoint curvature.
The proved genuine physical trial minimax therefore applies without any
nondegenerate-width or nonsingular shifted-old-model assumption. -/
theorem full_action_trial_minimax
    (A : Matrix (Fin n) (Fin n) ℝ) (S : Matrix (Fin n) (Fin p) ℝ)
    (d : Fin n → ℝ) (hd : d≠0) (mu L q : ℝ) (hmu : 0<mu) (hq : 0<q)
    (hlo : (A-mu • 1).PosSemidef) (hhi : (L • 1-A).PosSemidef) :
    let cl := d ⬝ᵥ (lowerActionEndpoint A mu hlo S*ᵥ d)
    let ch := d ⬝ᵥ (upperActionEndpoint A L hhi S*ᵥ d)
    let C := fullActionCompletions A S mu L
    IsLeast {v : ℝ | ∃ t : ℝ,IsGreatest ((fun B => |1-t/physicalTrialLength d q B|) '' C) v}
      ((ch-cl)/(ch+cl)) ∧
      (∀ t : ℝ,(∀ B∈C,|1-t/physicalTrialLength d q B|≤(ch-cl)/(ch+cl)) ↔ t=2*q/(cl+ch)) := by
  let cl := d ⬝ᵥ (lowerActionEndpoint A mu hlo S*ᵥ d)
  let ch := d ⬝ᵥ (upperActionEndpoint A L hhi S*ᵥ d)
  let C := fullActionCompletions A S mu L
  have hrange (c : ℝ) : (∃ B∈C,d ⬝ᵥ (B*ᵥ d)=c) ↔ c∈Set.Icc cl ch := by
    have h := full_action_curvature_range A S d mu L c hlo hhi
    constructor
    · rintro ⟨B,⟨hBl,hBh,hact⟩,he⟩
      exact h.mp ⟨B,hBl,hBh,hact,he⟩
    · intro hc
      obtain ⟨B,hBl,hBh,hact,he⟩ := h.mpr hc
      exact ⟨B,⟨hBl,hBh,hact⟩,he⟩
  have hcurv := (hrange (d ⬝ᵥ (A*ᵥ d))).mp ⟨A,⟨hlo,hhi,rfl⟩,rfl⟩
  have horder : cl≤ch := hcurv.1.trans hcurv.2
  have hcl : 0<cl := by
    have hl := (full_action_endpoint_feasibility A S mu L hlo hhi).1
    have hquad := hl.dotProduct_mulVec_nonneg d
    simp only [star_trivial,sub_mulVec,smul_mulVec,Matrix.one_mulVec,dotProduct_sub,
      dotProduct_smul,smul_eq_mul] at hquad
    have hD : 0<d ⬝ᵥ d := by
      simpa only [star_trivial,Matrix.one_mulVec] using
        (Matrix.PosDef.one : (1 : Matrix (Fin n) (Fin n) ℝ).PosDef).dotProduct_mulVec_pos hd
    change 0<d ⬝ᵥ (lowerActionEndpoint A mu hlo S*ᵥ d)
    nlinarith [mul_pos hmu hD]
  exact physical_trial_minimax C d q cl ch hq hcl horder hrange

end
end krylov.Completion
