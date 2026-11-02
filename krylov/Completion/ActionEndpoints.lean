import krylov.Completion.ShortedCompletion
set_option autoImplicit false
/-!
Article: main_krylov, thm:radau, full-action spectral endpoints.
Use: construct actual lower and upper matrices in the closed spectral band
that preserve the entire known action A'S=AS, including singular endpoint blocks.
Source: the proved shorted positive forms, with the actual reference matrix
providing the common feasible interval.
-/

namespace krylov.Completion
noncomputable section
open Matrix
variable {n p : ℕ}

/-- The physical lower full-action endpoint in the closed spectral band.
Use: attain the lowest feasible directional curvature while preserving AS.
Article: main_krylov, thm:radau.
Proof: add the lower scalar endpoint to the minimal positive observed-action lift. -/
def lowerActionEndpoint (A : Matrix (Fin n) (Fin n) ℝ) (mu : ℝ)
    (hlo : (A-mu • 1).PosSemidef) (S : Matrix (Fin n) (Fin p) ℝ) :
    Matrix (Fin n) (Fin n) ℝ := mu • 1+shortedForm (A-mu • 1) hlo S

/-- The physical upper full-action endpoint in the closed spectral band.
Use: attain the highest feasible directional curvature while preserving AS.
Article: main_krylov, thm:radau.
Proof: subtract the minimal positive upper-shift action lift from the upper endpoint. -/
def upperActionEndpoint (A : Matrix (Fin n) (Fin n) ℝ) (L : ℝ)
    (hhi : (L • 1-A).PosSemidef) (S : Matrix (Fin n) (Fin p) ℝ) :
    Matrix (Fin n) (Fin n) ℝ := L • 1-shortedForm (L • 1-A) hhi S

/-- Both constructed full-action endpoints lie in the original closed spectral
band and preserve the entire prescribed physical action on S.
Use: provide actual feasible endpoint matrices under full-action constraints,
including singular shifted old models, with no completion-existence hypothesis.
Article: main_krylov, thm:radau, full-action constraints.
Proof: the shorted form lies between zero and the genuine shifted reference
matrix. Add its positive remainder to the opposite spectral inequality and
use its exact preserved physical action. -/
theorem full_action_endpoint_feasibility
    (A : Matrix (Fin n) (Fin n) ℝ) (S : Matrix (Fin n) (Fin p) ℝ) (mu L : ℝ)
    (hlo : (A-mu • 1).PosSemidef) (hhi : (L • 1-A).PosSemidef) :
    let Alo := lowerActionEndpoint A mu hlo S
    let Ahi := upperActionEndpoint A L hhi S
    (Alo-mu • 1).PosSemidef ∧ (L • 1-Alo).PosSemidef ∧ Alo*S=A*S ∧
      (Ahi-mu • 1).PosSemidef ∧ (L • 1-Ahi).PosSemidef ∧ Ahi*S=A*S := by
  obtain ⟨hPl,hRl,hSl⟩ := shorted_form_properties (A-mu • 1) hlo S
  obtain ⟨hPh,hRh,hSh⟩ := shorted_form_properties (L • 1-A) hhi S
  dsimp only
  refine ⟨?_,?_,?_,?_,?_,?_⟩
  · simpa only [lowerActionEndpoint,add_sub_cancel_left] using hPl
  · convert hhi.add hRl using 1
    unfold lowerActionEndpoint
    module
  · unfold lowerActionEndpoint
    rw [Matrix.add_mul,hSl,Matrix.sub_mul]
    module
  · convert hlo.add hRh using 1
    unfold upperActionEndpoint
    module
  · simpa only [upperActionEndpoint,sub_sub_cancel] using hPh
  · unfold upperActionEndpoint
    rw [Matrix.sub_mul,hSh,Matrix.sub_mul]
    module

/-- The actual shorted form depends only on the entire observed action.
Use: compare a candidate completion with the genuine reference without
requiring equality of their unknown operator blocks.
Article: main_krylov, thm:radau, full-action constraints.
Proof: both physical action columns and their compressed positive matrix agree;
the actual Moore--Penrose formula therefore agrees, including its kernel. -/
theorem shorted_form_same_action (M C : Matrix (Fin n) (Fin n) ℝ)
    (hM : M.PosSemidef) (hC : C.PosSemidef) (S : Matrix (Fin n) (Fin p) ℝ)
    (hact : M*S=C*S) : shortedForm M hM S=shortedForm C hC S := by
  have hcomp : Sᵀ*M*S=Sᵀ*C*S := by
    simpa only [Matrix.mul_assoc] using congrArg (fun X => Sᵀ*X) hact
  unfold shortedForm
  rw [hact]
  congr 2
  have hcongr (X Y : Matrix (Fin p) (Fin p) ℝ) (hX : X.IsHermitian) (hY : Y.IsHermitian)
      (he : X=Y) : krylov.LinearAlgebra.pseudoinverse X hX=krylov.LinearAlgebra.pseudoinverse Y hY := by
    subst Y
    rfl
  exact hcongr _ _ _ _ hcomp

/-- The constructed lower and upper matrices are the actual Loewner extrema
over every physical matrix in the band with the same full observed action.
Use: attain the full-action directional curvature endpoints simultaneously
for every direction, rather than merely proving existence of some extension.
Article: main_krylov, thm:radau, full-action constraints.
Proof: compare the positive shifted shorted forms using their equal physical
action. Their proved positive remainders give both exact extremal inequalities. -/
theorem full_action_endpoint_extrema
    (A C : Matrix (Fin n) (Fin n) ℝ) (S : Matrix (Fin n) (Fin p) ℝ) (mu L : ℝ)
    (hlo : (A-mu • 1).PosSemidef) (hhi : (L • 1-A).PosSemidef)
    (hClo : (C-mu • 1).PosSemidef) (hChi : (L • 1-C).PosSemidef)
    (hact : C*S=A*S) :
    (C-lowerActionEndpoint A mu hlo S).PosSemidef ∧
      (upperActionEndpoint A L hhi S-C).PosSemidef := by
  have hlow : (C-mu • 1)*S=(A-mu • 1)*S := by
    simp only [Matrix.sub_mul,hact]
  have hhigh : (L • 1-C)*S=(L • 1-A)*S := by
    simp only [Matrix.sub_mul,hact]
  have helo := shorted_form_same_action (C-mu • 1) (A-mu • 1) hClo hlo S hlow
  have hehi := shorted_form_same_action (L • 1-C) (L • 1-A) hChi hhi S hhigh
  have hrl := (shorted_form_properties (C-mu • 1) hClo S).2.1
  have hrh := (shorted_form_properties (L • 1-C) hChi S).2.1
  rw [helo] at hrl
  rw [hehi] at hrh
  constructor
  · convert hrl using 1
    unfold lowerActionEndpoint
    module
  · convert hrh using 1
    unfold upperActionEndpoint
    module

end
end krylov.Completion
