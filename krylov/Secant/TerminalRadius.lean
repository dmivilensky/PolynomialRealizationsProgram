import krylov.Secant.TerminalPlane
import krylov.Reference.CG

/-!
Article: Lemma B.4 [lem:terminal-fibre] of krylov.tex.
Use: apply the actual common-probe formula to the true line search and the
proved information lower bound to the actual two final matrix completions.
Source: actual planar operators, nonsingular matrix actions and two-scenario radius calculus.
-/

namespace krylov.Secant
noncomputable section
open Matrix krylov.LinearAlgebra krylov.Reference
open scoped Matrix Matrix.Norms.L2Operator InnerProductSpace
variable {n : ℕ}

/-- The true normalized terminal line search has its reference length and exact planar post-search gradient.
Use: computes the actual terminal residual from the common actual last probe.
Article: main_krylov, lem:terminal-fibre, ρ=x√c e.
Proof: actual unit/orthogonal pairings make the last curvature exactly one;
the true line length is a and cancellation leaves precisely the cross component. -/
theorem terminal_line_search (e h : EuclideanSpace ℝ (Fin n)) (hh : ‖h‖=1)
    (heh : inner ℝ e h=0) (a x : ℝ) :
    lineLength (-a • h) h (h+x • e)=a ∧
      searchedGradient (-a • h) h (h+x • e)=(x*a) • e := by
  have hhe : inner ℝ h e=0 := (real_inner_comm e h).trans heh
  have hl : lineLength (-a • h) h (h+x • e)=a := by
    simp only [lineLength, real_inner_smul_right, inner_add_right, hhe,
      real_inner_self_eq_norm_sq, hh, one_pow, mul_one, mul_zero, add_zero, neg_neg, div_one]
  refine ⟨hl, ?_⟩
  rw [searchedGradient, hl, smul_add, smul_smul]
  module

/-- Every actual common final correction obeys the exact two-completion information lower bound.
Use: the hidden final diagonal is unavailable before the common correction decision.
Article: main_krylov, lem:terminal-fibre, displayed worst-residual lower bound.
Proof: apply the proved pointwise two-scenario estimate to the actual mean
matrix action and cancel its true inverse in K M; distribute the two actual output matrices. -/
theorem terminal_two_scenario_lower (M Δ : Matrix (Fin n) (Fin n) ℝ)
    (hM : IsUnit M.det) (ρ u : EuclideanSpace ℝ (Fin n)) :
    let K := Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ) (Δ*M⁻¹)
    ‖K ρ‖/Real.sqrt (1+‖K‖^2) ≤
      max ‖ρ+Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ) (M+Δ) u‖
        ‖ρ+Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ) (M-Δ) u‖ := by
  -- The common correction is arbitrary; only the actual inverse-mean cancellation is used.
  dsimp only
  have h := two_scenario_operator_lower
    (Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ) (Δ*M⁻¹)) ρ
    (Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ) M u)
  have he : Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ) (Δ*M⁻¹)
      (Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ) M u)=
        Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ) Δ u := by
    rw [← mul_apply_eq_comp, ← map_mul, Matrix.mul_assoc, nonsing_inv_mul _ hM, Matrix.mul_one]
  rw [he] at h
  simpa only [map_add, map_sub, map_neg, _root_.add_apply, _root_.sub_apply, _root_.neg_apply,
    add_assoc, sub_eq_add_neg] using h

/-- The actual inverse-mean centre leaves the two opposite actual hidden-diagonal residuals.
Use: the centre correction is an explicit feasible actual vector, with the exact printed signs.
Article: main_krylov, lem:terminal-fibre, centre −M⁻¹ρ.
Proof: expand both actual matrix actions and cancel the true mean matrix times its inverse. -/
theorem terminal_centre_residuals (M Δ : Matrix (Fin n) (Fin n) ℝ)
    (hM : IsUnit M.det) (ρ : EuclideanSpace ℝ (Fin n)) :
    (ρ+Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ) (M+Δ)
      (-(Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ) M⁻¹ ρ))=
        -(Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ) (Δ*M⁻¹) ρ)) ∧
    (ρ+Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ) (M-Δ)
      (-(Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ) M⁻¹ ρ))=
        Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ) (Δ*M⁻¹) ρ) := by
  have he : Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ) M
      (Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ) M⁻¹ ρ)=ρ := by
    rw [← mul_apply_eq_comp, ← map_mul, mul_nonsing_inv _ hM, map_one, one_apply_eq_self]
  simp only [map_add, map_sub, map_neg, _root_.add_apply, _root_.sub_apply, he,
    map_mul, mul_apply_eq_comp]
  constructor <;> abel

end
end krylov.Secant
