import bezout.Synthesis.Normalized
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Chebyshev.Extremal

/-!
Article: bezout, Introduction and Equation `eq:terminal`, prescribed minimax terminal.
Use: the stated normalized Chebyshev polynomial is an attained minimizer
over all real polynomials of degree at most N taking value one at zero.
Proof: the exterior Chebyshev extremal inequality, transported through the
invertible affine spectral coordinate. The zero-bound case is excluded explicitly.
-/

namespace bezout.Properties
noncomputable section
open Polynomial Polynomial.Chebyshev

/-- The normalized chart minimax lower bound has the full unrestricted polynomial class. -/
theorem chart_minimax (I : chebyshev1.SpectralInterval) (N : ℕ)
    (P : ℝ[X]) (hP : P.degree≤(N:WithBot ℕ)) (hη : P.eval I.eta=1)
    (M : ℝ) (hb : ∀ x ∈ Set.Icc (-1:ℝ) 1, |P.eval x|≤M) : I.epsilon N≤M := by
  have hM : 0≤M := (abs_nonneg (P.eval 0)).trans (hb 0 (by norm_num))
  have hMpos : 0<M := by
    by_contra hn
    have hzero : M=0 := le_antisymm (le_of_not_gt hn) hM
    let Q : ℝ[X] := C (2*I.den N)*P
    have hc : 2*I.den N≠0 := mul_ne_zero (by norm_num) (I.den_ne N)
    have hd : Q.degree≤(N:WithBot ℕ) := by simpa only [Q, degree_C_mul hc] using hP
    have hQ : ∀ x ∈ Set.Icc (-1:ℝ) 1, |Q.eval x|≤1 := by
      intro x hx
      have he : P.eval x=0 := abs_eq_zero.mp (le_antisymm (hzero ▸ hb x hx) (abs_nonneg _))
      simp [Q, he]
    have he := eval_iterate_derivative_le_of_forall_abs_le_one (k := 0)
      I.eta_gt_one.le hd hQ
    simp only [Function.iterate_zero, id_eq, Q, eval_mul, eval_C, hη, mul_one] at he
    have hd0 := I.den_pos N
    change 2*I.den N≤I.den N at he
    linarith
  let Q : ℝ[X] := C (1/M)*P
  have hd : Q.degree≤(N:WithBot ℕ) := by
    simpa only [Q, degree_C_mul (one_div_ne_zero (ne_of_gt hMpos))] using hP
  have hQ : ∀ x ∈ Set.Icc (-1:ℝ) 1, |Q.eval x|≤1 := by
    intro x hx
    simp only [Q, eval_mul, eval_C, abs_mul, abs_of_pos (one_div_pos.mpr hMpos)]
    calc
      _ ≤ (1/M)*M := mul_le_mul_of_nonneg_left (hb x hx) (one_div_pos.mpr hMpos).le
      _ = 1 := one_div_mul_cancel (ne_of_gt hMpos)
  have he := eval_iterate_derivative_le_of_forall_abs_le_one (k := 0)
    I.eta_gt_one.le hd hQ
  simp only [Function.iterate_zero, id_eq, Q, eval_mul, eval_C, hη, mul_one] at he
  change 1/M≤I.den N at he
  change 1/I.den N≤M
  apply (div_le_iff₀ (I.den_pos N)).mpr
  have hf := (div_le_iff₀ hMpos).mp he
  nlinarith

/-- The inverse chart carries the normalized interval into the physical spectrum. -/
theorem chart_mem (I : chebyshev1.SpectralInterval) {x : ℝ}
    (hx : x ∈ Set.Icc (-1:ℝ) 1) :
    (GradedFamily.chart I).eval x ∈ Set.Icc I.mu I.L := by
  simp only [GradedFamily.chart, eval_sub, eval_C, eval_mul, eval_X]
  have hd := I.delta_pos
  have he : I.delta=I.L-I.mu := rfl
  constructor <;> nlinarith [hx.1,hx.2]

/-- Full physical minimax lower bound, with no causal or sign restrictions on competitors. -/
theorem terminal_minimax_lower (I : chebyshev1.SpectralInterval) (N : ℕ)
    (p : ℝ[X]) (hp : p.degree≤(N:WithBot ℕ)) (h0 : p.eval 0=1)
    (M : ℝ) (hb : ∀ lam ∈ Set.Icc I.mu I.L, |p.eval lam|≤M) : I.epsilon N≤M := by
  apply chart_minimax I N (p.comp (GradedFamily.chart I))
  · rw [degree_comp (by rw [bezout.History.chart_degree]; norm_num),
      bezout.History.chart_degree, mul_one]
    exact hp
  · have hc := congrArg (fun p : ℝ[X] => p.eval 0) (GradedFamily.chart_comp_coordinate I)
    simp only [eval_comp, eval_sub, eval_C, eval_mul, eval_X, mul_zero, sub_zero] at hc
    simpa only [eval_comp, hc] using h0
  · intro x hx
    simpa only [eval_comp] using hb _ (chart_mem I hx)

/-- The prescribed residual attains the minimax constant uniformly and at the endpoint. -/
theorem terminal_minimax_attained (I : chebyshev1.SpectralInterval) (N : ℕ) :
    (I.residual N).degree≤(N:WithBot ℕ) ∧ (I.residual N).eval 0=1 ∧
    (∀ lam ∈ Set.Icc I.mu I.L, |(I.residual N).eval lam|≤I.epsilon N) ∧
    |(I.residual N).eval I.mu|=I.epsilon N := by
  refine ⟨GradedFamily.residual_degree_le I, GradedFamily.residual_zero I,
    fun _ hx => I.residual_abs_le N hx, ?_⟩
  rw [I.residual_eval, I.z_mu, T_eval_one, abs_of_pos (one_div_pos.mpr (I.den_pos N))]
  rfl

/-- The prescribed Chebyshev constant is an attained least uniform polynomial bound. -/
theorem terminal_minimax (I : chebyshev1.SpectralInterval) (N : ℕ) :
    IsLeast {M : ℝ | ∃ p : ℝ[X], p.degree≤(N:WithBot ℕ) ∧ p.eval 0=1 ∧
      ∀ lam ∈ Set.Icc I.mu I.L, |p.eval lam|≤M} (I.epsilon N) := by
  constructor
  · have h := terminal_minimax_attained I N
    exact ⟨I.residual N, h.1, h.2.1, h.2.2.1⟩
  · rintro M ⟨p,hp,h0,hb⟩
    exact terminal_minimax_lower I N p hp h0 M hb

end
end bezout.Properties
