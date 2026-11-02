import krylov.Information.PlanarRadius
import krylov.Stability.UniformGram

/-!
Article: main_krylov, thm:H, the small-source two-scenario information radius.
Use: turn the actual finite mean and hidden matrices into a uniform
second-order lower bound for every common correction. Source: the proved
Neumann inverse bound and the genuine Hilbert two-scenario inequality.
-/

namespace krylov.Information
noncomputable section
open Real Matrix krylov.Reference krylov.Stability krylov.Secant
open scoped InnerProductSpace Matrix.Norms.L2Operator
variable {n : ℕ}

/-- Two actual small matrix completions force the source's full quadratic information radius, with an explicit uniform cubic loss.
Article: main_krylov, thm:H, the factor 1-O(e_c).
The real mean inverse and the actual operator norm estimates are derived;
no residual expansion or information-radius conclusion is assumed. -/
theorem small_two_scenario_radius (A D : Matrix (Fin n) (Fin n) ℝ)
    (e : EuclideanSpace ℝ (Fin n)) (he : ‖e‖ = 1)
    (hDe : 1 ≤ ‖cgOperator D e‖) (ψ a : ℝ) (hψ : 0 ≤ ψ) (ha : 0 ≤ a)
    (hsmall : ψ * ‖A‖ ≤ 1 / 2) (u : EuclideanSpace ℝ (Fin n)) :
    let C := 2 * ‖D‖ * (‖A‖ + 1)
    let M := 1 + ψ • A
    let Δ := ψ • D
    ψ ^ 2 * a * (1-C*ψ) ≤
      max ‖(ψ*a) • e + cgOperator (M+Δ) u‖ ‖(ψ*a) • e + cgOperator (M-Δ) u‖ := by
  let C := 2 * ‖D‖ * (‖A‖ + 1)
  let M := 1 + ψ • A
  let Δ := ψ • D
  let J := cgOperator M⁻¹
  let K := cgOperator (Δ * M⁻¹)
  have hMdiff : ‖M-1‖ = ψ * ‖A‖ := by
    rw [show M-1=ψ • A by dsimp only [M]; abel, norm_smul, Real.norm_of_nonneg hψ]
  obtain ⟨hu, hJnorm, hJerror⟩ := near_identity_inverse M (hMdiff ▸ hsmall)
  have hJ : ‖J‖ ≤ 2 := by simpa only [J, cgOperator, Matrix.l2_opNorm_toEuclideanCLM] using hJnorm
  have hJerr : ‖J-ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin n))‖ ≤ 2*ψ*‖A‖ := by
    have heq : J-ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin n)) = cgOperator (M⁻¹-1) := by
      simp only [J, cgOperator, map_sub, map_one]
      rfl
    rw [heq, cgOperator, Matrix.l2_opNorm_toEuclideanCLM]
    exact (hJerror.trans_eq (by rw [hMdiff]; ring))
  have hDnorm : ‖cgOperator D‖ = ‖D‖ := Matrix.l2_opNorm_toEuclideanCLM D
  have hJe : ‖J e - e‖ ≤ 2*ψ*‖A‖ := by
    have hh := ((J-ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin n))).le_opNorm e).trans
      (mul_le_mul_of_nonneg_right hJerr (norm_nonneg e))
    simpa only [_root_.sub_apply, ContinuousLinearMap.id_apply, he, mul_one] using hh
  have hDJ : 1 - 2*ψ*‖D‖*‖A‖ ≤ ‖cgOperator D (J e)‖ := by
    have ht := norm_sub_le (cgOperator D (J e)) (cgOperator D (J e)-cgOperator D e)
    rw [sub_sub_cancel] at ht
    have hh : ‖cgOperator D (J e)-cgOperator D e‖ ≤ 2*ψ*‖D‖*‖A‖ := by
      rw [← map_sub]
      exact ((cgOperator D).le_opNorm _).trans
        ((mul_le_mul_of_nonneg_left hJe (norm_nonneg _)).trans_eq (by rw [hDnorm]; ring))
    linarith only [ht, hh, hDe]
  have hK : ‖K‖ ≤ 2*ψ*‖D‖ := by
    have heq : K = (ψ • cgOperator D) * J := by simp only [K, Δ, J, cgOperator, map_mul, map_smul]
    rw [heq]
    have hsc : ‖ψ • cgOperator D‖ = ψ*‖D‖ := by rw [norm_smul, Real.norm_of_nonneg hψ, hDnorm]
    exact (norm_mul_le _ _).trans ((mul_le_mul hsc.le hJ (norm_nonneg _) (by positivity)).trans_eq (by ring))
  have hnum : ψ^2*a*(1-2*ψ*‖D‖*‖A‖) ≤ ‖K ((ψ*a) • e)‖ := by
    have heq : K ((ψ*a) • e) = (ψ^2*a) • cgOperator D (J e) := by
      simp only [K, Δ, J, cgOperator, map_mul, map_smul, _root_.smul_apply,
        mul_apply_eq_comp, smul_smul]
      congr 1
      ring
    rw [heq, norm_smul, Real.norm_of_nonneg (by positivity : 0 ≤ ψ^2*a)]
    exact mul_le_mul_of_nonneg_left hDJ (by positivity)
  have hroot : 0 < sqrt (1+‖K‖^2) := sqrt_pos.mpr (by positivity)
  have hden : sqrt (1+‖K‖^2) ≤ 1+2*ψ*‖D‖ := by
    have hh : sqrt (1+‖K‖^2) ≤ 1+‖K‖ := by
      apply (sq_le_sq₀ (sqrt_nonneg _) (by positivity)).mp
      rw [sq_sqrt (by positivity)]
      nlinarith [norm_nonneg K]
    exact hh.trans (add_le_add le_rfl hK)
  have hrad : ψ^2*a*(1-C*ψ) ≤ ‖K ((ψ*a) • e)‖ / sqrt (1+‖K‖^2) := by
    by_cases hb : ψ^2*a*(1-C*ψ) ≤ 0
    · exact hb.trans (div_nonneg (norm_nonneg _) hroot.le)
    · have hb' : 0 ≤ ψ^2*a*(1-C*ψ) := (lt_of_not_ge hb).le
      apply (le_div_iff₀ hroot).mpr
      calc
        _ ≤ ψ^2*a*(1-C*ψ)*(1+2*ψ*‖D‖) := mul_le_mul_of_nonneg_left hden hb'
        _ ≤ ψ^2*a*(1-2*ψ*‖D‖*‖A‖) := by
          have hn : 0 ≤ 4*ψ^4*a*‖D‖^2*(‖A‖+1) := by positivity
          dsimp only [C]
          nlinarith only [hn]
        _ ≤ _ := hnum
  exact hrad.trans (terminal_two_scenario_lower M Δ hu ((ψ*a) • e) u)

end
end krylov.Information
