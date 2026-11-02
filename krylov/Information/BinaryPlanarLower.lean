import krylov.Information.BinaryPlanarFibre
import krylov.Information.SmallTwoScenarioRadius

/-!
Article: main_krylov, thm:H, the original gradient-only compatible planar lower bound.
Use: combine true binary-ball witnesses, complete actual policy replay and
the actual small two-scenario radius. The common remainder constant is
chosen before the method, the tensor sign and the source scale.
Source: the source's two harmonic perturbations and the proved information
radius, in the genuine physical reference metric.
-/

namespace krylov.Information
noncomputable section
open Real Matrix Finset krylov.Tensor krylov.Tensor.BinaryCubic krylov.Secant
  krylov.Reference krylov.LinearAlgebra krylov.Correction krylov.Methods
open scoped BigOperators InnerProductSpace Matrix.Norms.L2Operator
variable {N : ℕ}

/-- The complete executed compatible-binary gradient-only lower bound has the printed one-half coefficient and a uniform explicit small-scale loss.
Article: main_krylov, thm:H, the planar information lower bound.
Both witness tensors belong to the original unit ball and their genuine
unknown base coefficients obey the original budget. The outputs are actual
globally CG-consistent at-most-one-correction executions. -/
theorem binaryPlanar_gradient_lower
    (A : Matrix (Fin (N+1)) (Fin (N+1)) ℝ) (hA : A.PosDef)
    (g : EuclideanSpace ℝ (Fin (N+1))) (hN : 0 < N)
    (hcount : referenceAtomCount A hA g = N+1) (r : ℝ) (hr : 0 ≤ r) :
    ∃ ε₀ C : ℝ, 0 < ε₀ ∧ 0 < C ∧
      ∀ κ e_c : ℝ, 0 ≤ κ → κ ≤ e_c → e_c < ε₀ →
      ∀ m : ProbedMethod (EuclideanSpace ℝ (Fin (N+1))), CGConsistent m → OneCorrectionMethod m →
      let e := canonicalCGUnitStep A g 0
      let h := canonicalCGUnitStep A g N
      let probes := fun σ => binaryPlanarProbe A e h κ r N (gradientWitness r σ)
      let corrections := fun σ (_ : ℕ) => cgOperator
        (metricRoot A * binaryPlanarOutput e h κ r N (gradientWitness r σ) * metricRoot A)
      let out := fun σ => cgOperator (metricRoot A)⁻¹
        (probedGradient m (probes σ) (corrections σ) g (N+1))
      (gradientWitness r 1).InBall ∧ (gradientWitness r (-1)).InBall ∧
      (∀ σ : ℝ, σ^2=1 → |κ/(sqrt 2*(1+r))*(σ+r)| ≤ e_c) ∧
      (κ^2/(2*(1+r)^2))*sqrt (cgEnergy A g N)*(1-C*e_c) ≤ max ‖out 1‖ ‖out (-1)‖ := by
  let e := canonicalCGUnitStep A g 0
  let h := canonicalCGUnitStep A g N
  let M₀ := planarMatrix e h (2*r) 1 (-r)
  let Δ₀ := planarMatrix e h (1+2*r^2) (-r) 0
  let C₀ := 2 * ‖Δ₀‖ * (‖M₀‖ + 1)
  let C := C₀ + 1
  have hC₀ : 0 ≤ C₀ := by dsimp only [C₀]; positivity
  let ε₀ := 1 / (2*(‖M₀‖+1))
  have hε₀ : 0 < ε₀ := by dsimp only [ε₀]; positivity
  refine ⟨ε₀, C, hε₀, by dsimp only [C]; positivity, ?_⟩
  intro κ e_c hκ hκe hec m hm h1
  dsimp only
  refine ⟨gradientWitness_inBall hr (by norm_num), gradientWitness_inBall hr (by norm_num),
    fun σ hσ => gradientWitness_base_bound hr hσ hκ hκe, ?_⟩
  let ψ := κ / (sqrt 2*(1+r))
  let a := sqrt (cgEnergy A g N)
  have hψ : 0 ≤ ψ := by dsimp only [ψ]; positivity
  have hψκ : ψ ≤ κ := by
    have hs : 1 ≤ sqrt (2 : ℝ) := by nlinarith [sq_sqrt (by norm_num : (0 : ℝ) ≤ 2), sqrt_nonneg (2 : ℝ)]
    have hd : 1 ≤ sqrt 2*(1+r) := by nlinarith only [hs, hr]
    exact div_le_self hκ hd
  have hsmall : ψ*‖M₀‖ ≤ 1/2 := by
    have hh := (lt_div_iff₀ (by positivity : 0 < 2*(‖M₀‖+1))).mp hec
    have hec₀ : 0 ≤ e_c := hκ.trans hκe
    have hψe := hψκ.trans hκe
    nlinarith [mul_le_mul_of_nonneg_right hψe (norm_nonneg M₀)]
  have ho := canonicalCG_frame_of_full_atoms A hA g hcount
  have he : ‖e‖=1 := ho.norm_eq_one (0 : Fin (N+1))
  have hh : ‖h‖=1 := ho.norm_eq_one (Fin.last N)
  have heh : inner ℝ e h=0 := ho.inner_eq_zero (i := 0) (j := Fin.last N)
    (by intro hz; have hv := congrArg Fin.val hz; simp only [Fin.val_zero, Fin.val_last] at hv; omega)
  have hΔ : 1 ≤ ‖cgOperator Δ₀ e‖ := by
    have hee : inner ℝ e e=1 := by rw [real_inner_self_eq_norm_sq, he, one_pow]
    have hhe : inner ℝ h e=0 := (real_inner_comm _ _).trans heh
    have hact : cgOperator Δ₀ e = (1+2*r^2) • e + (-r) • h := by
      simp only [Δ₀, cgOperator, planarMatrix_action, hee, hhe, mul_one, mul_zero, add_zero]
    have hsq := planar_coordinates_norm_sq e h he hh heh (1+2*r^2) (-r)
    rw [← hact] at hsq
    nlinarith [norm_nonneg (cgOperator Δ₀ e), sq_nonneg r, sq_nonneg (r^2)]
  obtain ⟨u, hu⟩ := binaryPlanarWitness_terminal_form A hA g hN hcount m hm h1 κ r
  have hb := small_two_scenario_radius M₀ Δ₀ e he hΔ ψ a hψ (sqrt_nonneg _) hsmall u
  have hM : 1+ψ • M₀ = 1+planarMatrix e h (2*r*ψ) ψ (-r*ψ) := by
    dsimp only [M₀]
    rw [← planarMatrix_scale]
    congr 2 <;> ring
  have hD : ψ • Δ₀ = planarMatrix e h ((1+2*r^2)*ψ) (-r*ψ) 0 := by
    dsimp only [Δ₀]
    rw [← planarMatrix_scale]
    congr 1 <;> ring
  dsimp only at hb
  rw [hM, hD] at hb
  have hψsq : ψ^2 = κ^2/(2*(1+r)^2) := by
    dsimp only [ψ]
    rw [div_pow, mul_pow, sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
  have hscale : ψ^2*a*(1-C*e_c) ≤ ψ^2*a*(1-C₀*ψ) := by
    have hh := mul_le_mul_of_nonneg_left (hψκ.trans hκe) hC₀
    have hec₀ := hκ.trans hκe
    apply mul_le_mul_of_nonneg_left _ (by positivity : 0 ≤ ψ^2*a)
    dsimp only [C]
    linarith only [hh, hec₀]
  have hfull := hscale.trans hb
  rw [hψsq] at hfull
  rw [hu 1, hu (-1)]
  simpa only [C₀, M₀, Δ₀, e, h, ψ, a, one_smul, neg_one_smul, sub_eq_add_neg] using hfull

end
end krylov.Information
