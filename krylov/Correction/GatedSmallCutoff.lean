import krylov.Correction.GatedUniformCutoff
import krylov.Correction.GatedRestartEnergy

/-!
Article: main_krylov, thm:UCg, original-history terminal and cutoff bounds.
Use: Apply the genuine uniform two-case cycle argument to the real measured
history, actual returned gradient, true searched line and performed queries.
Source: proved actual observed-window execution and canonical dictionaries,
true full terminal model estimates and scale-uniform restart geometry.
-/

namespace krylov.Correction
noncomputable section
open Matrix krylov.Methods krylov.Reference krylov.Secant krylov.Stability
open scoped InnerProductSpace Matrix.Norms.L2Operator
variable {n : ℕ}

/-- A genuine observed prefix at its first quadratic small line has an actual metric gradient of quadratic size with a conditioning-only constant.
Use: Finish the original uniform spectral-gated RFC finite-cycle theorem.
Article: main_krylov, thm:UCg, genuine original-history cycle bounds.
Proof: The true old-angle and pair allowances derive both real Gram and projected-conjugacy margins. The original nonsingular observed solve gives the actual scale-uniform small-line gradient estimate. Insert the genuine line cutoff and already proved old projected residual, preserving the original reference metric.
-/
theorem observed_prefix_small_line_gradient_bound (base : Matrix (Fin n) (Fin n) ℝ) (hb : base.PosDef)
    (W : List (EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n)))
    (g : EuclideanSpace ℝ (Fin n))
    (A : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (N : ℕ) (hN : 1≤N) (hdim : W.length≤N) {μ κ γ a C M ε η : ℝ}
    (hμ : 0<μ) (hκ : 0≤κ) (hγ : 0≤γ) (ha : 0≤a) (hη : 0≤η) (hεη : ε≤η)
    (hspec : ∀ i, μ≤hb.1.eigenvalues i) (hnorm : ‖cgOperator base‖≤κ*μ)
    (hsolve : IsUnit (crossGram (windowImages W) (windowSteps W)).det)
    (hc : inner ℝ (windowDirection W g) (A (windowDirection W g))≠0)
    (hprefix : recordedPrefixBound a C ε (primalWindow base (windowSteps W))
      (Matrix.toEuclideanCLM (𝕜 := ℝ) (metricRoot base)⁻¹ g))
    (hy : ∀ i, ‖dualWindow base (windowImages W) i-primalWindow base (windowSteps W) i‖≤
      η*‖primalWindow base (windowSteps W) i‖)
    (hA : ‖canonicalOperator base A-ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin n))‖≤ε)
    (hangle : (N : ℝ)*a≤(1-γ)/8) (hpair : η≤a/2)
    (hsmall : ‖Matrix.toEuclideanCLM (𝕜 := ℝ) (metricRoot base)
      (lineLength g (windowDirection W g) (A (windowDirection W g)) • windowDirection W g)‖≤M*ε^2) :
    ‖Matrix.toEuclideanCLM (𝕜 := ℝ) (metricRoot base)⁻¹ g‖≤(8*κ*M+20*κ*C)*ε^2 := by
  have hmargins := uniform_restart_margins hN hdim hγ ha hη hpair hangle
  have hG := (unitGram_deviation (unitWindow (primalWindow base (windowSteps W)))
    (unitWindow_norm _ hprefix.1) ha hprefix.2.1).trans hmargins.1
  have hN' : (1 : ℝ)≤N := by exact_mod_cast hN
  have hhalf : η≤1/2 := by
    have ht := mul_le_mul_of_nonneg_right hN' ha
    nlinarith
  have hgrad := windowDirection_small_line_condition_bound base hb hμ hκ hspec hnorm W g A hsolve hG
    hη hmargins.2 hhalf hy (hA.trans hεη) hc
  exact (hgrad.trans (add_le_add
    (mul_le_mul_of_nonneg_left hsmall (by positivity : 0≤8*κ))
    (mul_le_mul_of_nonneg_left hprefix.2.2 (by positivity : 0≤20*κ)))).trans_eq (by ring)

end
end krylov.Correction
