import krylov.LinearAlgebra.SpectralEndpoints
import krylov.LinearAlgebra.SpectralUpperForm
import krylov.Convergence.ObservableFCSelfConcordant

/-!
Article: main_krylov, apG:Dunif, true spectral condition parameter.
Use: derive the observable-cycle primitive metric bounds from the actual
smallest/largest eigenvalues of Hstar, and specialize the uniform source
result to literal kappa=lambda_max/lambda_min.
Source: the attained finite spectral endpoints and the real spectral theorem;
all matrix-norm and quadratic-form bounds reuse the proved spectral API.
-/
namespace krylov.Convergence
noncomputable section
open Matrix krylov.LinearAlgebra krylov.Functions krylov.Nonlinear krylov.Reference
open scoped InnerProductSpace Matrix.Norms.L2Operator NNReal
variable {n : ℕ} [NeZero n]
set_option maxHeartbeats 800000

/-- The true nonempty positive spectrum supplies exactly the primitive
parameters m=sqrt(lambda_min), ratio=sqrt(kappa) of the source theorem. -/
theorem observable_spectral_data (base : Matrix (Fin n) (Fin n) ℝ) (hb : base.PosDef) :
    let lo:=spectralLower base hb.1
    let hi:=spectralUpper base hb.1
    let m:=Real.sqrt lo
    let ratio:=Real.sqrt (hi/lo)
    0<m ∧1≤ratio ∧
      (∀ v : EuclideanSpace ℝ (Fin n),m^2*‖v‖^2≤ inner ℝ v (cgOperator base v)) ∧
      ‖cgOperator base‖≤m^2*ratio^2 := by
  let lo:=spectralLower base hb.1
  let hi:=spectralUpper base hb.1
  have hlo : 0<lo:=spectralLower_pos base hb
  have hhi : 0<hi:=spectralUpper_pos base hb
  have horder : lo≤hi := (spectralLower_le base hb.1 0).trans (le_spectralUpper base hb.1 0)
  have hk : 1≤hi/lo := (le_div_iff₀ hlo).mpr (by simpa only [one_mul] using horder)
  have hratio : 1≤Real.sqrt (hi/lo):=Real.le_sqrt_of_sq_le (by norm_num at hk ⊢;exact hk)
  refine ⟨Real.sqrt_pos.mpr hlo,hratio,?_,?_⟩
  · intro v
    rw [Real.sq_sqrt hlo.le]
    exact spectral_lower_form base hb.1 (spectralLower_le base hb.1) v
  · rw [Real.sq_sqrt hlo.le,Real.sq_sqrt (div_nonneg hhi.le hlo.le)]
    have hn : ‖cgOperator base‖≤hi := by
      rw [cgOperator,Matrix.l2_opNorm_toEuclideanCLM]
      exact spectral_norm_le_of_eigenvalues base hb.1 hhi.le
        (fun i=>⟨(hb.eigenvalues_pos i).le,le_spectralUpper base hb.1 i⟩)
    convert hn using 1
    field_simp [hlo.ne']

/-- The complete genuine observable FC source bound with the literal
condition number of Hstar, not an externally supplied condition bound.
Both the radius and constant are fixed before the scalar objective. -/
theorem observable_fc_uniform_selfConcordant_kappa
    (base : Matrix (Fin n) (Fin n) ℝ) (hb : base.PosDef) (hn : 1≤n)
    (f : EuclideanSpace ℝ (Fin n) → ℝ) (D : StandardSelfConcordantData f Set.univ)
    (hgzero : gradient f 0=0) (hH : D.hessian 0=cgOperator base)
    (bar : ℝ) (x₀ : EuclideanSpace ℝ (Fin n))
    (hx₀ : ‖metricCoordinates base hb x₀‖≤
      observableFCRadius n (Real.sqrt (spectralUpper base hb.1/spectralLower base hb.1))) :
    ‖metricCoordinates base hb (observableRestartPoint false bar (metricCoordinates base hb)
      f (gradient f) (1/64) n x₀)‖≤
      1024*(1+Real.sqrt (spectralUpper base hb.1/spectralLower base hb.1))*(n:ℝ)*Real.sqrt n*
        ‖metricCoordinates base hb x₀‖^2 := by
  have hd:=observable_spectral_data base hb
  exact observable_fc_uniform_selfConcordant base hb hn _ _ hd.1 hd.2.1 hd.2.2.1 hd.2.2.2 f D hgzero hH bar x₀ hx₀

end
end krylov.Convergence
