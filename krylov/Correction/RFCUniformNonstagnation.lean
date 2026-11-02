import krylov.Correction.RFCUniformPrefix
import krylov.Correction.RFCUniformParameters

/-!
Article: main_krylov, thm:UCq and thm:UCg(iii).
Use: Whole spectral-class actual nonstagnating prefixes.
Source: proved genuine uniform finite-prefix induction, constructed scalar
allowances and the original real observed correction executor.
-/

namespace krylov.Correction
noncomputable section
open Matrix krylov.Methods krylov.Reference krylov.Secant krylov.Stability
open scoped InnerProductSpace Matrix.Norms.L2Operator

/-- One radius and positive constants precede every positive spectral reference, actual operator sequence and normalized nonstagnating run; every real preterminal prefix has derived domains, linear angles, quadratic projected residuals and CG step stability.
Use: Complete actual uniform ordinary-RFC reasoning without an assumed comparison trajectory.
Article: main_krylov, thm:UCq and thm:UCg(iii).
Proof: Choose the actual common numerical parameters from the proved scalar construction, apply the complete original finite-prefix induction and enlarge its monotone step coefficient to one fixed positive horizon constant.
-/
theorem gated_uniform_nonstagnating_prefix (n : ℕ) (hn : 2≤n) (κ γ : ℝ)
    (hκ : 1≤κ) (hγ : 0<γ) (hγ1 : γ<1) :
    ∃ M₀ ε₀ a C D : ℝ, 0<M₀ ∧ 0<ε₀ ∧ 0<a ∧ 0<C ∧ 0<D ∧
      ∀ (base : Matrix (Fin n) (Fin n) ℝ) (hb : base.PosDef) (μ : ℝ), 0<μ →
      (∀ i, μ≤hb.1.eigenvalues i ∧ hb.1.eigenvalues i≤μ*κ) →
      ∀ (A B : ℕ → EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
        (g : EuclideanSpace ℝ (Fin n)) (ε : ℝ), 0<ε → ε≤ε₀ →
      ‖cgCanonicalError base g 0‖≤1 → (∀ i<n, CG.gradient (cgOperator base) g i≠0) →
      M₀*ε≤‖cgCanonicalError base g (n-2)‖ →
      (∀ i<n, ‖canonicalOperator base (A i)-ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin n))‖≤ε) →
      (∀ i<n, ‖canonicalOperator base (B i)-ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin n))‖≤ε) →
      let m := gatedMethod fullMemory γ (E := EuclideanSpace ℝ (Fin n))
      let R := Matrix.toEuclideanCLM (𝕜 := ℝ) (metricRoot base)
      let J := Matrix.toEuclideanCLM (𝕜 := ℝ) (metricRoot base)⁻¹
      ∀ k≤n-1, gatedFullRunDefined γ A B g k ∧
        recordedPrefixBound (a*ε) C ε
          (primalWindow base (windowSteps (selectedWindow fullMemory (methodRun m A B g k))))
          (J (probedGradient m A B g k)) ∧
        ∀ i<k, ‖R (probedStep m A B g i)-canonicalCGStep base g i‖≤D*ε := by
  obtain ⟨K,C,L,M,δ,hK,hC,hL,hM,hδ,hgrowth,hallow,hMgrad,hMstep,hsmall⟩ :=
    rfc_uniform_prefix_parameters n κ γ hκ hγ hγ1
  let a := rfcLinearAngleConstant n K C
  let S := rfcUniformStepConstant n κ K C L
  have hK0 : 0≤K := by rw [hK]; exact mul_nonneg (by norm_num) (gatedCorrectionConstant_nonneg n γ)
  have hκ0 : 0≤κ := by linarith
  have hS : 0≤S n := rfcUniformStepConstant_nonneg n hκ0 hK0 hC.le hL n
  refine ⟨M,δ,a,C,S n+1,hM,hδ,rfcLinearAngleConstant_pos n hK0 hC.le,hC,by positivity,?_⟩
  intro base hb μ hμ hspec A B g ε hε he hinit hpre hN hA hB
  obtain ⟨hhalf,hrecord,hangle,hF,hProj⟩ := hsmall ε hε.le he
  have hpref := gated_nonstagnating_prefix base hb hn γ hγ hγ1 hμ hκ hK hC.le hL hε hhalf
    hspec hgrowth hallow hrecord hangle hF hProj hMgrad hMstep A B g hinit hpre hN hA hB
  dsimp only
  intro k hk
  refine ⟨(hpref k hk).1,(hpref k hk).2.1,?_⟩
  intro i hi
  apply ((hpref k hk).2.2 i hi).trans
  apply mul_le_mul_of_nonneg_right ?_ hε.le
  have ht := rfcUniformStepConstant_monotone n hκ0 hK0 hC.le hL (show k≤n by omega)
  change S k≤S n+1
  linarith

end
end krylov.Correction
