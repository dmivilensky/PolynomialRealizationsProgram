import krylov.Information.PlanarNormalization
import krylov.Information.PlanarReferenceLower
import krylov.Correction.ReferenceOperator

/-!
Article: main_krylov, thm:C, actual own-base normalized minimax lower scenarios.
Use: prove the sharp lower coefficient for every genuine source method on
explicit admissible full-reference scenarios, with all normalization derived.
Source: actual complete history and one-query execution, quantitative planar
radius and true own-base CG normalization with a uniform cubic loss.
-/

namespace krylov.Information
noncomputable section
open Matrix Filter Asymptotics Topology Finset krylov.Reference krylov.Secant
  krylov.LinearAlgebra krylov.Stability krylov.Correction
open scoped MatrixOrder InnerProductSpace Matrix.Norms.L2Operator
variable {n : ℕ}

/-- The genuinely returned terminal residual in the scenario's own inverse-base metric, normalized by its own last preterminal CG error.
Use: this is the actual source risk whose worst value enters the unknown-base minimax theorem.
Article: main_krylov, s4:C and thm:C, ρ_M(Ξ). -/
def Scenario.outputRatio (S : Scenario n)
    (m : krylov.Methods.ProbedMethod (EuclideanSpace ℝ (Fin n)))
    (g : EuclideanSpace ℝ (Fin n)) (N : ℕ) : ℝ :=
  ‖cgOperator (metricRoot S.base)⁻¹
    (krylov.Methods.probedGradient m S.probeOracle (S.correctionOracle N) g (N+1))‖/
      ‖cgCanonicalError S.base g N‖

/-- Genuine own-base metric and reference-error bounds control the actual original-reference output by its actual normalized source risk.
Use: transfer the real two-scenario fixed-reference lower bound to the precise normalization in the article.
Article: main_krylov, thm:C, actual source normalization comparison.
Proof: apply the true dual-metric comparison to the genuinely returned
output. Its own norm equals its actual risk times its positive true reference
normalization; bound that normalization and retain all nonnegative factors.
-/
theorem Scenario.outputRatio_reference_bound (S : Scenario n)
    (m : krylov.Methods.ProbedMethod (EuclideanSpace ℝ (Fin n)))
    (g : EuclideanSpace ℝ (Fin n)) (N : ℕ) (A : Matrix (Fin n) (Fin n) ℝ)
    (a c l : ℝ) (hc : 0≤c) (hφ : 0<‖cgCanonicalError S.base g N‖)
    (hmetric : ∀ v, ‖cgOperator (metricRoot A)⁻¹ v‖≤c*‖cgOperator (metricRoot S.base)⁻¹ v‖)
    (herror : ‖cgCanonicalError S.base g N‖≤a*l) :
    ‖cgOperator (metricRoot A)⁻¹
      (krylov.Methods.probedGradient m S.probeOracle (S.correctionOracle N) g (N+1))‖≤
        a*(c*l)*S.outputRatio m g N := by
  -- Normalize the same actual returned vector in both genuine physical metrics.
  let out := krylov.Methods.probedGradient m S.probeOracle (S.correctionOracle N) g (N+1)
  have hr : 0≤S.outputRatio m g N := div_nonneg (norm_nonneg _) hφ.le
  calc
    _ ≤ c*‖cgOperator (metricRoot S.base)⁻¹ out‖ := hmetric out
    _ = c*(S.outputRatio m g N*‖cgCanonicalError S.base g N‖) := by
      rw [Scenario.outputRatio,div_mul_cancel₀ _ hφ.ne']
    _ ≤ c*(S.outputRatio m g N*(a*l)) := mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_left herror hr) hc
    _ = _ := by ring

/-- A controlled positive normalization factor changes a quadratic lower coefficient by only the stated cubic loss.
Use: preserve the sharp source constant after the genuine own-base metric and φ comparisons.
Article: main_krylov, thm:C, uniform cubic normalization loss.
Proof: if the actual risk already exceeds K the conclusion is immediate.
Otherwise its bound by K≤s² controls the normalization-factor loss by C s³;
combine it with the proved four-cubic fixed-reference loss.
-/
theorem normalized_radius_cubic_loss {s K R D C : ℝ} (hs : 0≤s) (hK : K≤s^2)
    (hR : 0≤R) (hC : 0≤C) (hD : D≤1+C*s) (hlower : K-4*s^3≤D*R) :
    K-(4+C)*s^3≤R := by
  -- Only the below-K branch needs a quantitative normalization comparison.
  by_cases hKR : K≤R
  · exact (sub_le_self K (mul_nonneg (by positivity) (pow_nonneg hs 3))).trans hKR
  · have hRs : R≤s^2 := (le_of_not_ge hKR).trans hK
    have hprod := mul_le_mul_of_nonneg_left hRs (mul_nonneg hC hs)
    have hupper : D*R≤R+C*s^3 := by
      have h := mul_le_mul_of_nonneg_right hD hR
      nlinarith
    linarith

/-- Every original sufficiently small profile has explicit admissible full-reference signed scenarios forcing the sharp actual own-base normalized minimax lower coefficient for every source method.
Use: all constants precede every method and profile, and the risk is precisely the real source normalization on each actual scenario.
Article: main_krylov, thm:C, genuine all-profile unknown-base normalized lower bound.
Proof: choose the actual reference normalization tube once. The explicit
maximizing signed scenarios satisfy every primitive physical budget, have
full active references and force the proved fixed-reference worst output.
Both genuine own-base metric and φ bounds control that same actual output
by its actual risk. Cancel the positive reference scale and use K≤s² to
bound the full normalization loss uniformly by a cubic term.
-/
theorem admissible_planar_normalized_lower {N : ℕ}
    (A : Matrix (Fin (N+1)) (Fin (N+1)) ℝ) (hA : A.PosDef)
    (g : EuclideanSpace ℝ (Fin (N+1))) (hN : 0<N)
    (hcount : referenceAtomCount A hA g=N+1) :
    ∃ ε C : ℝ, 0<ε ∧ 0<C ∧
      ∀ (m : krylov.Methods.ProbedMethod (EuclideanSpace ℝ (Fin (N+1)))),
      krylov.Methods.CGConsistent m → krylov.Methods.OneCorrectionMethod m →
      ∀ (ω : ℕ → ℝ) (w τ r : ℝ), (∀ i∈range N, 0≤ω i) → 0≤w → 0≤τ →
      (∑ i∈range N, ω i)+w≤(1/2 : ℝ) → (∑ i∈range N, ω i)≤r → (∑ i∈range N, ω i)<ε →
      let W := ∑ i∈range N, ω i
      let a := maximizingCross W w
      let γ := maximizingComplement W w
      let S := fun σ => (planarLowerScenario (canonicalCGUnitStep A g 0) (canonicalCGUnitStep A g N)
        ω w N a γ σ).inPhysical (metricRoot A)⁻¹
      (S 1).Admissible N A r ω w τ ∧ (S (-1)).Admissible N A r ω w τ ∧
        (∃ hB : (S 1).base.PosDef, referenceAtomCount (S 1).base hB g=N+1) ∧
        (∃ hB : (S (-1)).base.PosDef, referenceAtomCount (S (-1)).base hB g=N+1) ∧
        sharpConstant W w-C*(W+w)^3≤max ((S 1).outputRatio m g N) ((S (-1)).outputRatio m g N) := by
  -- Fix the genuine normalization constants before every source method and original budget profile.
  obtain ⟨ε,L,hε,hL,hnorm⟩ := planarLowerScenario_normalization A hA g hN hcount
  refine ⟨ε,5+2*L,hε,by positivity,?_⟩
  intro m hm h1 ω w τ r hω hw hτ hs hWr hWε
  let W := ∑ i∈range N, ω i
  let a := maximizingCross W w
  let γ := maximizingComplement W w
  let S := fun σ => (planarLowerScenario (canonicalCGUnitStep A g 0) (canonicalCGUnitStep A g N)
    ω w N a γ σ).inPhysical (metricRoot A)⁻¹
  let scale := ‖cgCanonicalError A g N‖
  let D := (1+W)*(1+L*W)
  let R := max ((S 1).outputRatio m g N) ((S (-1)).outputRatio m g N)
  have hW₀ : 0≤W := sum_nonneg hω
  have hWs : W≤W+w := by linarith
  have hW₁ : W≤1 := by linarith
  have hscale : 0<scale := canonical_error_pos A hA _ (cg_nonstagnation A hA g N (by omega))
  obtain ⟨hγ,_,hcircle⟩ := maximizing_coordinates hW₀ hw
  have hcirc : a^2+γ^2=1 := by linarith
  obtain ⟨hBp,hcp,hφp,hup,hmp⟩ := hnorm ω w a γ 1 hω hw hWε hγ hcirc (by norm_num)
  obtain ⟨hBm,hcm,hφm,hum,hmm⟩ := hnorm ω w a γ (-1) hω hw hWε hγ hcirc (by norm_num)
  have hadm := admissible_planar_sharp_reference_lower A hA g hN hcount m hm h1 ω w τ r hω hw hτ hs hWr
  refine ⟨hadm.1,hadm.2.1,⟨hBp,hcp⟩,⟨hBm,hcm⟩,?_⟩
  -- Bound both genuinely returned fixed-reference norms by the actual own-base normalized risks.
  have hplus := Scenario.outputRatio_reference_bound (S 1) m g N A scale (1+W) (1+L*W)
    (by positivity) hφp hmp hup
  have hminus := Scenario.outputRatio_reference_bound (S (-1)) m g N A scale (1+W) (1+L*W)
    (by positivity) hφm hmm hum
  have hcoef : 0≤scale*D := by dsimp only [D]; positivity
  have hmax : max
      ‖cgOperator (metricRoot A)⁻¹
        (krylov.Methods.probedGradient m (S 1).probeOracle ((S 1).correctionOracle N) g (N+1))‖
      ‖cgOperator (metricRoot A)⁻¹
        (krylov.Methods.probedGradient m (S (-1)).probeOracle ((S (-1)).correctionOracle N) g (N+1))‖≤scale*D*R :=
    max_le (hplus.trans (mul_le_mul_of_nonneg_left (le_max_left _ _) hcoef))
      (hminus.trans (mul_le_mul_of_nonneg_left (le_max_right _ _) hcoef))
  have henergy : Real.sqrt (cgEnergy A g N)=scale :=
    (cgEnergy_sqrt A hA g N).trans (terminal_step_error_norm A hA g (by omega)).symm
  have href := hadm.2.2
  rw [henergy] at href
  have hlower : sharpConstant W w-4*(W+w)^3≤D*R :=
    (mul_le_mul_iff_left₀ hscale).mp (by simpa only [mul_assoc,mul_comm,mul_left_comm] using href.trans hmax)
  have hR : 0≤R := le_trans (div_nonneg (norm_nonneg _) hφp.le) (le_max_left _ _)
  have hKs : sharpConstant W w≤(W+w)^2 :=
    (sharpConstant_upper hW₀ hw).trans (by nlinarith [sq_nonneg W,sq_nonneg w])
  have hD : D≤1+(1+2*L)*(W+w) := by
    have hsq : W^2≤W := by nlinarith
    have h₁ := mul_le_mul_of_nonneg_left hsq hL.le
    have h₂ := mul_le_mul_of_nonneg_left hWs (by positivity : 0≤1+2*L)
    dsimp only [D]
    nlinarith
  have hbound := normalized_radius_cubic_loss (add_nonneg hW₀ hw) hKs hR
    (by positivity : 0≤1+2*L) hD hlower
  convert hbound using 1; ring

end
end krylov.Information
