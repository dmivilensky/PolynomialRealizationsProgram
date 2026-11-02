import krylov.Correction.RFCUniformPrefix
import krylov.Correction.RFCUniformParameters
import krylov.Correction.RFCContamination

/-!
Article: main_krylov, thm:UCq, original uniform observed RFC bounds.
Use: Expose actual normalized observed models and true quantitative prefix
consequences in a compact reusable form for the final uniform response.
Source: proved genuine nonstagnating finite-history induction, actual measured
model identities and real correction-contamination estimates.
-/

namespace krylov.Correction
noncomputable section
open Matrix krylov.Methods krylov.Reference krylov.Secant krylov.Stability
open scoped InnerProductSpace Matrix.Norms.L2Operator

/-- The actual whole nonstagnating RFC prefix has uniform second-order relative contamination in every true measured secant.
Use: Apply the original quantitative uniform RFC results to the same actual executor.
Article: main_krylov, thm:UCq.
Proof: Choose all constants before the genuine reference and run. Strengthen the common radius so the actual relative correction-to-line ratio is at most one half. The real finite-prefix theorem supplies that ratio at every original iteration; the true line-plus-correction identity turns it into a recorded-step ratio. Exact canonical oracle balance then gives the genuine quadratic contamination bound.
-/
theorem gated_uniform_nonstagnating_contamination (n : ℕ) (hn : 2≤n) (κ γ : ℝ)
    (hκ : 1≤κ) (hγ : 0<γ) (hγ1 : γ<1) :
    ∃ M₀ ε₀ Cξ : ℝ, 0<M₀ ∧ 0<ε₀ ∧ 0<Cξ ∧
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
      ∀ i<n-1, ‖J (probedSecant m A B g i)-canonicalOperator base (A i) (R (probedStep m A B g i))‖≤
        Cξ*ε^2*‖R (probedStep m A B g i)‖ := by
  obtain ⟨K,C,L,M,δ,hK,hC,hL,hM,hδ,hgrowth,hallow,hMgrad,hMstep,hsmall⟩ :=
    rfc_uniform_prefix_parameters n κ γ hκ hγ hγ1
  have hK0 : 0≤K := by rw [hK]; exact mul_nonneg (by norm_num) (gatedCorrectionConstant_nonneg n γ)
  let Q := rfcRelativeCorrectionConstant n K C
  have hQ : 0≤Q := rfcRelativeCorrectionConstant_nonneg n hK0 hC.le
  let δ' := min δ (1/(2*(Q+1)))
  have hδ' : 0<δ' := lt_min hδ (by positivity)
  refine ⟨M,δ',4*Q+1,hM,hδ',by positivity,?_⟩
  intro base hb μ hμ hspec A B g ε hε he hinit hpre hN hA hB
  have heδ := he.trans (min_le_left _ _)
  have heQ : ε*(2*(Q+1))≤1 := (le_div_iff₀ (by positivity : 0<2*(Q+1))).mp (he.trans (min_le_right _ _))
  have hqhalf : Q*ε≤1/2 := by nlinarith only [heQ,hε.le]
  obtain ⟨hhalf,hrecord,hangle,hF,hProj⟩ := hsmall ε hε.le heδ
  have hpref := gated_nonstagnating_prefix_with_corrections base hb hn γ hγ hγ1 hμ hκ hK hC.le hL hε hhalf
    hspec hgrowth hallow hrecord hangle hF hProj hMgrad hMstep A B g hinit hpre hN hA hB
  let m := gatedMethod fullMemory γ (E := EuclideanSpace ℝ (Fin n))
  let R := Matrix.toEuclideanCLM (𝕜 := ℝ) (metricRoot base)
  dsimp only
  intro i hi
  have hline := ((hpref (n-1) le_rfl).2.2 i hi).2
  have hrec := correction_line_to_recorded_bound (R (gatedObservedLineStep γ A B g i))
    (R (probedPhase m A B g i).movement) (mul_nonneg hQ hε.le) hqhalf hline
  have hbalance : R (gatedObservedLineStep γ A B g i)+R (probedPhase m A B g i).movement=R (probedStep m A B g i) := by
    change R (gatedObservedLineStep γ A B g i)+R (probedPhase m A B g i).movement=
      R (gatedObservedLineStep γ A B g i+(probedPhase m A B g i).movement)
    rw [map_add]
  rw [hbalance] at hrec
  have hχ : ‖R (probedPhase m A B g i).movement‖≤(2*Q)*ε*‖R (probedStep m A B g i)‖ := hrec.trans_eq (by ring)
  have hξ := probed_canonical_contamination_bound base hb m A B g i hε.le (hA i (by omega)) (hB i (by omega)) hχ
  apply hξ.trans
  have hcoef : 2*(2*Q)≤4*Q+1 := by linarith
  exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hcoef (sq_nonneg ε)) (norm_nonneg _)

end
end krylov.Correction
