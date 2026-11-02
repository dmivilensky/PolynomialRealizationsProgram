import krylov.Correction.GatedExecution
import krylov.Methods.CanonicalWindows

/-!
Article: main_krylov, thm:UCq and thm:UCg, actual uniform gated-RFC recording.
Use: Derive genuine physical correction and secant bounds from the measured
spectral test, without any minimum individual step or reference energy.
Source: original measured RFC execution, true canonical metric covariance,
the proved observed spectral-gate conditioning and coefficient noncancellation.
-/

namespace krylov.Correction
noncomputable section
open Matrix krylov.Methods krylov.Reference krylov.Secant
open scoped InnerProductSpace Matrix.Norms.L2Operator
variable {n p : ℕ}

/-- The genuine observed pair-defect matrix is exactly invariant under the actual primal/dual metric-root coordinates.
Use: Supply the actual finite uniform spectral-gated RFC induction.
Article: main_krylov, thm:UCq and thm:UCg, genuine uniform recording.
Proof: Every original measured pairing is preserved by the proved positive-root pairing identity.
-/
theorem canonical_pairDefect (base : Matrix (Fin n) (Fin n) ℝ) (hb : base.PosDef)
    (s y : Fin p → EuclideanSpace ℝ (Fin n)) :
    pairDefect (primalWindow base s) (dualWindow base y)=pairDefect s y := by
  ext i j
  simp only [pairDefect,primalWindow,dualWindow,← canonical_search_pairing base hb]

/-- The actual gated correction movement and returned gradient have exact primal/dual canonical coordinates through both real gate decisions.
Use: Supply the actual finite uniform spectral-gated RFC induction.
Article: main_krylov, thm:UCq and thm:UCg, genuine uniform recording.
Proof: The true pair model and defect are unchanged; the actual search scalar is preserved. The genuine canonical model-correction and operator-action identities identify the accepted query and its observed gradient. Both fallback branches retain the true searched gradient.
-/
theorem gatedArrayPhase_canonical (base : Matrix (Fin n) (Fin n) ℝ) (hb : base.PosDef)
    (γ : ℝ) (S Y : Fin p → EuclideanSpace ℝ (Fin n))
    (g d z : EuclideanSpace ℝ (Fin n))
    (B : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)) :
    let R := Matrix.toEuclideanCLM (𝕜 := ℝ) (metricRoot base)
    let J := Matrix.toEuclideanCLM (𝕜 := ℝ) (metricRoot base)⁻¹
    (gatedArrayPhase γ (primalWindow base S) (dualWindow base Y) (J g) (R d) (J z)
      (canonicalOperator base B)).movement=R (gatedArrayPhase γ S Y g d z B).movement ∧
    (gatedArrayPhase γ (primalWindow base S) (dualWindow base Y) (J g) (R d) (J z)
      (canonicalOperator base B)).gradient=J (gatedArrayPhase γ S Y g d z B).gradient := by
  let R := Matrix.toEuclideanCLM (𝕜 := ℝ) (metricRoot base)
  let J := Matrix.toEuclideanCLM (𝕜 := ℝ) (metricRoot base)⁻¹
  have hU : Fin.cons (R d) (primalWindow base S)=primalWindow base (Fin.cons d S) := by
    funext j
    exact Fin.cases rfl (fun _ => rfl) j
  have hZ : Fin.cons (J z) (dualWindow base Y)=dualWindow base (Fin.cons z Y) := by
    funext j
    exact Fin.cases rfl (fun _ => rfl) j
  have hg : searchedGradient (J g) (R d) (J z)=J (searchedGradient g d z) := by
    rw [searchedGradient,canonical_lineLength base hb,searchedGradient,map_add,map_smul]
  have hcorr := canonical_modelCorrection base hb (Fin.cons d S)
    (pairModel (Fin.cons d S) (Fin.cons z Y)) (searchedGradient g d z)
  dsimp only
  unfold gatedArrayPhase
  rw [hU,hZ,canonical_pairModel base hb]
  split
  · unfold rfcArrayPhase
    rw [canonical_pairDefect base hb]
    split
    · change combine _ (modelCoefficients _ _ _) + 0=R (combine _ (modelCoefficients _ _ _) + 0) ∧
        _ + canonicalOperator base B (combine _ (modelCoefficients _ _ _))=
          J (_ + B (combine _ (modelCoefficients _ _ _)))
      rw [hU,hZ,canonical_pairModel base hb,hg,hcorr,canonical_gradient_update base hb]
      simp only [add_zero]
      exact ⟨rfl,rfl⟩
    · change 0=R 0 ∧ searchedGradient (J g) (R d) (J z)=J (searchedGradient g d z)
      exact ⟨(map_zero R).symm,hg⟩
  · change 0=R 0 ∧ searchedGradient (J g) (R d) (J z)=J (searchedGradient g d z)
    exact ⟨(map_zero R).symm,hg⟩

end
end krylov.Correction
