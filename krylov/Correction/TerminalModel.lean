import krylov.Correction.FullReconstruction

/-!
Article: main_krylov, apD:lem-model, replacement of the actual last model.
Use: change only the last coefficient model after the genuine ordinary RFC
prefix, retaining the actual measured window and incoming gradient.
Source: the existing real coefficient solve and physical correction query;
the unchanged prefix supplies its proved analytic domains.
-/

namespace krylov.Correction
noncomputable section
open Matrix Filter Asymptotics Topology krylov.Methods krylov.Reference krylov.Stability
open scoped Matrix.Norms.L2Operator InnerProductSpace
variable {E X : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable [NormedAddCommGroup X] [NormedSpace ℝ X]

/-- Execute the last physical correction with an additive change to its actual observed model.
Use: this changes the terminal solve after the real RFC prefix, rather than assuming an output formula.
Article: main_krylov, apD:lem-model, replacement of H by H+Δ_H. -/
def modifiedTerminalGradient (A B : ℕ → E →L[ℝ] E) (g : E) (k : ℕ)
    (D : Matrix (Fin (k+1)) (Fin (k+1)) ℝ) : E :=
  let m := rfcMethod fullMemory 1 (E := E)
  let U := probedStepBasis m A B g k
  let H := pairModel U (probedImageBasis m A B g k)
  let gp := fullPostSearch 1 A B g k
  gp+B k (combine U (modelCoefficients U (H+D) gp))

/-- A model change vanishing at the reference preserves the actual terminal inverse domain locally.
Use: justify the modified solve before applying its exact residual identity.
Article: main_krylov, apD:lem-model, invertibility of H+Δ_H.
Proof: the genuine reference model is already positive; analyticity of the
actual model and the added change makes its nonzero determinant persist. -/
theorem modified_model_unit_eventually
    (A B : X → ℕ → E →L[ℝ] E) (g : X → E)
    (hA : ∀ i, AnalyticAt ℝ (fun z => A z i) 0)
    (hB : ∀ i, AnalyticAt ℝ (fun z => B z i) 0) (hg : AnalyticAt ℝ g 0)
    (Q : E →L[ℝ] E) (hA0 : A 0=(fun _ => Q)) (hB0 : B 0=(fun _ => Q))
    (hQ : Q.toLinearMap.IsSymmetric) (hpos : ∀ v : E, v≠0 → 0 < inner ℝ v (Q v))
    (k : ℕ) (hpre : ∀ i≤k, CG.gradient Q (g 0) i≠0)
    (D : X → Matrix (Fin (k+1)) (Fin (k+1)) ℝ)
    (hD : AnalyticAt ℝ D 0) (hD0 : D 0=0) :
    let m := rfcMethod fullMemory 1 (E := E)
    let H := fun z => pairModel (probedStepBasis m (A z) (B z) (g z) k)
      (probedImageBasis m (A z) (B z) (g z) k)
    ∀ᶠ z in 𝓝 (0 : X), IsUnit (H z+D z).det := by
  let H := fun z => pairModel (probedStepBasis (rfcMethod fullMemory 1) (A z) (B z) (g z) k)
    (probedImageBasis (rfcMethod fullMemory 1) (A z) (B z) (g z) k)
  have hd := (full_cycle_data_regular 1 A B g hA hB hg Q hA0 hB0 hQ hpos k hpre).2.2.2
  have hu := (full_model_unit_eventually 1 A B g hA hB hg Q hA0 hB0 hQ hpos k hpre).1
  have hu' : IsUnit (H 0+D 0).det := by simpa only [hD0,add_zero] using hu
  exact ((continuous_id.matrix_det.continuousAt.comp (hd.add hD).continuousAt).eventually_ne
    (isUnit_iff_ne_zero.mp hu')).mono fun _ hz => isUnit_iff_ne_zero.mpr hz

/-- The actual modified terminal gradient has the exact inverse-model projected residual.
Use: expose the genuine subtraction of the model change in the leading error factor.
Article: main_krylov, apD:lem-model, Uᵀg₊=−(UᵀBU−H−Δ_H)(H+Δ_H)⁻¹Uᵀg′.
Proof: apply the existing physical query identity to the actual modified model
on the inverse domain derived above, then lift its coordinates to Euclidean space. -/
theorem modifiedTerminalGradient_projected {k : ℕ}
    (A B : ℕ → E →L[ℝ] E) (g : E)
    (D : Matrix (Fin (k+1)) (Fin (k+1)) ℝ)
    (hu : IsUnit (pairModel (probedStepBasis (rfcMethod fullMemory 1) A B g k)
      (probedImageBasis (rfcMethod fullMemory 1) A B g k)+D).det) :
    let m := rfcMethod fullMemory 1 (E := E)
    let U := probedStepBasis m A B g k
    let H := pairModel U (probedImageBasis m A B g k)
    projectedResidual U (modifiedTerminalGradient A B g k D)=
      -(Matrix.toEuclideanCLM (𝕜 := ℝ) ((correctionCompression U (B k)-(H+D))*(H+D)⁻¹)
        (projectedResidual U (fullPostSearch 1 A B g k))) := by
  have he := modelCorrection_projected (probedStepBasis (rfcMethod fullMemory 1) A B g k)
    _ hu (B k) (fullPostSearch 1 A B g k)
  rw [Matrix.neg_mulVec] at he
  exact congrArg (WithLp.toLp 2) he

end
end krylov.Correction
