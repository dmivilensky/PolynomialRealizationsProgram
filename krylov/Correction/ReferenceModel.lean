import krylov.Correction.ReferenceBasis
import krylov.Correction.FullBasisAlgebra

/-!
Article: main_krylov, thm:C, canonical identification of the actual frozen model error.
Use: turn the real newest-first model coefficient into the source staircase
on genuine chronological CG flags with exactly the prescribed physical increments.
Source: existing actual CG reference columns, finite cumulative-drift
telescoping and the proved true staircase step-coordinate identity.
-/

namespace krylov.Correction
noncomputable section
open Matrix Finset krylov.Reference krylov.Variation krylov.Envelope krylov.Methods krylov.Secant
open scoped BigOperators InnerProductSpace Matrix.Norms.L2Operator
variable {n : ℕ}

/-- The actual physical correction operator with the specified canonical perturbation at a probe time.
Use: encode the original intermediate and terminal correction perturbations without shifting their budgets.
Article: main_krylov, thm:C, B_k=A_k+A¹ᐟ²F_kA¹ᐟ². -/
def canonicalCorrectionOperator (base : Matrix (Fin n) (Fin n) ℝ)
    (E : ℕ → Matrix (Fin n) (Fin n) ℝ) (F : Matrix (Fin n) (Fin n) ℝ) (k : ℕ) :
    EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n) :=
  canonicalFCPath base E 1 k+cgOperator (metricRoot base*F*metricRoot base)

/-- A true canonical correction operator differs from an earlier probe by its actual terminal perturbation and intervening increments.
Use: express each native newer-observation model entry in the original canonical budget variables.
Article: main_krylov, thm:C, B_k−A_i.
Proof: cancel the shared physical base, telescope the genuine cumulative
increments and combine their actual positive-root congruences by linearity. -/
theorem canonicalCorrectionOperator_sub_probe (base : Matrix (Fin n) (Fin n) ℝ)
    (E : ℕ → Matrix (Fin n) (Fin n) ℝ) (F : Matrix (Fin n) (Fin n) ℝ)
    {i k : ℕ} (hi : i≤k) :
    canonicalCorrectionOperator base E F k-canonicalFCPath base E 1 i=
      cgOperator (metricRoot base*(F+∑ l∈Ico i k, E l)*metricRoot base) := by
  -- Preserve the actual terminal perturbation while telescoping only the genuine probe difference.
  unfold canonicalCorrectionOperator canonicalFCPath
  simp only [one_smul]
  have he : cgOperator base+cumulativeDrift base E k+
      cgOperator (metricRoot base*F*metricRoot base)-(cgOperator base+cumulativeDrift base E i)=
      (cumulativeDrift base E k-cumulativeDrift base E i)+cgOperator (metricRoot base*F*metricRoot base) := by abel
  rw [he,cumulativeDrift_sub base E hi]
  simp only [cgOperator,← map_add,Matrix.mul_add,Matrix.add_mul]
  congr 1
  exact add_comm _ _

/-- The actual frozen model error is precisely the genuine reference compression of the source staircase.
Use: discharge the geometric leading-model-factor identity in the actual RFC second-order expansion.
Article: main_krylov, thm:C, C^(−1/2)(U₀ᵀBU₀−H)C^(−1/2)=Qᵀ𝓛Q to first order.
Proof: use the true earlier-probe difference in every actual native entry.
The actual reference column scales reduce it to two genuine chronological
CG steps; the proved staircase coordinate suffix has exactly their later
observation time, including the unscaled direction in the head column. -/
theorem reference_model_staircase (base : Matrix (Fin n) (Fin n) ℝ) (hb : base.PosDef)
    (g : EuclideanSpace ℝ (Fin n)) (k : ℕ)
    (hN : k+1≤referenceAtomCount base hb g)
    (E : ℕ → Matrix (Fin n) (Fin n) ℝ) (F : Matrix (Fin n) (Fin n) ℝ) :
    (Matrix.of fun i j : Fin (k+1) => inner ℝ (referenceModelBasis base g k i)
      ((canonicalCorrectionOperator base E F k-canonicalFCPath base E 1 (k-(min i j).val))
        (referenceModelBasis base g k j)))=
      correctionCompression (fun i => cgOperator (metricRoot base) (referenceModelBasis base g k i))
        (staircaseOperator base g E F (k+1)) := by
  -- Chronological maximum equals the newest-first minimum used by the actual observed model.
  ext i j
  have htime : max (k-i.val) (k-j.val)=k-(min i j).val := by
    rcases le_total i j with hij | hji
    · rw [min_eq_left hij,max_eq_left (by omega)]
    · rw [min_eq_right hji,max_eq_right (by omega)]
  change inner ℝ (referenceModelBasis base g k i)
    ((canonicalCorrectionOperator base E F k-canonicalFCPath base E 1 (k-(min i j).val))
      (referenceModelBasis base g k j))=inner ℝ _ (staircaseOperator _ _ _ _ _ _)
  rw [canonicalCorrectionOperator_sub_probe base E F (Nat.sub_le _ _)]
  have hp := metric_drift_pairing base (F+∑ l∈Ico (k-(min i j).val) k, E l)
    (referenceModelBasis base g k i) (referenceModelBasis base g k j)
  change inner ℝ _ (cgOperator _ _)=inner ℝ _ (cgOperator _ _) at hp
  rw [hp]
  change inner ℝ (cgOperator (metricRoot base) (referenceModelBasis base g k i))
    (cgOperator (F+∑ l∈Ico (k-(min i j).val) k, E l)
      (cgOperator (metricRoot base) (referenceModelBasis base g k j)))=
    inner ℝ (cgOperator (metricRoot base) (referenceModelBasis base g k i))
      (staircaseOperator base g E F (k+1)
        (cgOperator (metricRoot base) (referenceModelBasis base g k j)))
  rw [referenceModelBasis_canonical base hb g k hN i,
    referenceModelBasis_canonical base hb g k hN j]
  simp only [map_smul,real_inner_smul_left,real_inner_smul_right]
  rw [staircase_step_pairing base hb g hN E F (by omega) (by omega),Nat.add_sub_cancel,htime]

/-- The true static reference model is exactly the physical reference Gram form.
Use: derive the reference energy matrix used in cancellation from actual quadratic images.
Article: main_krylov, thm:C, H₀=U₀ᵀAU₀.
Proof: actual quadratic images give the genuine operator compression, and
the existing exact full-column identity gives its physical matrix congruence. -/
theorem reference_model_gram (base : Matrix (Fin n) (Fin n) ℝ) (hb : base.PosDef)
    (g : EuclideanSpace ℝ (Fin n)) (k : ℕ) :
    pairModel (referenceModelBasis base g k)
      (probedImageBasis (rfcMethod fullMemory 1) (fun _ => cgOperator base)
        (fun _ => cgOperator base) g k)=correctionCompression (referenceModelBasis base g k) (cgOperator base) := by
  rw [quadratic_imageBasis _ (cgOperator base) g k]
  exact pairModel_quadratic _ _ (cgOperator_positive base hb).1

end
end krylov.Correction
