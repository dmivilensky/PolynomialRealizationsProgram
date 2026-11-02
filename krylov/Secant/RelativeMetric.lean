import krylov.Secant.Metric
import krylov.LinearAlgebra.NormOrder

/-!
Article: main_krylov, def:model, congruence invariance of the relative spectral norm.
Use: budgets describe the same physical uncertainty after any invertible change
of variables, independently of the positive square roots used to express them.
Source: Loewner congruence and the proved symmetric spectral norm characterization.
-/

namespace krylov.Secant
noncomputable section
open Matrix
open scoped Matrix MatrixOrder
variable {n : ℕ}

/-- The genuine canonical change is an order equivalence for physical symmetric forms.
Use: both signs of a physical relative budget survive normalization with no loss.
Article: main_krylov, def:model(c), relative spectral budgets.
Proof: the forward implication compresses by the actual metric root and reconstructs;
the reverse implication is the already proved monotonicity of inverse-root congruence. -/
theorem relativeOperator_le_iff (base : Matrix (Fin n) (Fin n) ℝ) (hbase : base.PosDef)
    (E F : Matrix (Fin n) (Fin n) ℝ) :
    relativeOperator base E ≤ relativeOperator base F ↔ E ≤ F := by
  constructor
  · intro h
    have hc := congruence_mono h (metricRoot base)
    simpa only [(metricRoot_isSymm base).eq, relativeOperator_reconstruct base _ hbase] using hc
  · exact relativeOperator_mono base

/-- A canonical spectral budget is exactly the pair of signed physical Loewner bounds.
Use: translates actual norm constraints into admissibility and back, including zero budgets.
Article: main_krylov, def:model(c) and thm:window.
Proof: the symmetric normalized form lies in [−ωI,ωI] exactly when the physical
form lies in [−ωA,ωA], by the genuine metric order equivalence. -/
theorem relative_norm_le_iff (base E : Matrix (Fin n) (Fin n) ℝ) (hbase : base.PosDef)
    (hE : E.IsSymm) {ω : ℝ} (hω : 0 ≤ ω) :
    relativeBudget base E ≤ ω ↔ -(ω • base) ≤ E ∧ E ≤ ω • base := by
  -- Match the two canonical shifted positivity tests with their physical endpoints.
  have hs := Matrix.isHermitian_iff_isSymm.mpr (relativeOperator_isSymm base E hE)
  rw [relativeBudget, krylov.LinearAlgebra.spectral_norm_iff_shifted_posSemidef _ hs hω]
  have hu : (ω • 1 - relativeOperator base E).PosSemidef ↔ E ≤ ω • base := by
    rw [← relativeOperator_le_iff base hbase E (ω • base), relativeOperator_smul,
      relativeOperator_base base hbase, Matrix.le_iff]
  have hl : (ω • 1 + relativeOperator base E).PosSemidef ↔ -(ω • base) ≤ E := by
    rw [← relativeOperator_le_iff base hbase (-(ω • base)) E, relativeOperator_neg,
      relativeOperator_smul, relativeOperator_base base hbase, Matrix.le_iff]
    simp only [sub_neg_eq_add, add_comm]
  rw [hu, hl, and_comm]

/-- Invertible physical congruence preserves the actual relative spectral norm exactly.
Use: establishes the coordinate-invariance statement following def:model.
Article: main_krylov, Section 2, relative spectral norm invariant under congruence.
Proof: transfer both signed physical budget inequalities through the congruence;
use its inverse for the reverse norm inequality. -/
theorem relativeBudget_congruence (base E C : Matrix (Fin n) (Fin n) ℝ)
    (hbase : base.PosDef) (hE : E.IsSymm) (hC : IsUnit C.det) :
    relativeBudget (Cᵀ * base * C) (Cᵀ * E * C) = relativeBudget base E := by
  have hi : Function.Injective C.mulVec := by
    intro v w he
    have hh := congrArg (fun z => C⁻¹ *ᵥ z) he
    simpa only [mulVec_mulVec, nonsing_inv_mul C hC, one_mulVec] using hh
  have hbase' : (Cᵀ * base * C).PosDef := by
    simpa only [conjTranspose_eq_transpose_of_trivial] using
      hbase.conjTranspose_mul_mul_same (B := C) hi
  have hE' : (Cᵀ * E * C).IsSymm := by
    simp only [Matrix.IsSymm, transpose_mul, transpose_transpose, hE.eq, Matrix.mul_assoc]
  have hb := (relative_norm_le_iff base E hbase hE (by apply chebyshev1.opNorm_nonneg)).mp le_rfl
  have hb' := (relative_norm_le_iff _ _ hbase' hE'
    (by apply chebyshev1.opNorm_nonneg)).mp le_rfl
  apply le_antisymm
  · apply (relative_norm_le_iff _ _ hbase' hE'
      (by apply chebyshev1.opNorm_nonneg)).mpr
    simpa only [Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_neg, Matrix.neg_mul] using
      And.intro (congruence_mono hb.1 C) (congruence_mono hb.2 C)
  · apply (relative_norm_le_iff base E hbase hE
      (by apply chebyshev1.opNorm_nonneg)).mpr
    -- Reverse the physical congruence using the same actual nonsingular inverse.
    have ht : IsUnit Cᵀ.det := by simpa only [det_transpose] using hC
    have he : ∀ X : Matrix (Fin n) (Fin n) ℝ, C⁻¹ᵀ * (Cᵀ * X * C) * C⁻¹ = X := by
      intro X
      rw [transpose_nonsing_inv, ← Matrix.mul_assoc, ← Matrix.mul_assoc,
        nonsing_inv_mul _ ht, Matrix.one_mul, Matrix.mul_assoc, mul_nonsing_inv _ hC, Matrix.mul_one]
    have hh := And.intro (congruence_mono hb'.1 C⁻¹) (congruence_mono hb'.2 C⁻¹)
    simpa only [Matrix.mul_neg, Matrix.neg_mul, Matrix.mul_smul, Matrix.smul_mul, he] using hh

end
end krylov.Secant
