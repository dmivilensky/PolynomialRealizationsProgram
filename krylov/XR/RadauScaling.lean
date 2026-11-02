import krylov.XR.RadauSource

/-!
Article: main_krylov, apG:radau-adequate, genuine raw-direction convention.
Use: remove the harmless unit-direction convention from the primitive
adequacy argument without changing either actual observed Schur coefficient.
Source: exact homogeneity of the literal ordinary-inverse formulas.
-/
namespace krylov.XR
noncomputable section
open Matrix krylov.Methods krylov.Reference krylov.Convergence krylov.Secant
open scoped InnerProductSpace Matrix.Norms.L2Operator
variable {n p : ℕ}

/-- Both actual observed consistency coefficients are invariant under
every nonzero real rescaling of the raw new direction.
Article: main_krylov, apG:radau-adequate. -/
theorem radau_coefficients_smul (s : Fin p → EuclideanSpace ℝ (Fin n))
    (T : Matrix (Fin p) (Fin p) ℝ) (d : EuclideanSpace ℝ (Fin n))
    (hd : d≠0) (c mu upper : ℝ) (hc : c≠0) :
    lowerConsistencyCoefficient s T (c • d) mu=lowerConsistencyCoefficient s T d mu ∧
      upperConsistencyCoefficient s T (c • d) upper=upperConsistencyCoefficient s T d upper := by
  have hco : coordinates s (c • d)=c • coordinates s d := by
    ext i
    simp only [coordinates,real_inner_smul_right,Pi.smul_apply,smul_eq_mul]
  have hn := norm_ne_zero_iff.mpr hd
  constructor <;>
    simp only [lowerConsistencyCoefficient,upperConsistencyCoefficient,hco,mulVec_smul,
      smul_dotProduct,dotProduct_smul,smul_eq_mul,norm_smul,Real.norm_eq_abs,mul_pow,sq_abs] <;>
    field_simp

/-- The true directional Rayleigh quotient is exactly the energy of
the genuinely normalized physical direction.
Article: main_krylov, apG:radau-adequate. -/
theorem radau_normalized_energy (H : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (d : EuclideanSpace ℝ (Fin n)) :
    inner ℝ ((‖d‖⁻¹ : ℝ) • d) (H ((‖d‖⁻¹ : ℝ) • d))=inner ℝ d (H d)/‖d‖^2 := by
  rw [map_smul,real_inner_smul_left,real_inner_smul_right]
  ring

end
end krylov.XR
