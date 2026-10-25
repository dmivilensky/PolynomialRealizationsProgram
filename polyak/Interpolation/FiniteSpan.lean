import polyak.Interpolation.Data
import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
Article: Appendix A, every finite wave segment has a finite-dimensional realization.
Use: reduce a finite Hilbert table to genuine Euclidean positions and gradients.
Proof: span all positions and gradients, then choose an orthonormal basis.
-/

namespace polyak.Interpolation
noncomputable section

variable {E I : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Article: finite spectral realization. Use: the span includes both data fields. -/
def dataSpan (x σ : I → E) : Submodule ℝ E :=
  Submodule.span ℝ (Set.range x ∪ Set.range σ)

/-- Article: finite spectral realization. Use: lift each actual position into the span. -/
def spanPosition (x σ : I → E) (i : I) : dataSpan x σ :=
  ⟨x i, Submodule.subset_span (Or.inl ⟨i, rfl⟩)⟩

/-- Article: finite spectral realization. Use: lift each actual gradient into the span. -/
def spanGradient (x σ : I → E) (i : I) : dataSpan x σ :=
  ⟨σ i, Submodule.subset_span (Or.inr ⟨i, rfl⟩)⟩

/-- Article: Appendix A, finite-dimensionality of every finite segment. -/
instance dataSpan_finiteDimensional [Finite I] (x σ : I → E) :
    FiniteDimensional ℝ (dataSpan x σ) :=
  FiniteDimensional.span_of_finite ℝ ((Set.finite_range x).union (Set.finite_range σ))

/-- Article: exact spectral interpolation. Use: the discrepancy is unchanged in the span. -/
theorem datumT_span (x σ : I → E) (values : I → ℝ) (i j : I) :
    datumT (spanPosition x σ) (spanGradient x σ) values i j =
      datumT x σ values i j := rfl

/-- Article: exact spectral interpolation. Use: the interpolation radius is unchanged. -/
theorem datumR_span (x σ : I → E) (i j : I) :
    datumR (spanPosition x σ) (spanGradient x σ) i j = datumR x σ i j := rfl

/-- Article: exact spectral interpolation. Use: no finite-dimensional feasibility is lost. -/
theorem tableFeasible_span_iff (x σ : I → E) (values : I → ℝ) :
    TableFeasible (spanPosition x σ) (spanGradient x σ) values ↔
      TableFeasible x σ values := Iff.rfl

/-- Article: finite Euclidean realization. Use: isometries preserve the signed discrepancy. -/
theorem datumT_isometry {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    (J : E →ₗᵢ[ℝ] F) (x σ : I → E) (values : I → ℝ) (i j : I) :
    datumT (fun k => J (x k)) (fun k => J (σ k)) values i j =
      datumT x σ values i j := by
  simp only [datumT, ← map_add J, ← map_sub J, J.inner_map_map]

/-- Article: finite Euclidean realization. Use: isometries preserve the interpolation radius. -/
theorem datumR_isometry {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    (J : E →ₗᵢ[ℝ] F) (x σ : I → E) (i j : I) :
    datumR (fun k => J (x k)) (fun k => J (σ k)) i j = datumR x σ i j := by
  simp only [datumR, ← map_sub J, J.norm_map]

/-- Article: Appendix A, finite segments. Use: a genuine Euclidean table with identical slacks.
Proof: choose an orthonormal basis of the span of the finitely many data. -/
theorem exists_euclidean_table [Finite I] (x σ : I → E) (values : I → ℝ) :
    ∃ (d : ℕ) (y τ : I → EuclideanSpace ℝ (Fin d)),
      (∀ i j, datumT y τ values i j = datumT x σ values i j) ∧
      (∀ i j, datumR y τ i j = datumR x σ i j) ∧
      (∀ i, ‖y i‖ = ‖x i‖) ∧ (∀ i, ‖τ i‖ = ‖σ i‖) := by
  let J := (stdOrthonormalBasis ℝ (dataSpan x σ)).repr.toLinearIsometry
  refine ⟨Module.finrank ℝ (dataSpan x σ),
    fun i => J (spanPosition x σ i), fun i => J (spanGradient x σ i), ?_, ?_, ?_, ?_⟩
  · intro i j
    rw [datumT_isometry]
    exact datumT_span x σ values i j
  · intro i j
    rw [datumR_isometry]
    exact datumR_span x σ i j
  · intro i
    exact J.norm_map _
  · intro i
    exact J.norm_map _

end
end polyak.Interpolation
