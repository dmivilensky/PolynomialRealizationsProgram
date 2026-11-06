import chebyshev1.Realization.Basic

/-! The initial normalization required by the article's Definition 3.1.
The underlying data structure remains general for compatibility. -/
namespace chebyshev1.Realization
noncomputable section
open scoped BigOperators
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The article requires the readout of the initial memory vector to be one. -/
def Normalized (R : chebyshev1.Realization ι) : Prop :=
  ∑ i, R.readout i * R.b i = 1

theorem normalized_iff_scalarTransfer_zero (R : chebyshev1.Realization ι) (lam : ℝ) :
    R.Normalized ↔ R.scalarTransfer 0 lam = 1 := by
  simp [Normalized, scalarTransfer, orderedProduct, scalarContract, Matrix.one_apply]

end
end chebyshev1.Realization
