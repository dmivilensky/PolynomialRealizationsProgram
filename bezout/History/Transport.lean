import bezout.History.Oracle
import Mathlib.Analysis.InnerProductSpace.LinearMap
import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-!
Article: bezout, restriction of the physical channel model to its invariant subspace.
Use: actual queries, answers and outputs commute with every intertwining linear
embedding, including the isometric inclusion of the active network modes.
Proof: uniqueness of the triangular oracle recursion; isometries preserve the
literal terminal squared errors sample by sample and therefore their integrals.
-/

namespace bezout.History
noncomputable section
open scoped BigOperators
section Algebra
variable {N : ℕ} {E F : Type*} [AddCommGroup E] [Module ℝ E]
  [AddCommGroup F] [Module ℝ F]

/-- Every actual causal oracle execution respects an intertwining linear embedding. -/
theorem oracleAnswers_map (h : bezout.History N) (J : E →ₗ[ℝ] F)
    (initial : E) (oracle : Fin N → E → E) (ambient : Fin N → F → F)
    (hi : ∀ s x, ambient s (J x)=J (oracle s x)) :
    h.oracleAnswers (J initial) ambient=fun s => J (h.oracleAnswers initial oracle s) := by
  symm
  apply h.oracleAnswers_unique
  intro s
  rw [h.oracleAnswers_eq]
  have he : J initial-∑ j,h.a s j • J (h.oracleAnswers initial oracle j)=
      J (h.oracleQuery initial oracle s) := by
    simp only [oracleQuery, map_sub, map_sum, map_smul]
  rw [he, hi]

/-- Physical queries remain inside the active subspace at every actual call. -/
theorem oracleQuery_map (h : bezout.History N) (J : E →ₗ[ℝ] F)
    (initial : E) (oracle : Fin N → E → E) (ambient : Fin N → F → F)
    (hi : ∀ s x, ambient s (J x)=J (oracle s x)) (s : Fin N) :
    h.oracleQuery (J initial) ambient s=J (h.oracleQuery initial oracle s) := by
  simp only [oracleQuery, h.oracleAnswers_map J initial oracle ambient hi,
    map_sub, map_sum, map_smul]

/-- The full finite perturbed output, not only its derivative, respects active coordinates. -/
theorem oracleOutput_map (h : bezout.History N) (J : E →ₗ[ℝ] F)
    (initial : E) (oracle : Fin N → E → E) (ambient : Fin N → F → F)
    (hi : ∀ s x, ambient s (J x)=J (oracle s x)) :
    h.oracleOutput (J initial) ambient=J (h.oracleOutput initial oracle) := by
  simp only [oracleOutput, h.oracleAnswers_map J initial oracle ambient hi,
    map_sub, map_sum, map_smul]
end Algebra

/-- An isometric active-coordinate representation preserves literal terminal errors. -/
theorem oracleOutput_isometry {N : ℕ} {E F : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    (h : bezout.History N) (J : E →ₗᵢ[ℝ] F) (initial nominal : E)
    (oracle : Fin N → E → E) (ambient : Fin N → F → F)
    (hi : ∀ s x, ambient s (J x)=J (oracle s x)) :
    ‖h.oracleOutput (J initial) ambient-J nominal‖^2=
      ‖h.oracleOutput initial oracle-nominal‖^2 := by
  have he : h.oracleOutput (J initial) ambient=J (h.oracleOutput initial oracle) :=
    h.oracleOutput_map J.toLinearMap initial oracle ambient hi
  rw [he, ← map_sub, J.norm_map]

/-- Active-coordinate finite-noise predictions are the same physical ambient MSE. -/
theorem oracleOutput_mse_isometry {N : ℕ} {E F Ω : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F] [MeasurableSpace Ω]
    (μ : MeasureTheory.Measure Ω) (h : bezout.History N) (J : E →ₗᵢ[ℝ] F)
    (initial nominal : E) (oracle : Ω → Fin N → E → E) (ambient : Ω → Fin N → F → F)
    (hi : ∀ ω s x, ambient ω s (J x)=J (oracle ω s x)) :
    (∫ ω, ‖h.oracleOutput (J initial) (ambient ω)-J nominal‖^2 ∂μ)=
      ∫ ω, ‖h.oracleOutput initial (oracle ω)-nominal‖^2 ∂μ := by
  apply MeasureTheory.integral_congr_ae
  exact Filter.Eventually.of_forall (fun ω => h.oracleOutput_isometry J initial nominal
    (oracle ω) (ambient ω) (hi ω))

end
end bezout.History
