import nesterov.Rates.Envelope
import nesterov.Stationary.Execution
import polyak.Functions.Embedding
import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
Article: Remark uniform rates and smooth subclasses, Appendix A.
Use: every finite prefix in an arbitrary Hilbert space is reproduced exactly
by a genuine full execution on a Euclidean space with the same μ and L.
-/

noncomputable section
namespace nesterov
open scoped BigOperators InnerProductSpace

namespace Functions

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]

/-- Restriction to an isometric subspace uses the actual adjoint gradient. -/
theorem hasGradientAt_restrict (J : F →ₗᵢ[ℝ] E) {f : E → ℝ}
    (hf : Differentiable ℝ f) (x : F) :
    HasGradientAt (fun y => f (J y))
      (polyak.embeddingProjection J (gradient f (J x))) x := by
  rw [hasGradientAt_iff_hasFDerivAt]
  convert ((hf (J x)).hasGradientAt.hasFDerivAt.comp x J.toContinuousLinearMap.hasFDerivAt) using 1
  · rfl
  · ext y
    simp only [InnerProductSpace.toDual_apply_apply, ContinuousLinearMap.comp_apply]
    exact ContinuousLinearMap.adjoint_inner_left J.toContinuousLinearMap y (gradient f (J x))

/-- Orthogonal restriction preserves both curvature constants exactly. -/
theorem centered_restrict {μ L : ℝ} {f : E → ℝ}
    (hf : polyak.CenteredSmoothStronglyConvex μ L f) (J : F →ₗᵢ[ℝ] E) :
    polyak.CenteredSmoothStronglyConvex μ L (fun x => f (J x)) := by
  have hg := hasGradientAt_restrict J hf.differentiable
  refine ⟨⟨hf.mu_pos, hf.mu_lt_L, fun x => (hg x).differentiableAt, ?_, ?_⟩, ?_, ?_⟩
  · intro x y
    rw [(hg x).gradient]
    have h := hf.tangent_lower (J x) (J y)
    have he : inner ℝ (polyak.embeddingProjection J (gradient f (J x))) (y - x) =
        inner ℝ (gradient f (J x)) (J y - J x) := by
      rw [← map_sub]
      exact ContinuousLinearMap.adjoint_inner_left J.toContinuousLinearMap _ _
    rw [he]
    simpa only [← map_sub, J.norm_map] using h
  · intro x y
    rw [(hg x).gradient, (hg y).gradient, ← map_sub]
    exact (polyak.norm_embeddingProjection_le J _).trans
      (by simpa only [← map_sub, J.norm_map] using hf.grad_lipschitz (J x) (J y))
  · simpa only [map_zero] using hf.value_zero
  · rw [(hg 0).gradient]
    simp only [map_zero, hf.gradient_zero]

end Functions

namespace StationaryMethod

variable (M : StationaryMethod)
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- A finite table satisfying the actual recursion agrees with the full causal
executor throughout the prefix determined by that table. -/
theorem run_eq_of_prefix {g : E → E} {w : ℕ → E} (n : ℕ)
    (hw : ∀ k < n, ∑ j : Fin (M.memory + 1), M.recurrenceCoeff j • w (k + j) =
      g (M.query w k)) :
    ∀ i < n + M.memory, M.run g (fun j => w j) i = w i := by
  intro i
  induction i using Nat.strong_induction_on with
  | h i ih =>
    intro hi
    by_cases himem : i < M.memory
    · exact M.run_initial g (fun j => w j) ⟨i, himem⟩
    · let k := i - M.memory
      have hk : k < n := by dsimp [k]; omega
      have he : i = k + M.memory := by dsimp [k]; omega
      have hstep : w (k + M.memory) =
          (M.recurrenceCoeff (Fin.last M.memory))⁻¹ •
            (g (M.query w k) - ∑ j : Fin M.memory,
              M.recurrenceCoeff j.castSucc • w (k + j)) := by
        have hh := hw k hk
        rw [Fin.sum_univ_castSucc] at hh
        simp only [Fin.val_castSucc, Fin.val_last] at hh
        rw [← hh]
        simp only [add_sub_cancel_left, smul_smul, inv_mul_cancel₀ M.leading_ne, one_smul]
      rw [he, M.run_step, hstep]
      congr 2
      · congr 1
        apply Finset.sum_congr rfl
        intro j _
        rw [ih (k + j) (by dsimp [k]; omega) (by dsimp [k]; omega)]
      · apply Finset.sum_congr rfl
        intro j _
        rw [ih (k + j) (by dsimp [k]; omega) (by dsimp [k]; omega)]

end StationaryMethod

namespace Rates.HilbertRun

variable {M : StationaryMethod} {μ L : ℝ}

/-- Exact finite-dimensional compression preserves every state norm up to the
chosen horizon, while retaining a full actual trajectory and the original class. -/
theorem exists_finiteDimensional_prefix_isometry (r : Rates.HilbertRun M μ L) (n : ℕ) :
    ∃ s : Rates.HilbertRun M μ L, FiniteDimensional ℝ s.Carrier ∧
      ∃ J : s.Carrier →ₗᵢ[ℝ] r.Carrier,
        (∀ i < n + M.memory, J (s.w i) = r.w i) ∧
        ∀ k ≤ n, s.stateNorm k = r.stateNorm k := by
  let a : Fin (n + M.memory) → r.Carrier := fun i => r.w i
  let V : Submodule ℝ r.Carrier := Submodule.span ℝ (Set.range a)
  have : FiniteDimensional ℝ V := FiniteDimensional.span_of_finite ℝ (Set.finite_range a)
  let e := (stdOrthonormalBasis ℝ V).repr
  let d := Module.finrank ℝ V
  let J : EuclideanSpace ℝ (Fin d) →ₗᵢ[ℝ] r.Carrier :=
    V.subtypeₗᵢ.comp e.symm.toLinearIsometry
  let P := polyak.embeddingProjection J
  let v : ℕ → EuclideanSpace ℝ (Fin d) := fun k => P (r.w k)
  let f : EuclideanSpace ℝ (Fin d) → ℝ := fun x => r.f (J x)
  have hf : polyak.CenteredSmoothStronglyConvex μ L f :=
    Functions.centered_restrict r.admissible J
  have hJ (i : ℕ) (hi : i < n + M.memory) : J (v i) = r.w i := by
    let x : V := ⟨r.w i, Submodule.subset_span ⟨⟨i, hi⟩, rfl⟩⟩
    have hx : J (e x) = r.w i := by
      change ((e.symm (e x) : V) : r.Carrier) = r.w i
      rw [e.symm_apply_apply]
    dsimp [v, P]
    rw [← hx, polyak.embeddingProjection_embed]
  have hquery (k : ℕ) : M.query v k = P (M.query r.w k) := by
    simp only [StationaryMethod.query, v, map_sum, map_smul]
  have hqueryJ (k : ℕ) (hk : k < n) : J (M.query v k) = M.query r.w k := by
    simp only [StationaryMethod.query, map_sum, map_smul]
    apply Finset.sum_congr rfl
    intro j _
    rw [hJ (k + j) (by omega)]
  have hv : ∀ k < n, ∑ j : Fin (M.memory + 1), M.recurrenceCoeff j • v (k + j) =
      gradient f (M.query v k) := by
    intro k hk
    calc
      _ = P (∑ j : Fin (M.memory + 1), M.recurrenceCoeff j • r.w (k + j)) := by
        simp only [v, map_sum, map_smul]
      _ = P (gradient r.f (M.query r.w k)) := congrArg P (r.trajectory k)
      _ = gradient f (M.query v k) := by
        rw [(Functions.hasGradientAt_restrict J r.admissible.differentiable _).gradient, hqueryJ k hk]
  let initial : Fin M.memory → EuclideanSpace ℝ (Fin d) := fun j => v j
  let w := M.run (gradient f) initial
  have hw : ∀ i < n + M.memory, w i = v i := M.run_eq_of_prefix n hv
  let s : Rates.HilbertRun M μ L :=
    ⟨EuclideanSpace ℝ (Fin d), f, hf, w, M.run_isTrajectory (gradient f) initial⟩
  refine ⟨s, inferInstance, J, ?_, ?_⟩
  · intro i hi
    change J (w i) = r.w i
    rw [hw _ hi, hJ _ hi]
  intro k hk
  change M.stateNorm w k = M.stateNorm r.w k
  unfold StationaryMethod.stateNorm
  congr 1
  apply Finset.sum_congr rfl
  intro j _
  have hi : k + j < n + M.memory := by omega
  rw [hw _ hi, ← J.norm_map, hJ _ hi]

/-- The complete finite-dimensional run preserves all finite-horizon ratios. -/
theorem exists_finiteDimensional_prefix (r : Rates.HilbertRun M μ L) (n : ℕ) :
    ∃ s : Rates.HilbertRun M μ L, FiniteDimensional ℝ s.Carrier ∧
      ∀ k ≤ n, s.stateNorm k = r.stateNorm k := by
  obtain ⟨s, hs, _, _, hnorm⟩ := exists_finiteDimensional_prefix_isometry r n
  exact ⟨s, hs, hnorm⟩

end Rates.HilbertRun
end nesterov
