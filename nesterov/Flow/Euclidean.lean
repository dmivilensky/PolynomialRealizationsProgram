import nesterov.Flow.Results
import polyak.Functions.Embedding

/-!
Article: Theorem `flow`(c), the literal real space R^(2J).
Use: one isometric coordinate change transports the actual objective,
gradients, position and velocity, retaining every norm and all exponents.
-/

noncomputable section

namespace nesterov.Flow

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]

theorem IsSolution.isometric_transport {θ m L : ℝ} {f : E → ℝ} {x v : ℝ → E}
    (hf : polyak.CenteredSmoothStronglyConvex m L f) (hx : IsSolution θ f x v)
    (T : E →ₗᵢ[ℝ] F) :
    IsSolution θ (polyak.extendObjective m L T f) (fun t => T (x t)) (fun t => T (v t)) := by
  constructor
  · intro t ht
    exact T.toContinuousLinearMap.hasFDerivAt.comp_hasDerivAt t (hx.position_derivative t ht)
  · intro t ht
    have hh := T.toContinuousLinearMap.hasFDerivAt.comp_hasDerivAt t (hx.velocity_derivative t ht)
    simpa only [Function.comp_def, LinearIsometry.coe_toContinuousLinearMap, map_sub, map_smul,
      polyak.gradient_extendObjective_embed hf.toSmoothStronglyConvex]
      using hh

theorem complex_euclidean_finrank (J : ℕ) :
    Module.finrank ℝ (EuclideanSpace ℂ (Fin J)) = 2 * J := by
  have hh := Module.finrank_mul_finrank ℝ ℂ (EuclideanSpace ℂ (Fin J))
  simpa using hh.symm

/-- The canonical real orthonormal coordinates of the orthogonal complex planes. -/
def realCoordinates (J : ℕ) :
    EuclideanSpace ℂ (Fin J) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin (2 * J)) := by
  rw [← complex_euclidean_finrank J]
  exact (stdOrthonormalBasis ℝ (EuclideanSpace ℂ (Fin J))).repr

/-- Theorem flow(c) on R^(2J), with the exact two norm identities and all
three sharp exponents on the transported genuine smooth objective. -/
theorem exists_real_spiral_witness {θ m c : ℝ} (hθ : 0 < θ) (hm : 0 < m)
    (hc : θ / 3 < c) (hcQ : c < cQ θ m) :
    ∃ (J : ℕ) (L : ℝ) (f : EuclideanSpace ℝ (Fin (2 * J)) → ℝ)
      (x v : ℝ → EuclideanSpace ℝ (Fin (2 * J))), 0 < J ∧ m < L ∧
      polyak.CenteredSmoothStronglyConvex m L f ∧ IsSolution θ f x v ∧
      ‖x 0‖ = 1 ∧ (∀ t : ℝ, ‖x t‖ = Real.exp (-c * t) * ‖x 0‖) ∧
      (∀ t : ℝ, ‖v t‖ = Real.exp (-c * t) * ‖v 0‖) ∧
      decayExponent x v = (c : EReal) ∧
      observableExponent (fun t => f (x t)) = ((2 * c : ℝ) : EReal) ∧
      observableExponent (fun t => energy f (x t) (v t)) = ((2 * c : ℝ) : EReal) := by
  obtain ⟨J, L, f, x, v, hJ, hL, hf, hsol, hzero, hxnorm, hvnorm, hs, hv, he⟩ :=
    exists_spiral_witness hθ hm hc hcQ
  let T := (realCoordinates J).toLinearIsometry
  let g := polyak.extendObjective m L T f
  have hvalue (t : ℝ) : g (T (x t)) = f (x t) := polyak.extendObjective_embed hL T f (x t)
  refine ⟨J, L, g, fun t => T (x t), fun t => T (v t), hJ, hL,
    hf.extendObjective T, hsol.isometric_transport hf T, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa only [T.norm_map] using hzero
  · simpa only [T.norm_map] using hxnorm
  · simpa only [T.norm_map] using hvnorm
  · simpa only [decayExponent, T.norm_map] using hs
  · simpa only [hvalue] using hv
  · simpa only [energy, hvalue, T.norm_map] using he

end nesterov.Flow
