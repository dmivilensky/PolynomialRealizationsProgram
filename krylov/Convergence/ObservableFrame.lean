import krylov.Convergence.ObservableFCBounds
import krylov.LinearAlgebra.SpectralLowerForms
import krylov.Stability.ObservedProjection

/-!
Article: main_krylov, apG:Dunif, actual full-prefix reconstruction.
Use: pass from real normalized observations to the true orthogonal
projector and, at a completed cycle, the whole canonical gradient.
Source: the finite real Gram identity and finite-dimensional completeness.
No full-rank or inverse-domain premise is required by these conclusions.
-/
namespace krylov.Convergence
noncomputable section
open Matrix krylov.Methods krylov.LinearAlgebra krylov.Stability
open scoped InnerProductSpace Matrix.Norms.L2Operator
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {p : ℕ}

/-- The actual synthesis squared norm is its real coefficient Gram form.
Article: main_krylov, apG:Dunif. -/
theorem observable_gram_form (s : Fin p → E) (c : Fin p → ℝ) :
    c ⬝ᵥ (crossGram s s*ᵥc)=‖combine s c‖^2 := by
  simpa only [ContinuousLinearMap.id_apply,real_inner_self_eq_norm_sq] using
    operatorGram_form (ContinuousLinearMap.id ℝ E) s c

/-- A proved actual coefficient lower bound gives the true Gram spectral
endpoint, also for an empty observed prefix. Article: apG:Dunif. -/
theorem observable_gram_spectral (s : Fin p → E) (a : ℝ)
    (hform : ∀ c : Fin p → ℝ,a*‖WithLp.toLp 2 c‖^2≤c ⬝ᵥ (crossGram s s*ᵥc)) :
    ∀ i,a≤(crossGram_isHermitian s).eigenvalues i := by
  apply spectral_lower_of_form _ (crossGram_isHermitian s)
  intro v
  simpa only [Matrix.inner_toEuclideanCLM,WithLp.toLp_ofLp] using hform (WithLp.ofLp v)

/-- A positive actual synthesis gain proves independence of the observed
columns; individual reference step lengths never enter.
Article: main_krylov, apG:Dunif. -/
theorem observable_frame_independent (s : Fin p → E) (a : ℝ) (ha : 0<a)
    (hform : ∀ c : Fin p → ℝ,a*‖WithLp.toLp 2 c‖^2≤c ⬝ᵥ (crossGram s s*ᵥc)) :
    LinearIndependent ℝ s := by
  apply Fintype.linearIndependent_iff.mpr
  intro c hc
  have hh := hform c
  rw [observable_gram_form] at hh
  change combine s c=0 at hc
  rw [hc,norm_zero,zero_pow (by decide : 2≠0)] at hh
  have hsq : ‖WithLp.toLp 2 c‖^2≤0 := nonpos_of_mul_nonpos_right hh ha
  have hn : ‖WithLp.toLp 2 c‖=0 := by nlinarith only [hsq,norm_nonneg (WithLp.toLp 2 c)]
  have hz : c=0 := (WithLp.toLp_injective 2) (norm_eq_zero.mp hn)
  intro i
  exact congrFun hz i

variable [FiniteDimensional ℝ E]

/-- At the genuine full dimension, a positive measured Gram lower bound
makes the actual observed-span projector the identity.
Article: main_krylov, apG:Dunif, full-cycle termination. -/
theorem observable_full_projection (s : Fin p → E) (a : ℝ) (ha : 0<a)
    (hdim : p=Module.finrank ℝ E)
    (hform : ∀ c : Fin p → ℝ,a*‖WithLp.toLp 2 c‖^2≤c ⬝ᵥ (crossGram s s*ᵥc)) (g : E) :
    observedProjection s g=g := by
  have hs := (observable_frame_independent s a ha hform).span_eq_top_of_card_eq_finrank'
    (by simpa only [Fintype.card_fin] using hdim)
  change (Submodule.span ℝ (Set.range s)).starProjection g=g
  rw [hs]
  simp only [Submodule.starProjection_top,ContinuousLinearMap.id_apply]

/-- A completed real FC prefix reconstructs the genuine entire gradient
from the already proved staircase coordinates.
Article: main_krylov, apG:Dunif, uniform completion estimate. -/
theorem observable_full_residual (s : Fin p → E) (hdim : p=Module.finrank ℝ E)
    (hG : ‖crossGram s s-1‖≤1/8)
    (hform : ∀ c : Fin p → ℝ,(7/8:ℝ)*‖WithLp.toLp 2 c‖^2≤c ⬝ᵥ (crossGram s s*ᵥc))
    (g : E) : ‖g‖≤4*‖projectedResidual s g‖ := by
  have hh := observedProjection_residual_bound s (hG.trans (by norm_num)) g
  rw [observable_full_projection s (7/8) (by norm_num) hdim hform g] at hh
  exact hh

end
end krylov.Convergence
