import krylov.XR.LocalOracleQueries
import krylov.XR.LocalOracleBounds

/-!
Article: main_krylov, lem:xr-local, actual finite scalar-source stability.
Use: genuine Hessian perturbations preserve the entire finite adaptive
value/gradient transcript and any open strict branch of its data program.
The enclosure of every perturbed query is proved, not supplied as a source
or execution certificate.
Source: the actual derivative mean-value bound and finite adaptive continuity.
-/

namespace krylov.XR
noncomputable section
open Set Metric Filter Topology
open scoped InnerProductSpace NNReal
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- A true small Hessian perturbation preserves every finite open decision
of a continuous data-only scalar oracle program, with all its actual query
points enclosed in the original source ball. -/
theorem finite_scalar_source_open_branch
    (Q : E →L[ℝ] E) (hQ : Q.toLinearMap.IsSymmetric) (g₀ : E) (constant : ℝ)
    (query : (k : ℕ) → (Fin k → ℝ × E) → E) (N : ℕ)
    (radius : ℝ) (hradius : 0 < radius)
    (hquery : ∀ k < N, ContinuousAt (query k)
      (adaptiveTranscript query (fun x =>
        (quadraticObjective Q g₀ constant x, quadraticGradient Q g₀ x)) k))
    (hpoints : ∀ k < N, adaptivePoint query (fun x =>
      (quadraticObjective Q g₀ constant x, quadraticGradient Q g₀ x)) k ∈ ball 0 radius)
    (V : Set (Fin N → ℝ × E))
    (hV : V ∈ 𝓝 (adaptiveTranscript query (fun x =>
      (quadraticObjective Q g₀ constant x, quadraticGradient Q g₀ x)) N)) :
    ∃ epsilon : ℝ, 0 < epsilon ∧ ∀ (f : E → ℝ) (G : E → E) (H : E → E →L[ℝ] E),
      f 0 = quadraticObjective Q g₀ constant 0 → G 0 = g₀ →
      (∀ z ∈ ball 0 radius, HasFDerivAt f (innerSL ℝ (G z)) z) →
      (∀ z ∈ ball 0 radius, HasFDerivAt G (H z) z) →
      (∀ z ∈ ball 0 radius, ‖H z - Q‖ ≤ epsilon) →
      (∀ k < N, adaptivePoint query (fun x => (f x, G x)) k ∈ ball 0 radius) ∧
        adaptiveTranscript query (fun x => (f x, G x)) N ∈ V := by
  have hreference : Continuous (fun x =>
      (quadraticObjective Q g₀ constant x, quadraticGradient Q g₀ x)) := by
    apply Continuous.prodMk
    · exact continuous_iff_continuousAt.mpr (fun x =>
        (quadraticObjective_hasFDerivAt Q hQ g₀ constant x).continuousAt)
    · exact continuous_const.add Q.continuous
  obtain ⟨eta, heta, hstable⟩ := finite_adaptive_open_branch query _ hreference
    (ball 0 radius) isOpen_ball N hquery hpoints V hV
  let C := radius + radius ^ 2 + 1
  have hC : 0 < C := by dsimp only [C]; positivity
  refine ⟨eta / C, div_pos heta hC, ?_⟩
  intro f G H hf₀ hg₀ hF hG hH
  apply hstable (fun x => (f x, G x))
  intro z hz
  have hb := scalar_oracle_error_on_ball Q hQ g₀ constant f G H radius hradius
    ⟨eta / C, (div_pos heta hC).le⟩ hf₀ hg₀ hF hG hH z hz
  change ‖(f z, G z) - (quadraticObjective Q g₀ constant z, quadraticGradient Q g₀ z)‖ ≤
    eta / C * C at hb
  rwa [div_mul_cancel₀ eta hC.ne'] at hb

end
end krylov.XR
