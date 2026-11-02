import krylov.Convergence.SlidingGramInference
import krylov.Convergence.SecantWindowSource

/-!
Article: main_krylov, thm:G, independence-free source Gram bootstrap.
Use: derive the asymptotic orthonormality of a genuine full-conjugacy window
from actual derivative regularity and the measured conjugacy equations.
Source: the original local Lipschitz Hessian and exact observed FC equations.
-/

namespace krylov.Convergence
noncomputable section
open Matrix Set Filter Topology krylov.Methods
open scoped InnerProductSpace Matrix.Norms.L2Operator NNReal
variable {n : ℕ} {α : Type*} {l : Filter α}

/-- Genuine convergent full-conjugacy windows are asymptotically orthonormal
and eventually nonsingular, with inverse norm tending to one. Uniform
independence is proved here; it is not a hypothesis. -/
theorem conjugate_source_window_conditioning
    (G : EuclideanSpace ℝ (Fin (n+1)) → EuclideanSpace ℝ (Fin (n+1)))
    (H : EuclideanSpace ℝ (Fin (n+1)) → EuclideanSpace ℝ (Fin (n+1)) →L[ℝ]
      EuclideanSpace ℝ (Fin (n+1)))
    (S : Set (EuclideanSpace ℝ (Fin (n+1)))) (hS : Convex ℝ S)
    (h₀ : (0:EuclideanSpace ℝ (Fin (n+1)))∈S) {L : ℝ≥0}
    (hH : LipschitzOnWith L H S) (hH₀ : H 0=ContinuousLinearMap.id ℝ _)
    (hG : ∀ z∈S,HasFDerivAt G (H z) z)
    (a b : α → Fin (n+1) → EuclideanSpace ℝ (Fin (n+1)))
    (ha : ∀ i,Tendsto (fun z=>a z i) l (𝓝 0))
    (hb : ∀ i,Tendsto (fun z=>b z i) l (𝓝 0))
    (hmem : ∀ᶠ z in l,(∀ i,a z i∈S) ∧(∀ i,b z i∈S))
    (hne : ∀ᶠ z in l,∀ i,b z i-a z i≠0)
    (hconj : ∀ᶠ z in l,∀ i j : Fin (n+1),i<j →
      inner ℝ (G (b z i)-G (a z i)) (b z j-a z j)=0) :
    let V := fun z=>windowMatrix (unitWindow (fun i=>b z i-a z i))
    Tendsto (fun z=>(V z)ᵀ*V z) l (𝓝 1) ∧
    (∀ᶠ z in l,IsUnit (V z).det) ∧Tendsto (fun z=>‖(V z)⁻¹‖) l (𝓝 1) := by
  dsimp only
  let V := fun z=>windowMatrix (unitWindow (fun i=>b z i-a z i))
  let ε := fun z=>(L:ℝ)/2*sourceWindowRadius (a z) (b z)
  have hε : Tendsto ε l (𝓝 0) := by
    have hh := tendsto_finsetSum Finset.univ (fun i _=>(ha i).norm.add (hb i).norm)
    have hr : Tendsto (fun z=>sourceWindowRadius (a z) (b z)) l (𝓝 0) := by
      simpa only [sourceWindowRadius,norm_zero,add_zero,Finset.sum_const_zero] using hh
    simpa only [mul_zero] using hr.const_mul ((L:ℝ)/2)
  have hgram : Tendsto (fun z=>(V z)ᵀ*V z) l (𝓝 1) := by
    apply tendsto_iff_norm_sub_tendsto_zero.mpr
    apply squeeze_zero' (g:=fun z=>((n+1:ℕ):ℝ)*ε z)
    · exact Filter.Eventually.of_forall fun z=>norm_nonneg ((V z)ᵀ*V z-1)
    · filter_upwards [hmem,hne,hconj] with z hz hsz hcz
      rw [←crossGram_windowMatrix]
      exact conjugate_window_gram_bound _ _ (unitWindow_norm _ hsz)
        (mul_nonneg (by positivity) (sourceWindowRadius_nonneg _ _))
        (source_unit_window_error G H S hS h₀ hH hH₀ hG _ _ hz.1 hz.2 hsz)
        (conjugate_window_unit _ _ hcz)
    · simpa only [mul_zero] using hε.const_mul ((n+1:ℕ):ℝ)
  exact ⟨hgram,(gram_identity_window_conditioning V hgram).1,
    (gram_identity_window_conditioning V hgram).2⟩

end
end krylov.Convergence
