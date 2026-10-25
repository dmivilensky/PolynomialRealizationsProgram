import polyak.Realization.Potential
import polyak.Dynamics.Instances
import polyak.Dynamics.Embedding

/-!
Article: Appendix A, startup recurrence and actual heavy-ball execution.
Use: the constructed infinite table is the from-rest trajectory of one genuine objective.
Proof: the corrected initial gradient gives the first step, and uniqueness closes the full executor.
-/

namespace polyak.Realization
noncomputable section
open Interpolation Dynamics

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-- Article: the mode gradient required by the first zero-impulse step. -/
def initialGradient (x : Option ℕ → E) (A B β : ℝ) : E :=
  (1/B) • (x (some 1)-(A-β) • x (some 0))

omit [CompleteSpace E] in
/-- Article: exact first mode step. -/
theorem initialGradient_step (x : Option ℕ → E) (A B β : ℝ) (hB : B≠0) :
    x (some 1)=(A-β) • x (some 0)+B • initialGradient x A B β := by
  unfold initialGradient
  rw [smul_smul, mul_one_div_cancel hB, one_smul]
  module

omit [CompleteSpace E] in
/-- Article: zero-impulse startup in both orthogonal components. -/
theorem startupPosition_first (x σ : Option ℕ → E) (A B β τ Y : ℝ) (hB : B≠0) :
    startupPosition x A B β τ Y (some 1)=(A-β) • startupPosition x A B β τ Y (some 0)+
      B • startupGradient σ (initialGradient x A B β) A B β τ Y (some 0) := by
  apply WithLp.ofLp_injective 2
  simp only [startupPosition,startupGradient,productPosition,productGradient,correctGradient,
    scalarPosition,response_zero,response_one,ite_true,mul_one,WithLp.ofLp_add,WithLp.ofLp_smul]
  apply Prod.ext
  · exact initialGradient_step x A B β hB
  · change Y*(A+B*τ-β)=(A-β)*Y+B*(τ*Y)
    ring

omit [CompleteSpace E] in
/-- Article: every later startup step obeys the same normalized recurrence. -/
theorem startupPosition_recurrence (x σ : Option ℕ → E) (A B β τ Y : ℝ)
    (hrec : ∀ k, x (some (k+2))=A • x (some (k+1))+B • σ (some (k+1))-β • x (some k))
    (k : ℕ) :
    startupPosition x A B β τ Y (some (k+2))=A • startupPosition x A B β τ Y (some (k+1))+
      B • startupGradient σ (initialGradient x A B β) A B β τ Y (some (k+1))-
      β • startupPosition x A B β τ Y (some k) := by
  apply WithLp.ofLp_injective 2
  have hn : (some (k+1) : Option ℕ)≠some 0 := by simp
  simp only [startupPosition,startupGradient,productPosition,productGradient,correctGradient,
    scalarPosition,hn,↓reduceIte,WithLp.ofLp_add,WithLp.ofLp_sub,WithLp.ofLp_smul]
  apply Prod.ext
  · exact hrec k
  · change Y*response (A+B*τ) β (k+2)=
      A*(Y*response (A+B*τ) β (k+1))+B*(τ*(Y*response (A+B*τ) β (k+1)))-
        β*(Y*response (A+B*τ) β k)
    rw [response_recurrence]
    ring

/-- Article: realized trajectories are true heavy-ball iterates from rest.
Use: no free-state or supplied-gradient executor replaces the original algorithm. -/
theorem startup_iterate {μ L α β τ Y : ℝ} (x σ : Option ℕ → E)
    {ψ : WithLp 2 (E × ℝ) → ℝ} (hψ : NormalizedSmooth ψ)
    (hB : normalizedB μ L α≠0)
    (hdata : ∀ i,gradient ψ (startupPosition x (normalizedA μ L α β) (normalizedB μ L α) β τ Y i)=
      startupGradient σ (initialGradient x (normalizedA μ L α β) (normalizedB μ L α) β)
        (normalizedA μ L α β) (normalizedB μ L α) β τ Y i)
    (hrec : ∀ k,x (some (k+2))=normalizedA μ L α β • x (some (k+1))+
      normalizedB μ L α • σ (some (k+1))-β • x (some k)) (N : ℕ) :
    iterate (gradient (denormalizeFunction μ L ψ)) α β
      (startupPosition x (normalizedA μ L α β) (normalizedB μ L α) β τ Y (some 0)) N=
        startupPosition x (normalizedA μ L α β) (normalizedB μ L α) β τ Y (some N) := by
  let A := normalizedA μ L α β
  let B := normalizedB μ L α
  let X := startupPosition x A B β τ Y
  let S := startupGradient σ (initialGradient x A B β) A B β τ Y
  have hg (i : Option ℕ) : gradient (denormalizeFunction μ L ψ) (X i)=
      ((L+μ)/2) • X i-((L-μ)/2) • S i := by
    rw [(hasGradientAt_denormalize hψ.differentiable (X i)).gradient,hdata]
  have heq : (fun k => X (some k))=iterate (gradient (denormalizeFunction μ L ψ)) α β (X (some 0)) := by
    apply iterate_unique
    · rfl
    · have hfirst : X (some 1)=(A-β) • X (some 0)+B • S (some 0) :=
        startupPosition_first x σ A B β τ Y hB
      rw [hfirst,hg]
      dsimp [A,B,normalizedA,normalizedB]
      module
    · intro k
      have hr : X (some (k+2))=A • X (some (k+1))+B • S (some (k+1))-β • X (some k) :=
        startupPosition_recurrence x σ A B β τ Y hrec k
      rw [hr,hg]
      dsimp [A,B,normalizedA,normalizedB]
      module
  exact (congrFun heq N).symm

omit [CompleteSpace E] [InnerProductSpace ℝ E] in
/-- Article: the mode component lower-bounds the true Hilbert norm. -/
theorem norm_le_startupPosition (x : Option ℕ → E) (A B β τ Y : ℝ) (k : ℕ) :
    ‖x (some k)‖ ≤ ‖startupPosition x A B β τ Y (some k)‖ :=
  WithLp.norm_fst_le E (startupPosition x A B β τ Y (some k))

end
end polyak.Realization
