import polyak.Growth.Envelope
import polyak.Dynamics.Original
import polyak.Dynamics.WorstCase

/-!
Article: Appendix A, W_N≤√2 Γ(N).
Use: connect free-state segments to the original, genuinely from-rest algorithm.
Proof: prepend the initial error once; the ℓ² initial state has norm √2 times its error.
-/

namespace polyak.Growth
noncomputable section
open polyak.Dynamics

/-- Article: prepending e₋₁=e₀. Use: the zero-momentum executor becomes a free segment. -/
def restPosition {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (σ : E → E) (A B β : ℝ) (e₀ : E) (k : ℕ) : E :=
  (normalizedState σ A B β e₀ k).2

/-- Article: prepended recurrence. Use: every transition includes the genuine first step. -/
theorem restPosition_recurrence {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (σ : E → E) (A B β : ℝ) (e₀ : E) (k : ℕ) :
    restPosition σ A B β e₀ (k+2) = A • restPosition σ A B β e₀ (k+1) +
      B • σ (restPosition σ A B β e₀ (k+1)) - β • restPosition σ A B β e₀ k := rfl

/-- Article: ℓ² state initialization. Use: the source constant √2 is exact. -/
theorem restPosition_stateNorm_zero {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (σ : E → E) (A B β : ℝ) (e₀ : E) :
    stateNorm (restPosition σ A B β e₀) 0 = Real.sqrt 2 * ‖e₀‖ := by
  change Real.sqrt (‖e₀‖^2+‖e₀‖^2) = _
  apply (sq_eq_sq₀ (Real.sqrt_nonneg _) (by positivity)).mp
  rw [Real.sq_sqrt (by positivity), mul_pow, Real.sq_sqrt (by norm_num : (0:ℝ)≤2)]
  ring

/-- Article: original trajectory upper bound. Use: all genuine functions and dimensions. -/
theorem original_ratio_le_envelope {μ L α β r : ℝ} {d N : ℕ}
    (hr : r ∈ ratios μ L α β d N) :
    r ≤ Real.sqrt 2 * envelope (normalizedA μ L α β) (normalizedB μ L α) β N := by
  obtain ⟨f,hf,a,x₀,hmin,hne,rfl⟩ := hr
  let ψ := originalPotential μ L f a
  let A := normalizedA μ L α β
  let B := normalizedB μ L α
  let e₀ := x₀-a
  let x := restPosition (gradient ψ) A B β e₀
  have hψ : NormalizedSmooth ψ := originalPotential_normalized hf a hmin
  let s := Segment.ofNormalized hψ x N (fun k _ => restPosition_recurrence _ _ _ _ _ k)
  have hs := stateNorm_le_envelope s
  have hs0 : stateNorm x 0 = Real.sqrt 2*‖e₀‖ := restPosition_stateNorm_zero _ _ _ _ _
  have he : x (N+1) = iterate (gradient f) α β x₀ N-a := by
    have hh := (original_normalized_run hf a hmin α β x₀).2 N
    exact (congrArg Prod.fst hh).symm
  have hb := norm_right_le_stateNorm x N
  rw [he] at hb
  have hh : ‖iterate (gradient f) α β x₀ N-a‖ ≤
      (Real.sqrt 2 * envelope A B β N)*‖e₀‖ := by
    calc
      _ ≤ stateNorm x N := hb
      _ ≤ envelope A B β N * stateNorm x 0 := hs
      _ = _ := by rw [hs0]; ring
  exact (div_le_iff₀ (norm_pos_iff.mpr (sub_ne_zero.mpr hne))).2 hh

/-- Article: W_N≤√2 Γ(N). Use: exact original supremum, including N=0. -/
theorem worstAll_le_envelope (μ L α β : ℝ) (N : ℕ) :
    worstAll μ L α β N ≤
      Real.sqrt 2 * envelope (normalizedA μ L α β) (normalizedB μ L α) β N := by
  apply csSup_le (Set.insert_nonempty _ _)
  intro r hr
  rcases hr with rfl | ⟨d,_,hr⟩
  · exact mul_nonneg (Real.sqrt_nonneg _) (envelope_nonneg _ _ _ _)
  · exact original_ratio_le_envelope hr

end
end polyak.Growth
