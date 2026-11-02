import krylov.XR.GlobalAlgorithm
import Mathlib.Analysis.Real.Sqrt

/-!
Article: krylov, the unnumbered stationarity bound following thm:XR.
Use: retain the finite descent telescope and count actual accepted outer steps,
then select an actually evaluated gradient no larger than its finite average.
Source: the standard gradient-related Armijo complexity argument, applied to
the already proved one-probe executor decrease. The model is arbitrary, so the
same statements apply to both algorithmModel and the practical secant policy.
-/

namespace krylov.XR
noncomputable section
open scoped InnerProductSpace NNReal BigOperators

/-- Finite descent telescopes before any infinite-sum or limit argument. -/
theorem descent_finite_sum_le (v a : ℕ → ℝ) (c : ℝ)
    (hd : ∀ k, v (k+1) ≤ v k - c * a k) (N : ℕ) :
    c * ∑ k ∈ Finset.range N, a k ≤ v 0 - v N := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [Finset.sum_range_succ, mul_add]
    linarith [hd N]

/-- One member of a nonempty finite descent history is bounded by its
objective-budget average. No monotonicity of the individual errors is used. -/
theorem descent_exists_le_average (v a : ℕ → ℝ) (c b : ℝ) (hc : 0 < c)
    (hb : ∀ k, b ≤ v k) (hd : ∀ k, v (k+1) ≤ v k - c * a k)
    (N : ℕ) (hN : 0 < N) :
    ∃ k < N, a k ≤ (v 0 - b) / (c * (N : ℝ)) := by
  by_contra! h
  have hn : (0 : ℝ) < N := Nat.cast_pos.mpr hN
  have hs : (N : ℝ) * ((v 0 - b) / (c * (N : ℝ))) <
      ∑ k ∈ Finset.range N, a k := by
    simpa only [Finset.sum_const, Finset.card_range, nsmul_eq_mul] using
      Finset.sum_lt_sum_of_nonempty (Finset.nonempty_range_iff.mpr (Nat.ne_of_gt hN))
        (fun k hk => h k (Finset.mem_range.mp hk))
  have he : c * ((N : ℝ) * ((v 0 - b) / (c * (N : ℝ)))) = v 0 - b := by
    field_simp
  have ht := descent_finite_sum_le v a c hd N
  have hstrict := mul_lt_mul_of_pos_left hs hc
  rw [he] at hstrict
  linarith [hb N]

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Quantitative stationarity of the genuine safeguarded one-probe run.
The selected index is an actual cached gradient at an accepted outer iterate;
the count is accepted steps, not the number of backtracking oracle queries. -/
theorem run_exists_small_gradient (P : Parameters) (dimension : ℕ)
    (model : State E → ModelResult E) (f : E → ℝ) (G : E → E)
    (hF : ∀ x, HasFDerivAt f (innerSL ℝ (G x)) x)
    (L : ℝ≥0) (hL : 0 < (L : ℝ)) (hG : LipschitzWith L G)
    (hsigma : 0 < P.armijo) (hsigma₁ : P.armijo < 1) (S₀ : State E)
    (hc₁ : 0 < S₀.descentConstant) (hc₂ : S₀.descentConstant ≤ S₀.normConstant)
    (hf : S₀.value = f S₀.point) (hg : S₀.gradient = G S₀.point)
    (b : ℝ) (hb : ∀ x, b ≤ f x) (N : ℕ) (hN : 0 < N) :
    ∃ k < N, ‖G (run P dimension model f G S₀ k).point‖ ≤
      Real.sqrt ((f S₀.point - b) /
        ((P.armijo * minimumLength P.armijo S₀.descentConstant S₀.normConstant L *
          S₀.descentConstant) * (N : ℝ))) := by
  have ht : 0 < minimumLength P.armijo S₀.descentConstant S₀.normConstant L := by
    apply lt_min (by norm_num)
    have hn := hc₁.trans_le hc₂
    exact div_pos (mul_pos (sub_pos.mpr hsigma₁) hc₁) (by positivity)
  have hc := mul_pos (mul_pos hsigma ht) hc₁
  obtain ⟨k, hk, ha⟩ := descent_exists_le_average
    (fun j => (run P dimension model f G S₀ j).value)
    (fun j => ‖G (run P dimension model f G S₀ j).point‖ ^ 2)
    _ b hc
    (fun j => by rw [(run_cache_constants P dimension model f G S₀ hf hg j).1]; exact hb _)
    (run_sufficient_decrease P dimension model f G hF L hL hG hsigma hsigma₁
      S₀ hc₁ hc₂ hf hg) N hN
  refine ⟨k, hk, Real.le_sqrt_of_sq_le ?_⟩
  simpa only [run, hf] using ha

/-- The printed initialization gives the same finite complexity bound for
every model, including practicalModel. A stationary initial state is included
by its actual stopped execution, without a positive-safeguard hypothesis. -/
theorem initializedRun_exists_small_gradient {n : ℕ} (P : Parameters) (hP : P.Valid n)
    (model : State (EuclideanSpace ℝ (Fin n)) → ModelResult (EuclideanSpace ℝ (Fin n)))
    (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (G : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (hF : ∀ x, HasFDerivAt f (innerSL ℝ (G x)) x)
    (L : ℝ≥0) (hL : 0 < (L : ℝ)) (hG : LipschitzWith L G)
    (b : ℝ) (hb : ∀ x, b ≤ f x) (x₀ : EuclideanSpace ℝ (Fin n))
    (bounds : SpectralBounds) (N : ℕ) (hN : 0 < N) :
    let S₀ := algorithmInitialState P f G x₀ bounds
    ∃ k < N, ‖G (run P n model f G S₀ k).point‖ ≤
      Real.sqrt ((f x₀ - b) /
        ((P.armijo * minimumLength P.armijo S₀.descentConstant S₀.normConstant L *
          S₀.descentConstant) * (N : ℝ))) := by
  dsimp only
  by_cases hz : G x₀ = 0
  · refine ⟨0, hN, ?_⟩
    simpa only [run, algorithmInitialState, initialState, hz, norm_zero] using
      Real.sqrt_nonneg ((f x₀ - b) /
        ((P.armijo * minimumLength P.armijo
          (algorithmInitialState P f G x₀ bounds).descentConstant
          (algorithmInitialState P f G x₀ bounds).normConstant L *
          (algorithmInitialState P f G x₀ bounds).descentConstant) * (N : ℝ)))
  · have hc := algorithmInitialState_constants P hP f G x₀ bounds hz
    rcases hP with ⟨_, _, _, _, _, _, hs, hs₁, _, _, _, _⟩
    exact run_exists_small_gradient P n model f G hF L hL hG hs
      (hs₁.trans (by norm_num)) _ hc.1 hc.2 rfl rfl b hb N hN

end
end krylov.XR
