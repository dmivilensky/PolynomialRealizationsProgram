import krylov.XR.EuclideanModel
import krylov.XR.GlobalAlgorithm

/-!
Article: main_krylov, thm:XR and cor:xrF, Euclidean-split globalization.
Use: instantiate the same actual safeguarded one-probe executor theorem
with the literal Euclidean value model. Scalar gate/model selection does
not change the proved safeguard or genuine Armijo backtracking mechanism.
Source: the generic executor globalization and actual original initialization.
-/
namespace krylov.XR
noncomputable section
open Filter Set
open scoped InnerProductSpace NNReal Topology
variable {n : ℕ}

/-- Global stationarity of the complete literal XR algorithm, with all
rank/refutation/value/Radau/capacity decisions and the rejected probe active.
No acceptance, descent, or convergence certificate is an algorithm input. -/
theorem euclideanAlgorithmRun_global (P : Parameters) (hP : P.Valid n)
    (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (G : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (hF : ∀ x, HasFDerivAt f (innerSL ℝ (G x)) x)
    (L : ℝ≥0) (hL : 0 < (L : ℝ)) (hG : LipschitzWith L G)
    (hb : ∃ b, ∀ x, b ≤ f x) (x₀ : EuclideanSpace ℝ (Fin n))
    (bounds : SpectralBounds := none) :
    Summable (fun k => ‖G (euclideanAlgorithmRun P f G x₀ bounds k).point‖ ^ 2) ∧
      Tendsto (fun k => ‖G (euclideanAlgorithmRun P f G x₀ bounds k).point‖) atTop (𝓝 0) ∧
      ∀ (z : EuclideanSpace ℝ (Fin n)) (indices : ℕ → ℕ), Tendsto indices atTop atTop →
        Tendsto ((fun k => (euclideanAlgorithmRun P f G x₀ bounds k).point) ∘ indices) atTop (𝓝 z) →
          G z = 0 := by
  have hs : Summable (fun k => ‖G (euclideanAlgorithmRun P f G x₀ bounds k).point‖ ^ 2) := by
    by_cases hg : G x₀ = 0
    · have hr k : euclideanAlgorithmRun P f G x₀ bounds k = algorithmInitialState P f G x₀ bounds :=
        run_stationary P n (euclideanAlgorithmModel P) f G _ hg k
      simp only [hr, algorithmInitialState, initialState, hg, norm_zero, zero_pow (by norm_num : 2 ≠ 0)]
      exact summable_zero
    · have hc := algorithmInitialState_constants P hP f G x₀ bounds hg
      rcases hP with ⟨_, _, _, _, _, _, hsig, hsig₁, _, _, _, _⟩
      exact run_gradient_square_summable P n (euclideanAlgorithmModel P) f G hF L hL hG
        hsig (hsig₁.trans (by norm_num)) _ hc.1 hc.2 rfl rfl hb
  refine ⟨hs, gradient_norm_tendsto_zero _ G hs, ?_⟩
  intro z indices hi hx
  exact stationary_of_limit _ G hG.continuous hs z indices hi hx

/-- On bounded sublevels the literal algorithm has a stationary cluster
point. In finite Euclidean dimension this follows from Bolzano--Weierstrass. -/
theorem euclideanAlgorithmRun_stationary_cluster (P : Parameters) (hP : P.Valid n)
    (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (G : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (hF : ∀ x, HasFDerivAt f (innerSL ℝ (G x)) x)
    (L : ℝ≥0) (hL : 0 < (L : ℝ)) (hG : LipschitzWith L G)
    (hb : ∃ b, ∀ x, b ≤ f x) (x₀ : EuclideanSpace ℝ (Fin n))
    (bounds : SpectralBounds := none)
    (hbounded : Bornology.IsBounded (Set.range (fun k => (euclideanAlgorithmRun P f G x₀ bounds k).point))) :
    ∃ (z : EuclideanSpace ℝ (Fin n)) (indices : ℕ → ℕ), StrictMono indices ∧
      Tendsto ((fun k => (euclideanAlgorithmRun P f G x₀ bounds k).point) ∘ indices) atTop (𝓝 z) ∧ G z = 0 := by
  obtain ⟨z, _, indices, hi, hx⟩ := tendsto_subseq_of_bounded hbounded
    (fun k => ⟨k, rfl⟩)
  exact ⟨z, indices, hi, hx,
    (euclideanAlgorithmRun_global P hP f G hF L hL hG hb x₀ bounds).2.2 z indices hi.tendsto_atTop hx⟩

/-- Every actual accepted iterate remains in the original sublevel. -/
theorem euclideanAlgorithmRun_sublevel (P : Parameters) (hP : P.Valid n)
    (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (G : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (hF : ∀ x, HasFDerivAt f (innerSL ℝ (G x)) x)
    (L : ℝ≥0) (hL : 0 < (L : ℝ)) (hG : LipschitzWith L G)
    (x₀ : EuclideanSpace ℝ (Fin n)) (bounds : SpectralBounds) (k : ℕ) :
    f (euclideanAlgorithmRun P f G x₀ bounds k).point ≤ f x₀ := by
  by_cases hz : G x₀ = 0
  · have hr := run_stationary P n (euclideanAlgorithmModel P) f G
      (algorithmInitialState P f G x₀ bounds) hz k
    change f (run P n (euclideanAlgorithmModel P) f G (algorithmInitialState P f G x₀ bounds) k).point ≤ _
    rw [hr]
    exact le_rfl
  · let S₀ := algorithmInitialState P f G x₀ bounds
    have hc := algorithmInitialState_constants P hP f G x₀ bounds hz
    rcases hP with ⟨_, _, _, _, _, _, hsig, hsig₁, _, _, _, _⟩
    have hc₁ : 0 < S₀.descentConstant := hc.1
    have hc₂ : 0 < S₀.normConstant := hc.1.trans_le hc.2
    have hsig₂ : 0 ≤ 1 - P.armijo := by linarith
    have hm : 0 ≤ minimumLength P.armijo S₀.descentConstant S₀.normConstant L := by
      apply le_min (by norm_num)
      positivity
    have hv (j : ℕ) : (run P n (euclideanAlgorithmModel P) f G S₀ j).value ≤ S₀.value := by
      induction j with
      | zero => exact le_rfl
      | succ j ih =>
        have hd := run_sufficient_decrease P n (euclideanAlgorithmModel P) f G hF L hL hG
          hsig (hsig₁.trans (by norm_num)) S₀ hc.1 hc.2 rfl rfl j
        exact (hd.trans (sub_le_self _ (mul_nonneg
          (mul_nonneg (mul_nonneg hsig.le hm) hc.1.le) (sq_nonneg _)))).trans ih
    have hcache := (run_cache_constants P n (euclideanAlgorithmModel P) f G S₀ rfl rfl k).1
    have hvk := hv k
    rw [hcache] at hvk
    exact hvk

/-- Bounded original sublevels give a stationary cluster point of the
literal algorithm, as stated in Theorem XR. -/
theorem euclideanAlgorithmRun_stationary_cluster_of_bounded_sublevel (P : Parameters) (hP : P.Valid n)
    (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (G : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (hF : ∀ x, HasFDerivAt f (innerSL ℝ (G x)) x)
    (L : ℝ≥0) (hL : 0 < (L : ℝ)) (hG : LipschitzWith L G)
    (hb : ∃ b, ∀ x, b ≤ f x) (x₀ : EuclideanSpace ℝ (Fin n))
    (bounds : SpectralBounds := none)
    (hbounded : Bornology.IsBounded {x | f x ≤ f x₀}) :
    ∃ (z : EuclideanSpace ℝ (Fin n)) (indices : ℕ → ℕ), StrictMono indices ∧
      Tendsto ((fun k => (euclideanAlgorithmRun P f G x₀ bounds k).point) ∘ indices) atTop (𝓝 z) ∧ G z = 0 := by
  apply euclideanAlgorithmRun_stationary_cluster P hP f G hF L hL hG hb x₀ bounds
  apply hbounded.subset
  rintro x ⟨k, rfl⟩
  exact euclideanAlgorithmRun_sublevel P hP f G hF L hL hG x₀ bounds k

/-- The literal Euclidean split executor has the same quantitative
sufficient decrease, including its real rejected-probe branch. -/
theorem euclideanAlgorithmRun_sufficient_decrease (P : Parameters) (hP : P.Valid n)
    (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (G : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (hF : ∀ x, HasFDerivAt f (innerSL ℝ (G x)) x)
    (L : ℝ≥0) (hL : 0 < (L : ℝ)) (hG : LipschitzWith L G)
    (x₀ : EuclideanSpace ℝ (Fin n)) (bounds : SpectralBounds) (hg : G x₀ ≠ 0) (k : ℕ) :
    let S₀ := algorithmInitialState P f G x₀ bounds
    f (euclideanAlgorithmRun P f G x₀ bounds (k+1)).point ≤
      f (euclideanAlgorithmRun P f G x₀ bounds k).point-
        (P.armijo*minimumLength P.armijo S₀.descentConstant S₀.normConstant L*S₀.descentConstant)*
          ‖G (euclideanAlgorithmRun P f G x₀ bounds k).point‖^2 := by
  have hc := algorithmInitialState_constants P hP f G x₀ bounds hg
  have hd := run_sufficient_decrease P n (euclideanAlgorithmModel P) f G hF L hL hG
    hP.2.2.2.2.2.2.1 (hP.2.2.2.2.2.2.2.1.trans (by norm_num))
    (algorithmInitialState P f G x₀ bounds) hc.1 hc.2 rfl rfl k
  have hcache j := (run_cache_constants P n (euclideanAlgorithmModel P) f G
    (algorithmInitialState P f G x₀ bounds) rfl rfl j).1
  simpa only [hcache, euclideanAlgorithmRun] using hd

end
end krylov.XR
