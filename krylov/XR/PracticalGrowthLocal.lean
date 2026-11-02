import krylov.XR.PracticalGrowthModel

/-!
# Source-driven local activation for practical XR

Article Theorem 7.3 (`thm:grow`). Actual observations, pre-cleanup
independence and the true Hessian imply retention and Taylor data along
`practicalRun`; the generic safeguard controls the trial before its
inactivity has been proved.
-/
namespace krylov.XR
noncomputable section
open Set Metric Filter Topology krylov.Methods
open scoped InnerProductSpace NNReal
variable {n : ℕ}
set_option maxHeartbeats 800000

/-- Original local source and pre-cleanup G2 force actual eventual rank
and refutation-test retention in the literal data-only algorithm. -/
theorem practicalRun_eventually_retains_window (P : Parameters) (hP : P.Valid n)
    (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (G : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (H : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (x₀ center : EuclideanSpace ℝ (Fin n))
    (hF : ∀ᶠ z in 𝓝 center, HasFDerivAt f (innerSL ℝ (G z)) z)
    (hG : ∀ᶠ z in 𝓝 center, HasFDerivAt G (H z) z) (hH : ContinuousAt H center)
    (mu sigma : ℝ) (hmu : 0 < mu) (hsigma : 0 < sigma)
    (hpositive : ∀ v, mu * ‖v‖ ^ 2 ≤ inner ℝ v (H center v))
    (hconv : Tendsto (fun k => (practicalRun P f G x₀ k).point) atTop (𝓝 center))
    (hne : ∀ k, (practicalRun P f G x₀ k).point ≠ center)
    (K₀ : ℕ)
    (hgain : ∀ k, K₀ ≤ k →
      let W := incomingWindow (practicalRun P f G x₀ k)
      ∀ w : Fin W.length → ℝ, sigma ^ 2 * ‖WithLp.toLp 2 w‖ ^ 2 ≤
        ‖combine (krylov.Convergence.unitWindow (storedSteps W)) w‖ ^ 2) :
    ∃ K, ∀ k, K ≤ k →
      let S := practicalRun P f G x₀ k
      rankDeletion (incomingWindow S) = 0 ∧
        (practicalModel P S).pairs = incomingWindow S ∧
        (practicalModel P S).pairsBeforeTest = (incomingWindow S).length ∧
        (practicalModel P S).deletedByTest = 0 := by
  have htheta : 0 < P.windowThreshold := hP.2.2.2.2.2.1
  have hcoerc : 0 < localCoercivity mu sigma := by unfold localCoercivity; positivity
  let epsilon : ℝ := min (mu * sigma ^ 2 / (8 * ((n : ℝ) + 1)))
    (P.windowThreshold * localCoercivity mu sigma / (4 * ((n : ℝ) + 1)))
  have hepsilon : 0 < epsilon := by dsimp only [epsilon]; positivity
  let e : ℝ≥0 := ⟨epsilon, hepsilon.le⟩
  have hsmall : (n : ℝ) * epsilon ≤ mu * sigma ^ 2 / 4 := by
    have h := min_le_left (mu * sigma ^ 2 / (8 * ((n : ℝ) + 1)))
      (P.windowThreshold * localCoercivity mu sigma / (4 * ((n : ℝ) + 1)))
    change epsilon ≤ _ at h
    have hh := (le_div_iff₀ (by positivity : 0 < 8 * ((n : ℝ) + 1))).mp h
    nlinarith [hepsilon]
  have hgate : 2 * (n : ℝ) * epsilon / localCoercivity mu sigma < P.windowThreshold := by
    have h := min_le_right (mu * sigma ^ 2 / (8 * ((n : ℝ) + 1)))
      (P.windowThreshold * localCoercivity mu sigma / (4 * ((n : ℝ) + 1)))
    change epsilon ≤ _ at h
    have hh := (le_div_iff₀ (by positivity : 0 < 4 * ((n : ℝ) + 1))).mp h
    apply (div_lt_iff₀ hcoerc).2
    nlinarith [mul_pos htheta hcoerc, hepsilon]
  have hsym := local_hessian_symmetric f G H center hF hG.self_of_nhds
  obtain ⟨K₁, hK₁⟩ := practicalRun_eventually_secant_errors P hP f G H x₀ center hF hG hH
    mu hmu hpositive hconv hne e hepsilon
  refine ⟨max K₀ K₁, ?_⟩
  intro k hk
  let S := practicalRun P f G x₀ k
  have hlen : (incomingWindow S).length ≤ n := by
    simp only [incomingWindow, retainNewest_length]
    omega
  have hlenR : ((incomingWindow S).length : ℝ) ≤ n := by exact_mod_cast hlen
  have hy i : ‖storedImages (incomingWindow S) i - H center (storedSteps (incomingWindow S) i)‖ ≤
      epsilon * ‖storedSteps (incomingWindow S) i‖ := by
    exact hK₁ k (by omega) _ (List.mem_of_mem_drop (List.get_mem _ i))
  exact algorithmModel_local_retention P htheta S (practicalRun_pairs_positive P f G x₀ k)
    (H center) hsym mu sigma epsilon hmu hsigma hepsilon.le hpositive (hgain k (by omega)) hy
    ((mul_le_mul_of_nonneg_right hlenR hepsilon.le).trans hsmall)
    ((div_le_div_of_nonneg_right (by nlinarith [mul_le_mul_of_nonneg_right hlenR hepsilon.le])
      hcoerc.le).trans_lt hgate)


/-- Under G1 a genuine positive accepted pair is eventually appended at
every step, so the original incoming window is eventually nonempty. -/
theorem practicalRun_eventually_incoming_nonempty (P : Parameters) (hP : P.Valid n)
    (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (G : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (H : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (x₀ center : EuclideanSpace ℝ (Fin n))
    (hF : ∀ᶠ z in 𝓝 center, HasFDerivAt f (innerSL ℝ (G z)) z)
    (hG : ∀ᶠ z in 𝓝 center, HasFDerivAt G (H z) z) (hH : ContinuousAt H center)
    (mu : ℝ) (hmu : 0 < mu) (hpositive : ∀ v, mu * ‖v‖ ^ 2 ≤ inner ℝ v (H center v))
    (hconv : Tendsto (fun k => (practicalRun P f G x₀ k).point) atTop (𝓝 center))
    (hne : ∀ k, (practicalRun P f G x₀ k).point ≠ center) :
    ∃ K, ∀ k, K ≤ k → 0 < (incomingWindow (practicalRun P f G x₀ k)).length := by
  have hinit := practicalRun_initial_gradient_ne_zero P f G x₀ center hconv hne
  have hc := algorithmInitialState_constants P hP f G x₀ none hinit
  have hsig := hP.2.2.2.2.2.2.1
  have hsig₁ : P.armijo < 1 := hP.2.2.2.2.2.2.2.1.trans (by norm_num)
  obtain ⟨K, hK⟩ := run_eventually_local_new_pairs P n (practicalModel P) f G H
    (algorithmInitialState P f G x₀ none) rfl rfl hc.1 hc.2 hsig hsig₁
    center hF hG hH mu hmu hpositive hconv hne 1 (by norm_num)
  have hn : 0 < n := by have := hP.1; have := hP.2.1; have := hP.2.2.1; omega
  refine ⟨K + 1, ?_⟩
  intro k hk
  cases k with
  | zero => omega
  | succ k =>
    have hnew := hK k (by omega)
    have hlen := outerAdvance_pairs_nonempty P n (practicalModel P) f G
      (practicalRun P f G x₀ k) hnew.1 hnew.2.2.2
    have hmem := (practicalRun_memory_invariants P hP f G x₀ (k + 1)).1
    have hcap : 0 < (practicalRun P f G x₀ (k + 1)).capacity := by
      have := hP.1
      omega
    exact incomingWindow_nonempty _ hlen hcap hn


/-- Genuine local C² data eventually hold on the entire actual first
unit-trial segment, with arbitrarily small Hessian error. -/
theorem practicalRun_eventually_trial_data (P : Parameters) (hP : P.Valid n)
    (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (G : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (H : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (x₀ center : EuclideanSpace ℝ (Fin n))
    (hF : ∀ᶠ z in 𝓝 center, HasFDerivAt f (innerSL ℝ (G z)) z)
    (hG : ∀ᶠ z in 𝓝 center, HasFDerivAt G (H z) z)
    (hHC : ∀ᶠ z in 𝓝 center, ContinuousAt H z)
    (mu : ℝ) (hmu : 0 < mu) (hpositive : ∀ v, mu * ‖v‖ ^ 2 ≤ inner ℝ v (H center v))
    (hconv : Tendsto (fun k => (practicalRun P f G x₀ k).point) atTop (𝓝 center))
    (hne : ∀ k, (practicalRun P f G x₀ k).point ≠ center)
    (epsilon : ℝ) (hepsilon : 0 < epsilon) :
    ∃ K, ∀ k, K ≤ k →
      let S := practicalRun P f G x₀ k
      let u := (practicalModel P S).safeDirection S
      S.gradient ≠ 0 ∧
        (∀ t ∈ Icc (0 : ℝ) 1, HasFDerivAt f (innerSL ℝ (G (S.point + t • u))) (S.point + t • u)) ∧
        (∀ t ∈ Icc (0 : ℝ) 1, HasFDerivAt G (H (S.point + t • u)) (S.point + t • u)) ∧
        ContinuousOn (fun t : ℝ => H (S.point + t • u)) (Icc 0 1) ∧
        (∀ t ∈ Icc (0 : ℝ) 1, ‖H (S.point + t • u) - H center‖ ≤ epsilon) := by
  have hH := hHC.self_of_nhds
  have hclose : ∀ᶠ z in 𝓝 center, ‖H z - H center‖ < epsilon :=
    (hH.sub continuousAt_const).norm.eventually (gt_mem_nhds (by
      change ‖H center - H center‖ < epsilon
      simpa only [sub_self, norm_zero] using hepsilon))
  have hdata : ∀ᶠ z in 𝓝 center,
      HasFDerivAt f (innerSL ℝ (G z)) z ∧ HasFDerivAt G (H z) z ∧
        ContinuousAt H z ∧ ‖H z - H center‖ ≤ epsilon := by
    filter_upwards [hF, hG, hHC, hclose] with z hf hg hh he
    exact ⟨hf, hg, hh, he.le⟩
  obtain ⟨radius, hradius, hlocal⟩ := Metric.eventually_nhds_iff.mp hdata
  have hinit := practicalRun_initial_gradient_ne_zero P f G x₀ center hconv hne
  have hc := algorithmInitialState_constants P hP f G x₀ none hinit
  have hsig := hP.2.2.2.2.2.2.1
  have hsig₁ : P.armijo < 1 := hP.2.2.2.2.2.2.2.1.trans (by norm_num)
  obtain ⟨K, hK⟩ := run_eventually_local_new_pairs P n (practicalModel P) f G H
    (algorithmInitialState P f G x₀ none) rfl rfl hc.1 hc.2 hsig hsig₁
    center hF hG hH mu hmu hpositive hconv hne radius hradius
  refine ⟨K, ?_⟩
  intro k hk
  let S := practicalRun P f G x₀ k
  let u := (practicalModel P S).safeDirection S
  have hnear := (hK k hk).2.1
  have ha : S.point ∈ ball center radius := by
    change ‖S.point - center‖ < radius
    exact hnear.1
  have hb : S.point + u ∈ ball center radius := by
    change ‖S.point + u - center‖ < radius
    exact hnear.2
  have hsegment (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) : S.point + t • u ∈ ball center radius := by
    have h := (convex_ball center radius).segment_subset ha hb (lineMap_mem_segment ℝ S.point (S.point + u) ht)
    have he : AffineMap.lineMap S.point (S.point + u) t = S.point + t • u := by
      rw [AffineMap.lineMap_apply_module]
      module
    rwa [he] at h
  refine ⟨(hK k hk).1, fun t ht => (hlocal (hsegment t ht)).1,
    fun t ht => (hlocal (hsegment t ht)).2.1, ?_, fun t ht => (hlocal (hsegment t ht)).2.2.2⟩
  intro t ht
  have hpath : ContinuousAt (fun t : ℝ => S.point + t • u) t :=
    continuousAt_const.add (continuousAt_id.smul continuousAt_const)
  have hcomp : ContinuousAt (fun t : ℝ => H (S.point + t • u)) t :=
    (hlocal (hsegment t ht)).2.2.1.tendsto.comp hpath.tendsto
  exact hcomp.continuousWithinAt

end
end krylov.XR
