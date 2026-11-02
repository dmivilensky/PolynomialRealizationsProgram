import krylov.XR.LocalRetention

/-!
Article: main_krylov, G1--G2 and thm:grow with m0=n.
Use: treat the second ModelStep only when the first true trial was rejected.
Its newly observed probe and all old retained pairs have genuine small
relative Hessian errors; positivity is the actual append guard invariant.
Source: local safeguarded query bounds and true gradient secants.
-/

namespace krylov.XR
noncomputable section
open Set Metric Filter Topology krylov.Methods
open scoped InnerProductSpace NNReal
variable {n : ℕ}

/-- Every pair of the actual unchanged-anchor probe state is positive,
independently of whether the new probe passes its insertion guard. -/
theorem firstProbeState_positive (P : Parameters)
    (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (G : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (S : State (EuclideanSpace ℝ (Fin n))) (hS : ∀ a ∈ S.pairs, positivePair a) :
    ∀ a ∈ (firstProbeState (algorithmModel P) f G S).pairs, positivePair a := by
  exact appendPositive_positive _ _ (fun a ha => hS a (algorithmModel_pair_mem P S a ha))

/-- All observations of the actual probe state eventually approximate the
limiting Hessian relatively, without a probe-query localization premise. -/
theorem algorithmRun_eventually_probe_secant_errors (P : Parameters) (hP : P.Valid n)
    (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (G : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (H : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (x₀ center : EuclideanSpace ℝ (Fin n)) (bounds : SpectralBounds)
    (hF : ∀ᶠ z in 𝓝 center, HasFDerivAt f (innerSL ℝ (G z)) z)
    (hG : ∀ᶠ z in 𝓝 center, HasFDerivAt G (H z) z) (hH : ContinuousAt H center)
    (mu : ℝ) (hmu : 0 < mu) (hpositive : ∀ v, mu * ‖v‖ ^ 2 ≤ inner ℝ v (H center v))
    (hconv : Tendsto (fun k => (algorithmRun P f G x₀ bounds k).point) atTop (𝓝 center))
    (hne : ∀ k, (algorithmRun P f G x₀ bounds k).point ≠ center)
    (epsilon : ℝ≥0) (hepsilon : 0 < (epsilon : ℝ)) :
    ∃ K, ∀ k, K ≤ k →
      ∀ a ∈ (firstProbeState (algorithmModel P) f G (algorithmRun P f G x₀ bounds k)).pairs,
        ‖a.image - H center a.step‖ ≤ (epsilon : ℝ) * ‖a.step‖ := by
  have hclose : ∀ᶠ z in 𝓝 center, ‖H z - H center‖ < (epsilon : ℝ) :=
    (hH.sub continuousAt_const).norm.eventually (gt_mem_nhds (by
      change ‖H center - H center‖ < (epsilon : ℝ)
      simpa only [sub_self, norm_zero] using hepsilon))
  have hdata : ∀ᶠ z in 𝓝 center, HasFDerivAt G (H z) z ∧ ‖H z - H center‖ ≤ (epsilon : ℝ) := by
    filter_upwards [hG, hclose] with z hg hh
    exact ⟨hg, hh.le⟩
  obtain ⟨radius, hradius, hlocal⟩ := Metric.eventually_nhds_iff.mp hdata
  obtain ⟨K₁, hK₁⟩ := algorithmRun_eventually_secant_errors P hP f G H x₀ center bounds
    hF hG hH mu hmu hpositive hconv hne epsilon hepsilon
  have hinit := algorithmRun_initial_gradient_ne_zero P f G x₀ center bounds hconv hne
  have hc := algorithmInitialState_constants P hP f G x₀ bounds hinit
  obtain ⟨K₂, hK₂⟩ := run_eventually_local_new_pairs P n (algorithmModel P) f G H
    (algorithmInitialState P f G x₀ bounds) rfl rfl hc.1 hc.2 hP.2.2.2.2.2.2.1
    (hP.2.2.2.2.2.2.2.1.trans (by norm_num)) center hF hG hH mu hmu hpositive hconv hne radius hradius
  refine ⟨max K₁ K₂, ?_⟩
  intro k hk
  let S := algorithmRun P f G x₀ bounds k
  let M := algorithmModel P S
  let u := M.safeDirection S
  have hnear := (hK₂ k (by omega)).2.1
  have herr := local_secant_error G H (H center) center radius epsilon
    (fun z hz => (hlocal hz).1) (fun z hz => (hlocal hz).2) S.point (S.point + u)
    (by change ‖S.point - center‖ < radius; exact hnear.1)
    (by change ‖S.point + u - center‖ < radius; exact hnear.2)
  have hcache := run_cache_constants P n (algorithmModel P) f G
    (algorithmInitialState P f G x₀ bounds) rfl rfl k
  have hnew : ‖(observedTrialPair f G S u).image - H center (observedTrialPair f G S u).step‖ ≤
      (epsilon : ℝ) * ‖(observedTrialPair f G S u).step‖ := by
    change ‖G (S.point + u) - S.gradient - H center u‖ ≤ (epsilon : ℝ) * ‖u‖
    rw [show S.gradient = G S.point from hcache.2.1]
    simpa only [add_sub_cancel_left] using herr
  exact appendPositive_all _ _ (fun a => ‖a.image - H center a.step‖ ≤ (epsilon : ℝ) * ‖a.step‖)
    (fun a ha => hK₁ k (by omega) a (algorithmModel_pair_mem P S a ha)) hnew

/-- Original G2 at the actually visited second ModelStep forces its full
incoming-window retention too; no adequacy assumption is needed. -/
theorem algorithmRun_eventually_probe_retains_window (P : Parameters) (hP : P.Valid n)
    (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (G : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (H : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (x₀ center : EuclideanSpace ℝ (Fin n)) (bounds : SpectralBounds)
    (hF : ∀ᶠ z in 𝓝 center, HasFDerivAt f (innerSL ℝ (G z)) z)
    (hG : ∀ᶠ z in 𝓝 center, HasFDerivAt G (H z) z) (hH : ContinuousAt H center)
    (mu sigma : ℝ) (hmu : 0 < mu) (hsigma : 0 < sigma)
    (hpositive : ∀ v, mu * ‖v‖ ^ 2 ≤ inner ℝ v (H center v))
    (hconv : Tendsto (fun k => (algorithmRun P f G x₀ bounds k).point) atTop (𝓝 center))
    (hne : ∀ k, (algorithmRun P f G x₀ bounds k).point ≠ center)
    (K₀ : ℕ)
    (hgain : ∀ k, K₀ ≤ k →
      let S := algorithmRun P f G x₀ bounds k
      ¬Accepted f P.armijo S.point S.gradient ((algorithmModel P S).safeDirection S) 1 →
      let W := incomingWindow (firstProbeState (algorithmModel P) f G S)
      ∀ w : Fin W.length → ℝ, sigma ^ 2 * ‖WithLp.toLp 2 w‖ ^ 2 ≤
        ‖combine (krylov.Convergence.unitWindow (storedSteps W)) w‖ ^ 2) :
    ∃ K, ∀ k, K ≤ k →
      let S := algorithmRun P f G x₀ bounds k
      ¬Accepted f P.armijo S.point S.gradient ((algorithmModel P S).safeDirection S) 1 →
      let S₁ := firstProbeState (algorithmModel P) f G S
      rankDeletion (incomingWindow S₁) = 0 ∧
        (algorithmModel P S₁).pairs = incomingWindow S₁ ∧
        (algorithmModel P S₁).pairsBeforeTest = (incomingWindow S₁).length ∧
        (algorithmModel P S₁).deletedByTest = 0 := by
  have htheta : 0 < P.windowThreshold := hP.2.2.2.2.2.1
  have hcoerc : 0 < localCoercivity mu sigma := by unfold localCoercivity; positivity
  let epsilon : ℝ := min (mu * sigma ^ 2 / (8 * ((n : ℝ) + 1)))
    (P.windowThreshold * localCoercivity mu sigma / (4 * ((n : ℝ) + 1)))
  have hepsilon : 0 < epsilon := by dsimp only [epsilon]; positivity
  let e : ℝ≥0 := ⟨epsilon, hepsilon.le⟩
  have hsmall : (n : ℝ) * epsilon ≤ mu * sigma ^ 2 / 4 := by
    have h := (le_div_iff₀ (by positivity : 0 < 8 * ((n : ℝ) + 1))).mp
      (min_le_left (mu * sigma ^ 2 / (8 * ((n : ℝ) + 1)))
        (P.windowThreshold * localCoercivity mu sigma / (4 * ((n : ℝ) + 1))))
    change epsilon * (8 * ((n : ℝ) + 1)) ≤ _ at h
    nlinarith
  have hgate : 2 * (n : ℝ) * epsilon / localCoercivity mu sigma < P.windowThreshold := by
    have h := (le_div_iff₀ (by positivity : 0 < 4 * ((n : ℝ) + 1))).mp
      (min_le_right (mu * sigma ^ 2 / (8 * ((n : ℝ) + 1)))
        (P.windowThreshold * localCoercivity mu sigma / (4 * ((n : ℝ) + 1))))
    change epsilon * (4 * ((n : ℝ) + 1)) ≤ _ at h
    apply (div_lt_iff₀ hcoerc).2
    nlinarith [mul_pos htheta hcoerc]
  have hsym := local_hessian_symmetric f G H center hF hG.self_of_nhds
  obtain ⟨K₁, hK₁⟩ := algorithmRun_eventually_probe_secant_errors P hP f G H x₀ center bounds
    hF hG hH mu hmu hpositive hconv hne e hepsilon
  refine ⟨max K₀ K₁, ?_⟩
  intro k hk
  dsimp only
  intro hreject
  let S := algorithmRun P f G x₀ bounds k
  let S₁ := firstProbeState (algorithmModel P) f G S
  have hlen : (incomingWindow S₁).length ≤ n := by
    simp only [incomingWindow, retainNewest_length]
    omega
  have hlenR : ((incomingWindow S₁).length : ℝ) ≤ n := by exact_mod_cast hlen
  have hy i : ‖storedImages (incomingWindow S₁) i - H center (storedSteps (incomingWindow S₁) i)‖ ≤
      epsilon * ‖storedSteps (incomingWindow S₁) i‖ :=
    hK₁ k (by omega) _ (List.mem_of_mem_drop (List.get_mem _ i))
  exact algorithmModel_local_retention P htheta S₁
    (firstProbeState_positive P f G S (algorithmRun_pairs_positive P f G x₀ bounds k))
    (H center) hsym mu sigma epsilon hmu hsigma hepsilon.le hpositive (hgain k (by omega) hreject) hy
    ((mul_le_mul_of_nonneg_right hlenR hepsilon.le).trans hsmall)
    ((div_le_div_of_nonneg_right (by nlinarith [mul_le_mul_of_nonneg_right hlenR hepsilon.le])
      hcoerc.le).trans_lt hgate)

end
end krylov.XR
