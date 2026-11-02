import krylov.XR.LocalMemory

/-!
Article: main_krylov, thm:grow and apG:local(c), actual first-trial data.
Use: obtain all Taylor hypotheses along the genuinely computed unit trial
from the local C² source and accepted convergence. Locality is derived
from the internal safeguard, including when it is still active.
Source: the true local gradient and query bounds, convexity of a ball.
-/

namespace krylov.XR
noncomputable section
open Set Metric Filter Topology
open scoped InnerProductSpace
variable {n : ℕ}

/-- Genuine local C² data eventually hold on the entire actual first
unit-trial segment, with arbitrarily small Hessian error. -/
theorem algorithmRun_eventually_trial_data (P : Parameters) (hP : P.Valid n)
    (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (G : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (H : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (x₀ center : EuclideanSpace ℝ (Fin n)) (bounds : SpectralBounds)
    (hF : ∀ᶠ z in 𝓝 center, HasFDerivAt f (innerSL ℝ (G z)) z)
    (hG : ∀ᶠ z in 𝓝 center, HasFDerivAt G (H z) z)
    (hHC : ∀ᶠ z in 𝓝 center, ContinuousAt H z)
    (mu : ℝ) (hmu : 0 < mu) (hpositive : ∀ v, mu * ‖v‖ ^ 2 ≤ inner ℝ v (H center v))
    (hconv : Tendsto (fun k => (algorithmRun P f G x₀ bounds k).point) atTop (𝓝 center))
    (hne : ∀ k, (algorithmRun P f G x₀ bounds k).point ≠ center)
    (epsilon : ℝ) (hepsilon : 0 < epsilon) :
    ∃ K, ∀ k, K ≤ k →
      let S := algorithmRun P f G x₀ bounds k
      let u := (algorithmModel P S).safeDirection S
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
  have hinit := algorithmRun_initial_gradient_ne_zero P f G x₀ center bounds hconv hne
  have hc := algorithmInitialState_constants P hP f G x₀ bounds hinit
  have hsig := hP.2.2.2.2.2.2.1
  have hsig₁ : P.armijo < 1 := hP.2.2.2.2.2.2.2.1.trans (by norm_num)
  obtain ⟨K, hK⟩ := run_eventually_local_new_pairs P n (algorithmModel P) f G H
    (algorithmInitialState P f G x₀ bounds) rfl rfl hc.1 hc.2 hsig hsig₁
    center hF hG hH mu hmu hpositive hconv hne radius hradius
  refine ⟨K, ?_⟩
  intro k hk
  let S := algorithmRun P f G x₀ bounds k
  let u := (algorithmModel P S).safeDirection S
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
