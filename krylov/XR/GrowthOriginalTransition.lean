import krylov.XR.GrowthOriginalFloor
import krylov.XR.GrowthUpperMargin

/-!
Article: main_krylov, thm:XR and cor:xrF, original actual-floor transition.
Use: expose the real source-dependent G4 constants and conclude the
literal accepted-phase/capacity transition from the paper's actual running
ModelStep upper margin. This also supplies the genuine growth certificate
used by the independently proved native SS1/SS1-F rate dictionaries.
-/
namespace krylov.XR
noncomputable section
open Matrix Set Metric Filter Topology krylov.Methods krylov.Reference
open scoped InnerProductSpace NNReal
variable {n : ℕ}
set_option maxHeartbeats 800000

/-- Original G1--G2, the actual running upper margin, and strict numeric
G4 imply the genuine unit-step maximal-window phase for both F flags.
Every G3 inequality and every successful algorithm branch is derived. -/
theorem algorithmRun_original_floor_transition (P : Parameters) (hP : P.Valid n)
    (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (G : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (H : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (x₀ center : EuclideanSpace ℝ (Fin n)) (bounds : SpectralBounds)
    (hF : ∀ᶠ z in 𝓝 center, HasFDerivAt f (innerSL ℝ (G z)) z)
    (hG : ∀ᶠ z in 𝓝 center, HasFDerivAt G (H z) z)
    (mu sigma : ℝ) (hmu : 0 < mu) (hsigma : 0 < sigma)
    (hpositive : ∀ v, mu * ‖v‖ ^ 2 ≤ inner ℝ v (H center v))
    (hconv : Tendsto (fun k => (algorithmRun P f G x₀ bounds k).point) atTop (𝓝 center))
    (hne : ∀ k, (algorithmRun P f G x₀ bounds k).point ≠ center)
    (K₀ : ℕ)
    (hgain : ∀ k, K₀ ≤ k →
      let W := incomingWindow (algorithmRun P f G x₀ bounds k)
      ∀ w : Fin W.length → ℝ, sigma ^ 2 * ‖WithLp.toLp 2 w‖ ^ 2 ≤
        ‖combine (krylov.Convergence.unitWindow (storedSteps W)) w‖ ^ 2)
    (hprobeGain : ∀ k, K₀ ≤ k →
      let S := algorithmRun P f G x₀ bounds k
      ¬Accepted f P.armijo S.point S.gradient ((algorithmModel P S).safeDirection S) 1 →
      let W := incomingWindow (firstProbeState (algorithmModel P) f G S)
      ∀ w : Fin W.length → ℝ, sigma ^ 2 * ‖WithLp.toLp 2 w‖ ^ 2 ≤
        ‖combine (krylov.Convergence.unitWindow (storedSteps W)) w‖ ^ 2)
    (base : Matrix (Fin n) (Fin n) ℝ) (hbase : base.PosDef) (hcenter : H center = cgOperator base)
    (radius : ℝ) (hradius : 0 < radius) (L : ℝ≥0)
    (hLip : LipschitzOnWith L H (ball center radius))
    (hupperMargin : ∃ k, ‖H center‖ <
      boundsUpper (algorithmModel P (algorithmRun P f G x₀ bounds k)).bounds) :
    ∃ a > 0, ∃ gain > 0, ∃ b > 0, ∃ ell > 0, ∃ trialUpper > 0,
      ((algorithmInitialState P f G x₀ bounds).descentConstant <
        dimensionDescentConstant n a gain b trialUpper) →
      (dimensionNormConstant n a gain b ell <
        (algorithmInitialState P f G x₀ bounds).normConstant) →
      Nonempty (SelectedGrowthSource P f G H x₀ center bounds) ∧
      ∃ K, ∀ k, K ≤ k →
        let S := algorithmRun P f G x₀ bounds k
        S.capacity = P.maximumCapacity ∧
          (algorithmModel P S).pairs.length = P.maximumCapacity ∧
          (algorithmModel P S).deletedByTest = 0 ∧
          (algorithmModel P S).safeDirection S = (algorithmModel P S).direction ∧
          Accepted f P.armijo S.point S.gradient ((algorithmModel P S).safeDirection S) 1 := by
  obtain ⟨k, hk⟩ := hupperMargin
  obtain ⟨cache, hcache, hmargin⟩ := algorithmRun_cache_upper_margin P f G x₀ center bounds
    hconv hne ‖H center‖ (norm_nonneg _) k hk
  obtain ⟨trialUpper, htrialUpper, hsource⟩ := selectedGrowthSource_from_original_floor P hP
    f G H x₀ center bounds hF hG mu sigma hmu hsigma hpositive hconv hne K₀ hgain hprobeGain
    base hbase hcenter radius hradius L hLip (k+1) cache hcache hmargin
  let b := (‖H center‖+cache.2)/2
  let a := min mu b
  let gain := min sigma 1
  let ell := a/(2*(2*(1-P.armijo)-P.adequacyMargin))
  have hb : 0 < b := by dsimp only [b]; nlinarith [norm_nonneg (H center)]
  have ha : 0 < a := lt_min hmu hb
  have hgain : 0 < gain := lt_min hsigma (by norm_num)
  have hell : 0 < ell := by
    have hh := hP.2.2.2.2.2.2.2.2.2.2.2
    have hA : 0 < 2*(1-P.armijo)-P.adequacyMargin := by linarith
    exact div_pos ha (mul_pos (by norm_num) hA)
  refine ⟨a, ha, gain, hgain, b, hb, ell, hell, trialUpper, htrialUpper, ?_⟩
  intro hG₄₁ hG₄₂
  obtain ⟨D⟩ := hsource hG₄₁ hG₄₂
  exact ⟨⟨D⟩, D.eventually_maximum_window hP⟩

end
end krylov.XR
