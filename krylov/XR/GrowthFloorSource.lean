import krylov.XR.LocalFloorSource
import krylov.XR.GrowthRitzSource
import krylov.XR.GrowthRitzMonotone

/-!
Article: main_krylov, thm:XR and prop:floor, original source to actual G3.
Use: derive a compact interval of real running upper estimates and all
three trial-adequacy inequalities for the literal selected-model algorithm.
No trial accuracy, inverse domain, accepted-query bound or successful
phase is assumed. Source: true G1--G2, a persistent strict upper margin,
source-derived Ritz bounds and the constructive upper-only Radau theorem.
-/
namespace krylov.XR
noncomputable section
open Matrix Set Metric Filter Topology krylov.Methods krylov.Reference
open scoped InnerProductSpace NNReal
variable {n : ℕ}
set_option maxHeartbeats 800000

/-- Original G1--G2 and one true strict running upper bound imply G3 for
all late actual partial-window directions, for either value flag. -/
theorem algorithmRun_eventually_floored_adequate (P : Parameters) (hP : P.Valid n)
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
    (b : ℝ) (hab : mu ≤ b) (hb : 0 < b) (hnorm : ‖cgOperator base‖ ≤ b)
    (hsigma₁ : sigma ≤ 1)
    (hHlo : (base-mu • 1).PosSemidef) (hHhi : (b • 1-base).PosSemidef)
    (Kstrict : ℕ) (strictBounds : ℝ × ℝ)
    (hstrictBounds : (algorithmRun P f G x₀ bounds Kstrict).bounds = some strictBounds)
    (hstrict : b < strictBounds.2) :
    ∃ trialUpper > 0, ∃ K, ∀ k, K ≤ k →
      let S := algorithmRun P f G x₀ bounds k
      let d := algorithmSelectedDirection P S
      d ≠ 0 →
      (mu/(2*(2*(1-P.armijo)-P.adequacyMargin)))*‖d‖^2 ≤ algorithmComputedCurvature P S ∧
        algorithmComputedCurvature P S ≤ trialUpper*‖d‖^2 ∧
        inner ℝ (H center d) d ≤
          (2*(1-P.armijo)-P.adequacyMargin/2)*algorithmComputedCurvature P S := by
  obtain ⟨C, hC, Kr, hR⟩ := algorithmRun_eventually_modelRitzBound P hP f G H x₀ center bounds
    hF hG hH mu sigma hmu hsigma hpositive hconv hne K₀ hgain hprobeGain
  let upper := max (boundsUpper (algorithmRun P f G x₀ bounds Kr).bounds) C
  have hupper : 0 < upper := hC.trans_le (le_max_right _ _)
  have hrunning := algorithmRun_boundsUpper_bounded P C hC.le f G x₀ bounds Kr hR
  have hmodel (k : ℕ) (hk : Kr ≤ k) :
      boundsUpper (algorithmModel P (algorithmRun P f G x₀ bounds k)).bounds ≤ upper := by
    have hh := algorithmModel_boundsUpper_le P C hC.le (algorithmRun P f G x₀ bounds k) (hR k hk).1
    exact hh.trans (max_le (hrunning k hk) (le_max_right _ _))
  have hpos : ∀ v : EuclideanSpace ℝ (Fin n), mu*‖v‖^2 ≤ inner ℝ v (cgOperator base v) := by
    rw [←hcenter]
    exact hpositive
  obtain ⟨radius, hradius, hfloor⟩ := algorithmComputedCurvature_uniform_floor_radius P hP base hbase
    mu b strictBounds.2 upper sigma hmu hab hb hstrict hsigma hsigma₁ hHlo hHhi hpos hnorm
  let e : ℝ≥0 := ⟨radius, hradius.le⟩
  obtain ⟨Ke, hE⟩ := algorithmRun_eventually_secant_errors P hP f G H x₀ center bounds
    hF hG hH mu hmu hpositive hconv hne e hradius
  obtain ⟨Kt, hT⟩ := algorithmRun_eventually_retains_window P hP f G H x₀ center bounds
    hF hG hH mu sigma hmu hsigma hpositive hconv hne K₀ hgain
  refine ⟨upper, hupper, max Kstrict (max Kr (max Ke (max Kt K₀))), ?_⟩
  intro k hk
  let S := algorithmRun P f G x₀ bounds k
  let W := (algorithmModel P S).pairs
  have hret := (hT k (by omega)).2.1
  have hg := hgain k (by omega)
  dsimp only at hg hret
  rw [←hret] at hg
  obtain ⟨c, hc, hlow⟩ := algorithmRun_model_upper_margin P f G x₀ bounds Kstrict
    strictBounds hstrictBounds k (by omega)
  have hupp : c.2 ≤ upper := by
    have hh := hmodel k (by omega)
    rw [hc] at hh
    exact hh
  have hs (i : Fin W.length) : storedSteps W i ≠ 0 := by
    have hp := algorithmRun_pairs_positive P f G x₀ bounds k (W.get i)
      (algorithmModel_pair_mem P S _ (List.get_mem _ i))
    intro hz
    change 0 < inner ℝ (storedSteps W i) (storedImages W i) at hp
    rw [hz, inner_zero_left] at hp
    exact hp.false
  have hy (i : Fin W.length) : ‖storedImages W i - cgOperator base (storedSteps W i)‖ ≤
      radius*‖storedSteps W i‖ := by
    rw [←hcenter]
    exact hE k (by omega) _ (algorithmModel_pair_mem P S _ (List.get_mem _ i))
  dsimp only
  intro hd
  have hh := hfloor S c hc hlow hupp hs hg hy hd
  dsimp only at hh ⊢
  rw [hcenter]
  exact hh

end
end krylov.XR
