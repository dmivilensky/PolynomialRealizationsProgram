import jacobi.Jacobi.FiniteStieltjes
import Mathlib.Analysis.Calculus.Deriv.MeanValue

/-!
Article: jacobi, Lemma 1.3.
The actual Bessel logarithmic derivative tends to zero on the positive
resolvent axis. The proof uses its genuine nonnegative decreasing
Stieltjes geometry and the exact modified Bessel equation, without a
prior asymptotic expansion, product identity or first Rayleigh sum.
Source: the elementary Riccati restoring argument and the real mean value theorem.
Use: monotonicity then gives its full decay, excluding an escaped finite first trace.
-/
namespace jacobi.Bessel
noncomputable section
open Set Filter Real
open scoped Topology
set_option backward.isDefEq.respectTransparency false

/-- The actual Bessel Stieltjes function becomes smaller than every positive threshold somewhere on the nonnegative axis.
Use: monotonicity then gives its full decay, excluding an escaped finite first trace.
Article: jacobi, Lemma 1.3.
Proof: if R stayed at least epsilon, its genuine Riccati equation
would force R'<=-epsilon^2/2 after a finite explicit radius. The mean
value theorem would then force the actual nonnegative R below zero. -/
theorem stieltjes_small_value {a ε : ℝ} (ha : -1<a) (hε : 0<ε) :
    ∃ T:ℝ,0≤T ∧ stieltjes a T<ε := by
  -- The contradiction uses only the already proved actual Bessel equation and positive finite-resolvent limit.
  by_contra hn
  have hbound : ∀ s:ℝ,0≤s → ε≤stieltjes a s := by
    intro s hs
    exact not_lt.mp (fun hlt => hn ⟨s,hs,hlt⟩)
  let T := max 1 (1/ε^2)
  have hTpos : 0<T := lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  have hderiv : ∀ s∈Ici T,stieltjesSlope a s≤ -(ε^2)/2 := by
    intro s hs
    have hspos : 0<s := hTpos.trans_le hs
    have hscale : 1≤s*ε^2 := (div_le_iff₀ (sq_pos_of_pos hε)).mp ((le_max_right _ _).trans hs)
    have hR := stieltjes_nonneg ha hspos.le
    have hRsq := pow_le_pow_left₀ hε.le (hbound s hspos.le) 2
    have hterm : 0≤2*(a+1)*stieltjes a s := mul_nonneg (by linarith) hR
    have he := stieltjes_equation ha hspos.le
    have hscaled := mul_le_mul_of_nonneg_left hRsq (show 0≤2*s by positivity)
    nlinarith
  have hcont : ContinuousOn (stieltjes a) (Ici T) :=
    fun s hs => (stieltjes_hasDerivAt ha (hTpos.le.trans hs)).continuousAt.continuousWithinAt
  have hdiff : DifferentiableOn ℝ (stieltjes a) (interior (Ici T)) :=
    fun s hs => (stieltjes_hasDerivAt ha (hTpos.le.trans (interior_subset hs))).differentiableAt.differentiableWithinAt
  let Y := T+2*(stieltjes a T+1)/ε^2
  have hTY : T≤Y := by
    dsimp [Y]
    linarith [div_pos (show 0<2*(stieltjes a T+1) by linarith [stieltjes_nonneg ha hTpos.le])
      (sq_pos_of_pos hε)]
  have h := (convex_Ici T).image_sub_le_mul_sub_of_deriv_le hcont hdiff
    (C := -(ε^2)/2) (by
      intro s hs
      rw [(stieltjes_hasDerivAt ha (hTpos.le.trans (interior_subset hs))).deriv]
      exact hderiv s (interior_subset hs)) T (by simp) Y hTY hTY
  have he : (-(ε^2)/2)*(Y-T)= -(stieltjes a T+1) := by
    dsimp [Y]
    field_simp [hε.ne']
    ring
  rw [he] at h
  linarith [stieltjes_nonneg ha (hTpos.le.trans hTY)]

/-- The actual Bessel Stieltjes transform tends to zero as the positive resolvent parameter tends to infinity.
Use: discharges the no-loss-of-mass step in the exact first Rayleigh sum and the canonical product.
Article: jacobi, Lemma 1.3.
Proof: for every epsilon the preceding genuine Riccati argument gives
one value below epsilon. The actual Stieltjes function is nonnegative
and decreasing, so every later value has the same bound. -/
theorem stieltjes_tendsto_zero {a : ℝ} (ha : -1<a) :
    Tendsto (stieltjes a) atTop (𝓝 0) := by
  -- Actual monotonicity turns each proved small value into a uniform tail bound.
  apply Metric.tendsto_atTop.mpr
  intro ε hε
  obtain ⟨T,hT,hsmall⟩ := stieltjes_small_value ha hε
  refine ⟨T,fun s hs => ?_⟩
  rw [Real.dist_eq,sub_zero,abs_of_nonneg (stieltjes_nonneg ha (hT.trans hs))]
  exact ((stieltjes_antitone ha) hT (hT.trans hs) hs).trans_lt hsmall

end
end jacobi.Bessel
