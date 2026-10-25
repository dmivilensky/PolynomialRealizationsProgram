import polyak.Spectral.CompactDual

/-!
Article: Appendix A, strict endpoint sign of the limiting dual symbol.
Use: one uniform negative endpoint bound survives arbitrary lag supports and limits.
Proof: exact radial factorization and positivity of the hyperbolic denominator.
-/

namespace polyak.Spectral
noncomputable section
open Set
open scoped Topology OnePoint

/-- Article: positive uniform lower bound on the normalized symmetric lag at an endpoint. -/
theorem normalized_radial_ratio_ge {s x : ℝ} (hs : 0 < s) (hx : x ≤ 1) (n : ℕ) :
    (1-Real.exp (-s))/(1+Real.exp (-s)) ≤
      (Real.cosh ((n+1 : ℕ)*s)-x)/Real.sinh ((n+1 : ℕ)*s) := by
  let a := lagRadial s n
  let b := Real.exp (-s)
  obtain ⟨ha,hab,hb⟩ := lagRadial_bounds hs n
  have hap : 0 < a := ha
  have hbp : 0 < b := Real.exp_pos _
  have ha1 : a ≤ 1 := hab.trans hb.le
  have hsp : 0 < Real.sinh ((n+1 : ℕ)*s) := Real.sinh_pos_iff.mpr (by positivity)
  have hh := lagRadial_hyperbolic s n
  have he : ((Real.cosh ((n+1 : ℕ)*s)-x)*(1+b)-(1-b)*Real.sinh ((n+1 : ℕ)*s))*(2*a) =
      (1-a)*2*(b-a)+2*a*(1+b)*(1-x) := by
    calc
      _ = (2*a*Real.cosh ((n+1 : ℕ)*s))*(1+b)-2*a*x*(1+b)-
          (1-b)*(2*a*Real.sinh ((n+1 : ℕ)*s)) := by ring
      _ = _ := by rw [hh.1,hh.2]; ring
  have hn : 0 ≤ (1-a)*2*(b-a)+2*a*(1+b)*(1-x) := by
    exact add_nonneg (by positivity) (by positivity)
  have hmul : (1-b)*Real.sinh ((n+1 : ℕ)*s) ≤ (Real.cosh ((n+1 : ℕ)*s)-x)*(1+b) := by
    nlinarith
  apply (le_div_iff₀ hsp).mpr
  calc
    _ = ((1-b)*Real.sinh ((n+1 : ℕ)*s))/(1+b) := by ring
    _ ≤ _ := (div_le_iff₀ (show 0 < 1+b by positivity)).mpr hmul

/-- Article: every normalized finite lag has the same strict endpoint bound. -/
theorem complexLag_endpoint_le (u s δ ω : ℝ) (hs : 0 < s)
    (hω : ω=0 ∨ ω=Real.pi) (n : ℕ) :
    (complexLag u s δ n (ω : ℂ)).re ≤
      -u^2*((1-Real.exp (-s))/(1+Real.exp (-s))) := by
  have hr := normalized_radial_ratio_ge hs (Real.cos_le_one ((n+1 : ℕ)*ω)) n
  have he : (complexLag u s δ n (ω : ℂ)).re =
      -u^2*((Real.cosh ((n+1 : ℕ)*s)-Real.cos ((n+1 : ℕ)*ω))/Real.sinh ((n+1 : ℕ)*s)) := by
    rw [complexLag_real u s δ ω n hs]
    rcases hω with rfl | rfl <;> simp only [Complex.ofReal_re,Real.cos_zero,Real.sin_zero,
      Real.cos_pi,Real.sin_pi,one_pow,neg_sq,mul_zero,zero_mul,sub_zero]
    all_goals ring
  rw [he]
  exact mul_le_mul_of_nonpos_left hr (neg_nonpos.mpr (sq_nonneg _))

/-- Article: uniform strict endpoint negativity for every compact convex limiting dual. -/
theorem dualHull_endpoint_le {s : ℝ} (hs : 0 < s) (u ω : ℝ) (hω : ω=0 ∨ ω=Real.pi)
    (z : lagWindow s) (hz : (z : ℂ)=(ω : ℂ)) {d : DualCoefficient s} (hd : d ∈ dualHull s hs) :
    (evaluateDual u d z).re ≤ -u^2*((1-Real.exp (-s))/(1+Real.exp (-s))) := by
  apply dualHull_le (dualTraceCLM u z) _ ?_ hd
  have hfamily (δ : ℝ) (hδ : |δ| ≤ 1) (l : OnePoint ℕ) :
      (evaluateDual u (coefficientFamily s δ hs hδ l) z).re ≤
        -u^2*((1-Real.exp (-s))/(1+Real.exp (-s))) := by
    induction l using OnePoint.rec with
    | coe n =>
      rw [evaluateDual_coefficient_coe]
      change (complexLag u s δ n z).re ≤ _
      rw [hz]
      exact complexLag_endpoint_le u s δ ω hs hω n
    | infty =>
      rw [evaluateDual_coefficient_infty]
      change (complexGap u z).re ≤ _
      rw [hz]
      have hb := (lagRadial_bounds hs 0).2.2
      have hbp := Real.exp_pos (-s)
      have hd1 : (1-Real.exp (-s))/(1+Real.exp (-s)) ≤ 1 := by
        apply (div_le_one (by positivity)).mpr
        linarith
      have he : (complexGap u (ω : ℂ)).re = -u^2 := by
        rcases hω with rfl | rfl <;>
          simp [complexGap,← Complex.ofReal_cos,← Complex.ofReal_pow]
      rw [he]
      nlinarith [mul_le_mul_of_nonpos_left hd1 (neg_nonpos.mpr (sq_nonneg u))]
  intro g hg
  rcases hg with ⟨l,rfl⟩ | ⟨l,rfl⟩
  · exact hfamily 1 (by norm_num) l
  · exact hfamily (-1) (by norm_num) l

end
end polyak.Spectral
