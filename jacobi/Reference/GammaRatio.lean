import jacobi.Reference.BetaIntegral

/-!
Article: jacobi, Lemma C.1.
Euler's genuine Gamma limit, already proved in mathlib, evaluates the
normalized Gamma ratios needed by the reference norms. This avoids a
separate Stirling theorem or an assumed asymptotic coefficient formula.
Use: identifies the genuine Euler Gamma sequence with the original reference norm Gamma quotient.
-/
namespace jacobi.Reference
noncomputable section
open Real Filter
open scoped Topology
set_option backward.isDefEq.respectTransparency false

/-- The actual real Gamma recurrence evaluates every positive finite rising product.
Use: identifies the genuine Euler Gamma sequence with the original reference norm Gamma quotient.
Article: jacobi, Lemma C.1.
Source: Euler's Gamma recurrence, Real.Gamma_add_one.
Proof: induct on the original product length and apply the true positive-argument Gamma recurrence at each next factor. -/
theorem gamma_product {s : ℝ} (hs : 0<s) (n : ℕ) :
    Real.Gamma (s+n)=Real.Gamma s*∏ j∈Finset.range n,(s+j) := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hp : s+(n:ℝ)≠0 := ne_of_gt (by linarith [Nat.cast_nonneg (α := ℝ) n])
    rw [Nat.cast_add,Nat.cast_one,← add_assoc,Real.Gamma_add_one hp,ih,Finset.prod_range_succ]
    ring

/-- The actual Euler Gamma sequence gives exactly the source Gamma quotient at every positive original degree.
Use: derives the true reference norm power law from the proved community Gamma limit.
Article: jacobi, Theorem 5.1.
Proof: the actual Gamma product evaluates the denominator of the genuine Euler sequence. The Gamma recurrence shifts its final factor and the actual factorial is Gamma(n+1). -/
theorem gammaSeq_ratio {s : ℝ} (hs : 0<s) (n : ℕ) :
    Real.GammaSeq s n=Real.Gamma s*(n:ℝ)^s*Real.Gamma ((n:ℝ)+1)/
      (((n:ℝ)+s)*Real.Gamma ((n:ℝ)+s)) := by
  -- All denominator factors are strictly positive actual Gamma values or positive rising factors.
  have hG := gamma_product hs (n+1)
  rw [Nat.cast_add,Nat.cast_one,← add_assoc,Real.Gamma_add_one (show s+(n:ℝ)≠0 by
    exact ne_of_gt (by linarith [Nat.cast_nonneg (α := ℝ) n]))] at hG
  have hprod : (∏ j∈Finset.range (n+1),(s+(j:ℝ)))≠0 := by
    exact ne_of_gt (Finset.prod_pos (fun j _ => by linarith [Nat.cast_nonneg (α := ℝ) j]))
  rw [Real.GammaSeq,Real.Gamma_nat_eq_factorial,add_comm (n:ℝ) s]
  field_simp [hprod,(Real.Gamma_pos_of_pos hs).ne',
    (Real.Gamma_pos_of_pos (show 0<s+(n:ℝ) by linarith [Nat.cast_nonneg (α := ℝ) n])).ne',
    show s+(n:ℝ)≠0 by exact ne_of_gt (by linarith [Nat.cast_nonneg (α := ℝ) n])]
  linear_combination (n:ℝ)^s*hG

/-- The elementary true affine natural-degree ratio tends to one for arbitrary fixed real shifts.
Use: evaluates the exact Gamma-sequence expression for the original reference norm asymptotic.
Article: jacobi, Lemma C.1.
Proof: specialize the community affine-ratio limit with both leading coefficients equal to one. -/
theorem shifted_nat_ratio (s t : ℝ) : Tendsto (fun n : ℕ => ((n:ℝ)+s)/((n:ℝ)+t)) atTop (𝓝 1) := by
  simpa only [one_mul,div_one,add_comm] using
    (tendsto_add_mul_div_add_mul_atTop_nhds s t (1:ℝ) one_ne_zero)

/-- The actual positive-index Gamma quotient has its exact normalized power-law limit.
Use: supplies the original reference norm asymptotic, with its leading constant and no separate Stirling assumption.
Article: jacobi, Lemma C.1.
Proof: the true normalized quotient is the Euler Gamma sequence divided
by Gamma(s), times an affine degree ratio. Euler's proved Gamma limit
and the elementary affine ratio give the limit one. -/
theorem gamma_ratio_limit {s : ℝ} (hs : 0<s) :
    Tendsto (fun n : ℕ => (n:ℝ)^s*Real.Gamma ((n:ℝ)+1)/
      (((n:ℝ)+s)*Real.Gamma ((n:ℝ)+s))) atTop (𝓝 1) := by
  have h := (Real.GammaSeq_tendsto_Gamma s).div_const (Real.Gamma s)
  rw [div_self (Real.Gamma_pos_of_pos hs).ne'] at h
  convert h using 1
  funext n
  rw [gammaSeq_ratio hs]
  field_simp [(Real.Gamma_pos_of_pos hs).ne']

end
end jacobi.Reference
