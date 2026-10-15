import «2610.05164v2».Filters.NonlinearEnergy

/-!
Article: 2610.05164v2, Proposition 3.
Every Volterra iterate only sees the density on the left half-line.
Result: `«2610.05164v2».Filters.nonlinear_causal` supplies the stated article conclusion.
-/
namespace «2610.05164v2».Filters
noncomputable section
open Set MeasureTheory Real Filter
set_option backward.isDefEq.respectTransparency false

/--
Every Volterra iterate only sees the density on the left half-line.

Exact identity `volterraTerm s m n x=volterraTerm s j n x`.

Use: `«2610.05164v2».Filters.jost_causal` uses this identity to establish the identity `jost
s m x=jost s j x`.

Article: 2610.05164v2, Proposition 3 via `«2610.05164v2».Filters.nonlinear_causal`.

Proof: Induct on `n` while keeping `x` arbitrary; the recursive step uses the
previous-stage assertion. Intersect the eventual or almost-everywhere hypotheses, then prove
the asserted relation at an arbitrary point in that intersection. Identify the
summands/integrands on their required domain before replacing the sum or integral.
-/
theorem volterraTerm_causal {m j : ℝ → ℝ} (s : ℝ) (n : ℕ) (x : ℝ)
    (he : ∀ t ≤ x, m t=j t) : volterraTerm s m n x=volterraTerm s j n x := by
  -- Induct on `n` while keeping `x` arbitrary; the recursive step uses the previous-stage
  -- assertion.
  induction n generalizing x with
  | zero => rfl
  | succ n ih =>
    have hmf : (fun t => m t*volterraTerm s m n t) =ᵐ[volume.restrict (Iic x)]
        (fun t => j t*volterraTerm s j n t) := by
      filter_upwards [ae_restrict_mem measurableSet_Iic] with t ht
      rw [he t ht,ih t (fun y hy => he y (hy.trans ht))]
    change s/2*(cumulative (fun t => m t*volterraTerm s m n t) x-
      causal 2 (fun t => m t*volterraTerm s m n t) x)=_
    unfold cumulative causal
    rw [integral_congr_ae hmf,integral_congr_ae (hmf.mono (fun t ht => congrArg (fun z => exp (2*t)*z) ht))]
    rfl

/--
Exact identity `jost s m x=jost s j x`.

Use: `«2610.05164v2».Filters.nonlinear_causal` rewrites with this identity to establish exact
identity `nonlinear s m x=nonlinear s j x`.

Article: 2610.05164v2, Proposition 3 via `«2610.05164v2».Filters.nonlinear_causal`.

Proof: Identify the summands/integrands on their required domain before replacing the sum or
integral.
-/
theorem jost_causal {m j : ℝ → ℝ} (s x : ℝ) (he : ∀ t ≤ x, m t=j t) :
    jost s m x=jost s j x := tsum_congr (fun n => volterraTerm_causal s n x he)

/--
Exact identity `nonlinear s m x=nonlinear s j x`.

Use: the ordered `Article` showcase checks this article-facing formulation directly.

Article: 2610.05164v2, Proposition 3.

Proof: Intersect the eventual or almost-everywhere hypotheses, then prove the asserted relation
at an arbitrary point in that intersection. Identify the summands/integrands on their required
domain before replacing the sum or integral.
-/
theorem nonlinear_causal {m j : ℝ → ℝ} (s x : ℝ) (he : ∀ t ≤ x, m t=j t) :
    nonlinear s m x=nonlinear s j x := by
  have hmf : (fun t => exp (2*t)*(m t*jost s m t)) =ᵐ[volume.restrict (Iic x)]
      (fun t => exp (2*t)*(j t*jost s j t)) := by
    filter_upwards [ae_restrict_mem measurableSet_Iic] with t ht
    rw [he t ht,jost_causal s t (fun y hy => he y (hy.trans ht))]
  unfold nonlinear jostSlope causal
  rw [jost_causal s x he,integral_congr_ae hmf]

/--
The stated quantitative bound `TendstoUniformly (fun N : ℕ => fun x => ∑ n ∈ Finset.range N,
volterraTerm s m n x) (jost s m) atTop`.

Use: a standalone supporting limit for the article chain below; no retained declaration
currently has an explicit proof dependency on it.

Article: 2610.05164v2, Proposition 3.

Proof: Use the identities/estimates `«2610.05164v2».Filters.factorialBound_hasSum`,
`«2610.05164v2».Filters.volterraTerm_global_bound` with the arguments shown in the proof.
-/
theorem jost_uniform_convergence {m : ℝ → ℝ} (hm : Integrable m) (hn : ∀ t, 0 ≤ m t)
    {s : ℝ} (hs : 0 ≤ s) :
    TendstoUniformly (fun N : ℕ => fun x => ∑ n ∈ Finset.range N, volterraTerm s m n x)
      (jost s m) atTop :=
  tendstoUniformly_tsum_nat (factorialBound_hasSum s (∫ t, m t)).summable
    (volterraTerm_global_bound hm hn hs)

end
end «2610.05164v2».Filters
