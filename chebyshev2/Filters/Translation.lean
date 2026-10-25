import chebyshev2.Filters.SpectralObservations
import chebyshev2.Filters.VolterraUniqueness

/-!
Article: chebyshev2, Lemma 14.
Translation covariance of the actual causal and Jost filters.
Use: `chebyshev2.Filters.nonlinear_translate` feeds
`chebyshev2.Comparison.symmetric_logDeterminant_at` (symmetric log Determinant at).
Proof chain: `chebyshev2.Comparison.symmetric_logDeterminant_support_at` — chebyshev2, Lemma
14; Symmetric spectral observations with exact support/boundary terms.
-/
namespace chebyshev2.Filters
noncomputable section
open Set MeasureTheory Filter Real
set_option backward.isDefEq.respectTransparency false

/--
A change of variables on the full half-line, with no integrability premise needed for the
equality of totalized Bochner integrals.

Exact identity `(∫ t in Iic x, f (t+c))=∫ t in Iic (x+c), f t`.

Use: `chebyshev2.Filters.causal_translate` uses this identity to establish the identity
`causal a (fun t => m (t+c)) x=causal a m (x+c)`.

Article: chebyshev2, Lemma 14 via
`chebyshev2.Comparison.symmetric_logDeterminant_support_at`.

Proof: Separate `t ≤ x` from its negation; prove the goal under each of these mutually
exclusive hypotheses. Prove equality of functions by evaluating both sides at an arbitrary
argument.
-/
theorem integral_Iic_translate (f : ℝ → ℝ) (c x : ℝ) :
    (∫ t in Iic x, f (t+c))=∫ t in Iic (x+c), f t := by
  -- Separate `t ≤ x` from its negation; prove the goal under each of these mutually exclusive
  -- hypotheses.
  rw [← integral_indicator measurableSet_Iic,← integral_indicator measurableSet_Iic]
  have he : (Iic x).indicator (fun t => f (t+c))=
      fun t => (Iic (x+c)).indicator f (t+c) := by
    funext t
    by_cases ht : t ≤ x
    · simp only [Set.indicator,mem_Iic,add_le_add_iff_right,ht,ite_true]
    · simp only [Set.indicator,mem_Iic,add_le_add_iff_right,ht,ite_false]
  rw [he]
  exact integral_add_right_eq_self _ c

/--
Exact identity `causal a (fun t => m (t+c)) x=causal a m (x+c)`.

Use: `chebyshev2.Filters.jost_translate` rewrites with this identity to establish exact
identity `jost s (fun t => m (t+c)) x=jost s m (x+c)`.

Article: chebyshev2, Lemma 14 via
`chebyshev2.Comparison.symmetric_square_trace_support_at`.

Proof: Prove equality of functions by evaluating both sides at an arbitrary argument.
-/
theorem causal_translate (m : ℝ → ℝ) (a c x : ℝ) :
    causal a (fun t => m (t+c)) x=causal a m (x+c) := by
  -- Prove equality of functions by evaluating both sides at an arbitrary argument.
  have hi := integral_Iic_translate (fun t => exp (a*t)*m t) c x
  have he : (fun t => exp (a*(t+c))*m (t+c))=
      fun t => exp (a*c)*(exp (a*t)*m (t+c)) := by
    funext t
    rw [mul_add,exp_add]
    ring
  rw [he,integral_const_mul] at hi
  unfold causal
  rw [← hi]
  rw [← mul_assoc,← exp_add]
  congr 2
  ring

/--
Exact identity `jost s (fun t => m (t+c)) x=jost s m (x+c)`.

Use: `chebyshev2.Filters.nonlinear_translate` rewrites with this identity to establish
exact identity `nonlinear s (fun t => m (t+c)) x=nonlinear s m (x+c)`.

Article: chebyshev2, Lemma 14 via
`chebyshev2.Comparison.symmetric_logDeterminant_support_at`.

Proof: Use the identities/estimates `chebyshev2.Filters.jost_forcing_integrable`,
`chebyshev2.Filters.jost_equation`, `chebyshev2.Filters.causal_translate` with the
arguments shown in the proof.
-/
theorem jost_translate {m : ℝ → ℝ} (hm : Integrable m) (hn : ∀ x, 0 ≤ m x)
    {s : ℝ} (hs : 0 ≤ s) (c x : ℝ) :
    jost s (fun t => m (t+c)) x=jost s m (x+c) := by
  -- Establish hm as the integrability justification for the later integral estimates or
  -- changes of order.
  have hm' : Integrable (fun t => m (t+c)) := hm.comp_add_right c
  have hn' : ∀ t, 0 ≤ m (t+c) := fun t => hn _
  -- Establish hw as the integrability justification for the later integral estimates or
  -- changes of order.
  have hw : Integrable (fun t => m (t+c)*jost s m (t+c)) :=
    (jost_forcing_integrable hm hn hs).comp_add_right c
  have he : ∀ t, jost s m (t+c)=1+volterra s (fun t => m (t+c)) (fun t => jost s m (t+c)) t := by
    intro t
    rw [jost_equation hm hn hs]
    congr 1
    dsimp only [volterra]
    rw [causal_translate (fun t => m t*jost s m t) 2 c t]
    dsimp only [cumulative]
    rw [integral_Iic_translate (fun t => m t*jost s m t) c t]
  have hu := jost_unique hm' hn' hs hw (C := exp (s*(∫ t, m t)/2))
    (fun t => by
      rw [Real.norm_of_nonneg (jost_positive hm hn hs (t+c)).le]
      exact jost_uniform_bound hm hn hs (t+c)) he
  exact (congrFun hu x).symm

/--
Exact identity `nonlinear s (fun t => m (t+c)) x=nonlinear s m (x+c)`.

Use: `chebyshev2.Comparison.symmetric_logDeterminant_at` uses this identity to establish
the precise assertion is `logDeterminant (kernelEigenvalue hm hn) s= 2*(∫ x in Iic c, nonlinear
s m x)+log (1+nonlinear s m c)`.

Article: chebyshev2, Lemma 14 via
`chebyshev2.Comparison.symmetric_logDeterminant_support_at`.

Proof: Prove equality of functions by evaluating both sides at an arbitrary argument.
-/
theorem nonlinear_translate {m : ℝ → ℝ} (hm : Integrable m) (hn : ∀ x, 0 ≤ m x)
    {s : ℝ} (hs : 0 ≤ s) (c x : ℝ) :
    nonlinear s (fun t => m (t+c)) x=nonlinear s m (x+c) := by
  -- Prove equality of functions by evaluating both sides at an arbitrary argument.
  dsimp only [nonlinear]
  rw [jost_translate hm hn hs c x]
  dsimp only [jostSlope]
  have he : (fun t => m (t+c)*jost s (fun t => m (t+c)) t)=
      fun t => (m (t+c)*jost s m (t+c)) := by
    funext t
    rw [jost_translate hm hn hs]
  rw [he,causal_translate (fun t => m t*jost s m t) 2 c x]

end
end chebyshev2.Filters
