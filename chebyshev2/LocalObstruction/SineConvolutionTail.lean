import chebyshev2.LocalObstruction.SineTail
import chebyshev2.LocalObstruction.KernelPairing
import chebyshev2.Filters.Linear

/-!
Article: chebyshev2, Theorem 6.1.
Lemma 26(iv): the actual trace gradient W2 has the required exponential asymptotic, with remainder
bounded by the proved sine tail.
Use: `chebyshev2.LocalObstruction.sine_convolution_tail` feeds
`chebyshev2.LocalObstruction.theorem_6_1` (theorem 6 1).
Proof chain: `chebyshev2.LocalObstruction.theorem_6_1` — chebyshev2, Theorem 6.1; No locally
sharp C1 bound from finitely many spectral observations.
-/
namespace chebyshev2.LocalObstruction
noncomputable section
open Set Real Filter MeasureTheory Asymptotics chebyshev2.SineContinuum
open scoped Topology
set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false

 /--
Integrability of the displayed function: `Integrable (fun y => exp (2*y)*m y)`.

Use: `chebyshev2.LocalObstruction.sine_convolution_remainder_bound` rewrites with this
integrability result to prove the bound `|W₂ m
x-sineTraceTailCoefficient*exp (-2*x)|≤weightedSineTail x`.

Article: chebyshev2, Theorem 6.1 via `chebyshev2.LocalObstruction.sine_green_scale_tail`.

Proof: Prove equality of functions by evaluating both sides at an arbitrary argument.
-/
theorem sine_weighted_moment_integrable : Integrable (fun y => exp (2*y)*m y) := by
  -- Prove equality of functions by evaluating both sides at an arbitrary argument.
  have hleft := chebyshev2.Filters.forcing_integrable (by norm_num : (0:ℝ)≤2) m_integrable 1
  -- Establish hright as the integrability justification for the later integral estimates or
  -- changes of order.
  have hright : IntegrableOn (fun y => exp (2*y)*m y) (Ioi (1:ℝ)) := by
    have hi := (weightedSineTail_integrable (x := 1) le_rfl).const_mul (exp 2)
    have he : (fun y => exp (2*y)*m y)=fun y => exp 2*(exp (2*(y-1))*m y) := by
      funext y
      rw [← mul_assoc,← exp_add]
      congr 1
      congr 1
      ring
    rw [he]
    exact hi
  have h := hleft.union hright
  simpa only [Iic_union_Ioi,integrableOn_univ] using h

 /--
Defines `sineTraceTailCoefficient` of type `ℝ` by `∫ y, exp (2*y)*m y`.

Use: `chebyshev2.LocalObstruction.sine_convolution_remainder_bound` uses this definition to
establish the stated quantitative bound `|W₂ m x-sineTraceTailCoefficient*exp
(-2*x)|≤weightedSineTail x`.

Article: chebyshev2, Theorem 6.1 via `chebyshev2.LocalObstruction.theorem_6_1`.
-/
def sineTraceTailCoefficient : ℝ := ∫ y, exp (2*y)*m y

 /--
The stated quantitative bound `|W₂ m x-sineTraceTailCoefficient*exp (-2*x)|≤weightedSineTail
x`.

Use: `chebyshev2.LocalObstruction.sine_convolution_tail` uses this bound to establish the
stated quantitative bound `(fun x => W₂ m x-sineTraceTailCoefficient*exp (-2*x)) =o[atTop] n`.

Article: chebyshev2, Theorem 6.1 via `chebyshev2.LocalObstruction.theorem_6_1`.

Proof: Separate `y ∈ Ioi x` from its negation; prove the goal under each of these mutually
exclusive hypotheses.
-/
theorem sine_convolution_remainder_bound {x : ℝ} (hx : 1≤x) :
    |W₂ m x-sineTraceTailCoefficient*exp (-2*x)|≤weightedSineTail x := by
  -- Separate `y ∈ Ioi x` from its negation; prove the goal under each of these mutually
  -- exclusive hypotheses.
  let f := fun y => m y*exp (-2*|x-y|)-exp (-2*x)*(exp (2*y)*m y)
  have he : W₂ m x-sineTraceTailCoefficient*exp (-2*x)=∫ y, f y := by
    rw [integral_sub (W₂_integrable m_integrable x)
      (sine_weighted_moment_integrable.const_mul _),integral_const_mul]
    unfold W₂ sineTraceTailCoefficient
    ring
  -- Establish hb as the integrability justification for the later integral estimates or
  -- changes of order.
  have hb : Integrable ((Ioi x).indicator (fun y => exp (2*(y-x))*m y)) :=
    (weightedSineTail_integrable hx).integrable_indicator measurableSet_Ioi
  have hbound : ∀ y, ‖f y‖≤(Ioi x).indicator (fun y => exp (2*(y-x))*m y) y := by
    intro y
    have hex : exp (-2*x)*(exp (2*y)*m y)=exp (2*(y-x))*m y := by
      rw [← mul_assoc,← exp_add]
      congr 1
      congr 1
      ring
    by_cases hy : y ∈ Ioi x
    · have hxy : x<y := hy
      rw [indicator_of_mem hy]
      have hab : exp (-2*|x-y|)≤exp (2*(y-x)) := by
        rw [abs_of_nonpos (sub_nonpos.mpr hxy.le)]
        apply exp_le_exp.mpr
        linarith
      have hnonneg : 0≤m y*exp (-2*|x-y|) := mul_nonneg (m_positive y).le (exp_pos _).le
      have hle : m y*exp (-2*|x-y|)≤exp (2*(y-x))*m y := by
        simpa only [mul_comm] using mul_le_mul_of_nonneg_left hab (m_positive y).le
      change |m y*exp (-2*|x-y|)-exp (-2*x)*(exp (2*y)*m y)|≤_
      rw [hex,abs_of_nonpos (sub_nonpos.mpr hle)]
      linarith
    · have hxy : y≤x := le_of_not_gt hy
      rw [indicator_of_notMem hy]
      have hz : f y=0 := by
        dsimp only [f]
        rw [hex,abs_of_nonneg (sub_nonneg.mpr hxy)]
        rw [show -2*(x-y)=2*(y-x) by ring]
        ring
      rw [hz,norm_zero]
  rw [he]
  have h := norm_integral_le_of_norm_le hb (Eventually.of_forall hbound)
  rw [integral_indicator measurableSet_Ioi] at h
  exact h

 /--
The stated quantitative bound `(fun x => W₂ m x-sineTraceTailCoefficient*exp (-2*x)) =o[atTop]
n`.

Use: `chebyshev2.LocalObstruction.traceGradient` uses this identity in the displayed
construction of `traceGradient`. Its inputs and component formulas are fixed by that
definition.

Article: chebyshev2, Theorem 6.1 via `chebyshev2.LocalObstruction.theorem_6_1`.

Proof: Intersect the eventual or almost-everywhere hypotheses, then prove the asserted relation
at an arbitrary point in that intersection.
-/
theorem sine_convolution_tail :
    (fun x => W₂ m x-sineTraceTailCoefficient*exp (-2*x)) =o[atTop] n := by
  apply IsLittleO.of_bound
  intro c hc
  filter_upwards [weightedSineTail_littleO.bound hc,eventually_ge_atTop (1:ℝ)] with x ht hx
  rw [Real.norm_eq_abs,abs_of_nonneg (weightedSineTail_bounds hx).1] at ht
  rw [Real.norm_eq_abs]
  exact (sine_convolution_remainder_bound hx).trans ht

end
end chebyshev2.LocalObstruction
