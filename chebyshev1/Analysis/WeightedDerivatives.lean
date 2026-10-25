import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas

/-!
Article: chebyshev1, Theorem 5.2.
Identify a finite family of actual derivatives with mathlib's iterated derivative.
Use: `chebyshev1.Analysis.iteratedDeriv_eq_of_derivatives` feeds
`chebyshev1.SineJacobi.profileDerivative_eq` (profile Derivative eq).
Proof chain: `chebyshev1.SineJacobi.sineEnergy_decimal` — chebyshev1, Theorem 5.2; Exact sine
gain, resolvent expression, asymptotics and energy value.
Source: mathlib, Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas — Leibniz rule for weighted
derivative bounds. The needed form is proved here.
-/
namespace chebyshev1.Analysis
noncomputable section
open Set Filter Topology

/--
Scale-invariant derivative bounds, useful near singular endpoints.

Use: `chebyshev1.Analysis.WeightedDerivatives.mul` uses this definition to establish the
stated quantitative bound `WeightedDerivatives (f*g) x r (fun n => ∑ i ∈ Finset.range (n+1),
(n.choose i : ℝ)*A i*B (n-i)) m`.

Article: chebyshev1, Theorem 5.2 via `chebyshev1.SineJacobi.sineEnergy_decimal`.

Source: mathlib, Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas — Leibniz rule for weighted
derivative bounds.
-/
def WeightedDerivatives (f : ℝ → ℝ) (x r : ℝ) (C : ℕ → ℝ) (m : ℕ) : Prop :=
  ∀ n ≤ m, |iteratedDeriv n f x| * r^n ≤ C n

/-- Multiply two weighted derivative bounds: `|a| r^i ≤ A` and `|b| r^j ≤ B`
imply `|ab| r^(i+j) ≤ AB` for a nonnegative radius `r`.
Use: `WeightedDerivatives.mul` applies this to each pair of derivative terms in
Leibniz's finite binomial convolution; the radius powers then combine exactly.
Article: chebyshev1, Theorem 5.2, via the higher derivative bounds used by
`SineJacobi.sineEnergy_decimal`.
Source: absolute-value multiplicativity and nonnegative product monotonicity in mathlib.
Proof: rewrite the weighted product as the product of the two separately bounded
nonnegative factors, then apply `mul_le_mul`. -/
lemma weighted_mul {a b A B r : ℝ} {i j : ℕ} (hr : 0 ≤ r)
    (ha : |a| * r^i ≤ A) (hb : |b| * r^j ≤ B) :
    |a*b| * r^(i+j) ≤ A*B := by
  -- Nonnegative radius powers make both factors nonnegative, so multiplying the
  -- individual upper bounds preserves the inequality.
  calc
    _ = (|a| * r^i) * (|b| * r^j) := by rw [abs_mul, pow_add]; ring
    _ ≤ A*B := mul_le_mul ha hb (by positivity) (le_trans (by positivity) ha)

/--
Leibniz's rule propagates weighted bounds by a finite binomial convolution.

The stated quantitative bound `WeightedDerivatives (f*g) x r (fun n => ∑ i ∈ Finset.range
(n+1), (n.choose i : ℝ)*A i*B (n-i)) m`.

Use: `chebyshev1.Analysis.WeightedDerivatives.mul_relative` uses this identity to establish
the stated quantitative bound `WeightedDerivatives (f*g) x r (fun n => (∑ i ∈ Finset.range
(n+1), (n.choose i : ℝ)*A i*B (n-i))*(f*g) x) m`.

Article: chebyshev1, Theorem 5.2 via `chebyshev1.SineJacobi.sineEnergy_decimal`.

Source: mathlib, Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas — Leibniz rule for weighted
derivative bounds.

Proof: Identify the summands/integrands on their required domain before replacing the sum or
integral.
-/
theorem WeightedDerivatives.mul {f g : ℝ → ℝ} {x r : ℝ} {A B : ℕ → ℝ} {m : ℕ}
    (hr : 0 ≤ r) (hf : ContDiffAt ℝ m f x) (hg : ContDiffAt ℝ m g x)
    (ha : WeightedDerivatives f x r A m) (hb : WeightedDerivatives g x r B m) :
    WeightedDerivatives (f*g) x r
      (fun n => ∑ i ∈ Finset.range (n+1), (n.choose i : ℝ)*A i*B (n-i)) m := by
  -- Identify the summands/integrands on their required domain before replacing the sum or
  -- integral.
  intro n hn
  rw [iteratedDeriv_mul (hf.of_le (by exact_mod_cast hn)) (hg.of_le (by exact_mod_cast hn))]
  calc
    _ ≤ (∑ i ∈ Finset.range (n+1),
        |(n.choose i : ℝ)*iteratedDeriv i f x*iteratedDeriv (n-i) g x|)*r^n :=
      mul_le_mul_of_nonneg_right (Finset.abs_sum_le_sum_abs _ _) (by positivity)
    _ = ∑ i ∈ Finset.range (n+1), (n.choose i : ℝ)*
        (|iteratedDeriv i f x*iteratedDeriv (n-i) g x| *r^n) := by
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro i hi
      simp only [abs_mul, Nat.abs_cast]
      ring
    _ ≤ _ := by
      apply Finset.sum_le_sum
      intro i hi
      have hi' : i ≤ n := by simpa only [Finset.mem_range, Nat.lt_succ_iff] using hi
      have hh := weighted_mul hr (ha i (hi'.trans hn)) (hb (n-i) (by omega))
      rw [Nat.add_sub_of_le hi'] at hh
      simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hh (Nat.cast_nonneg _)

/--
Multiplication preserves relative bounds, with binomial convolution of constants.

The stated quantitative bound `WeightedDerivatives (f*g) x r (fun n => (∑ i ∈ Finset.range
(n+1), (n.choose i : ℝ)*A i*B (n-i))*(f*g) x) m`.

Use: `chebyshev1.SineJacobi.energyDensity_weighted_derivatives` uses this identity to
establish the stated quantitative bound `WeightedDerivatives energyDensity t t (fun n =>
energyDerivativeBound n*energyDensity t) 4`.

Article: chebyshev1, Theorem 5.2 via `chebyshev1.SineJacobi.sineEnergy_decimal`.

Source: mathlib, Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas — Leibniz rule for weighted
derivative bounds.

Proof: Identify the summands/integrands on their required domain before replacing the sum or
integral.
-/
theorem WeightedDerivatives.mul_relative {f g : ℝ → ℝ} {x r : ℝ} {A B : ℕ → ℝ} {m : ℕ}
    (hr : 0 ≤ r) (hf : ContDiffAt ℝ m f x) (hg : ContDiffAt ℝ m g x)
    (ha : WeightedDerivatives f x r (fun n => A n*f x) m)
    (hb : WeightedDerivatives g x r (fun n => B n*g x) m) :
    WeightedDerivatives (f*g) x r
      (fun n => (∑ i ∈ Finset.range (n+1), (n.choose i : ℝ)*A i*B (n-i))*(f*g) x) m := by
  -- Identify the summands/integrands on their required domain before replacing the sum or
  -- integral.
  intro n hn
  convert ha.mul hr hf hg hb n hn using 1
  simp only [Pi.mul_apply, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i hi
  ring

/--
The derivative of the iterated derivative at a smooth point.

The actual derivative at the stated point: `HasDerivAt (iteratedDeriv n f) (iteratedDeriv (n+1)
f x) x`.

Use:
`_private.chebyshev1.SineJacobi.GradedEnergy.0.chebyshev1.SineJacobi.gradedDerivative_deriv`
uses this derivative formula to establish the actual derivative at the stated point:
`HasDerivAt (gradedDerivative j) (gradedDerivative (j+1) s) s`.

Article: chebyshev1, Theorem 5.2 via `chebyshev1.SineJacobi.sineEnergy_decimal`.

Source: mathlib, Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas — Leibniz rule for weighted
derivative bounds.

Proof: Expand/rewrite the named definitions and identities appearing in the tactic block; the
remaining goal is a direct simplification or algebraic consequence.
-/
theorem hasDerivAt_iteratedDeriv {f : ℝ → ℝ} {x : ℝ} {n : ℕ}
    (hf : ContDiffAt ℝ (n+1 : ℕ) f x) :
    HasDerivAt (iteratedDeriv n f) (iteratedDeriv (n+1) f x) x := by
  -- Expand/rewrite the named definitions and identities appearing in the tactic block; the
  -- remaining goal is a direct simplification or algebraic consequence.
  have hd := hf.contDiffWithinAt.differentiableWithinAt_iteratedDerivWithin
    (m := n) (by exact_mod_cast Nat.lt_succ_self n) (s := univ) (by simp)
  have hd' : DifferentiableAt ℝ (iteratedDeriv n f) x := by
    simpa only [iteratedDerivWithin_univ, differentiableWithinAt_univ] using hd
  simpa only [iteratedDeriv_succ] using hd'.hasDerivAt

/--
Identify a finite family of actual derivatives with mathlib's iterated derivative.

Establishes the uniform, quantified assertion `∀ n ≤ m, EqOn (iteratedDeriv n (F 0)) (F n) s`.

Use: `chebyshev1.SineJacobi.gradedEnergy_fourth_derivative` uses this bound to establish
the identity stated in that declaration.

Article: chebyshev1, Theorem 5.2 via `chebyshev1.SineJacobi.sineEnergy_decimal`.

Source: mathlib, Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas — Leibniz rule for weighted
derivative bounds.

Proof: Induct on `n`; the recursive step uses the previous-stage assertion. Intersect the
eventual or almost-everywhere hypotheses, then prove the asserted relation at an arbitrary
point in that intersection.
-/
theorem iteratedDeriv_eq_of_derivatives {F : ℕ → ℝ → ℝ} {s : Set ℝ} {m : ℕ}
    (hs : IsOpen s) (hF : ∀ n < m, ∀ x ∈ s, HasDerivAt (F n) (F (n+1) x) x) :
    ∀ n ≤ m, EqOn (iteratedDeriv n (F 0)) (F n) s := by
  -- Induct on `n`; the recursive step uses the previous-stage assertion.
  intro n hn
  induction n with
  | zero => intro x hx; simp
  | succ n ih =>
    intro x hx
    rw [iteratedDeriv_succ]
    have he := ih (by omega)
    have he' : iteratedDeriv n (F 0) =ᶠ[𝓝 x] F n := by
      filter_upwards [hs.mem_nhds hx] with y hy
      exact he hy
    rw [he'.deriv_eq]
    exact (hF n (by omega) x hx).deriv

end
end chebyshev1.Analysis
