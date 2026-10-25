import chebyshev1.SineJacobi.Terminal

/-!
Article: chebyshev1, Lemma E.2.
The endpoint-normalized nonnegative cosine expansion in E.2.
Result: `chebyshev1.SineJacobi.normalized_fourier` supplies the stated article conclusion.
-/
namespace chebyshev1.SineJacobi
noncomputable section
open Polynomial Real
open scoped BigOperators

/--
Defines `endpoint` of type `ℝ` by `(2:ℝ)^s*((data N).leading s).eval 1`.

Use: `chebyshev1.SineJacobi.endpoint_sum` uses this definition to establish the identity
`endpoint N s = ∑ k ∈ Finset.range (s+1), coefficient N s k`.

Article: chebyshev1, Theorem E.1 via `chebyshev1.SineJacobi.leading_endpoint_max`.
-/
def endpoint (N s : ℕ) : ℝ := (2:ℝ)^s*((data N).leading s).eval 1

/--
Exact identity `endpoint N s = ∑ k ∈ Finset.range (s+1), coefficient N s k`.

Use: `chebyshev1.SineJacobi.endpoint_pos` rewrites with this identity to establish the
stated quantitative bound `0 < endpoint N s`.

Article: chebyshev1, Theorem E.1 via `chebyshev1.SineJacobi.leading_endpoint_max`.

Proof: Use the identities/estimates `chebyshev1.SineJacobi.leading_fourier` with the
arguments shown in the proof.
-/
theorem endpoint_sum (N s : ℕ) (hs : s < N) :
    endpoint N s = ∑ k ∈ Finset.range (s+1), coefficient N s k := by simpa only [mul_zero, cos_zero, mul_one, endpoint] using leading_fourier N s hs 0

/--
The stated quantitative bound `0 < endpoint N s`.

Use: `chebyshev1.SineJacobi.leading_eval_one_pos` uses this bound to establish the stated
quantitative bound `0 < ((data N).leading s).eval 1`.

Article: chebyshev1, Theorem E.3 via `chebyshev1.SineJacobi.endpoint_global_bound`.

Proof: Use the identities/estimates `chebyshev1.SineJacobi.endpoint_sum`,
`chebyshev1.SineJacobi.coefficient_pos` with the arguments shown in the proof.
-/
theorem endpoint_pos (N s : ℕ) (hs : s < N) : 0 < endpoint N s := by
  rw [endpoint_sum N s hs]
  apply Finset.sum_pos'
  · intro k hk
    exact (coefficient_pos N s k hs (by have := Finset.mem_range.mp hk; omega)).le
  · exact ⟨0, by simp, coefficient_pos N s 0 hs (by omega)⟩

/--
The stated quantitative bound `0 < ((data N).leading s).eval 1`.

Use: `chebyshev1.SineJacobi.normalized_fourier` uses this bound to establish the identity
`((data N).leading s).eval (cos theta) / ((data N).leading s).eval 1 = ∑ k ∈ Finset.range
(s+1), normalizedCoefficient N s k*cos (((s:ℝ)-2*(k:ℝ))*theta)`.

Article: chebyshev1, Theorem E.1 via `chebyshev1.SineJacobi.kernel_abs_le_endpoint`.

Proof: Use the identities/estimates `chebyshev1.SineJacobi.endpoint_pos` with the arguments
shown in the proof.
-/
theorem leading_eval_one_pos (N s : ℕ) (hs : s < N) : 0 < ((data N).leading s).eval 1 :=
  (mul_pos_iff_of_pos_left (pow_pos (by norm_num : (0:ℝ) < 2) s)).mp (endpoint_pos N s hs)

/--
All proper leading blocks attain their absolute maxima at one.

The stated quantitative bound `|((data N).leading s).eval x| ≤ ((data N).leading s).eval 1`.

Use: `chebyshev1.SineJacobi.kernel_abs_le_endpoint` uses this bound to establish the stated
quantitative bound `|((data N).realization I).kernel N s lam nu| ≤ |((data N).realization
I).kernel N s I.mu I.mu|`.

Article: chebyshev1, Theorem E.1.

Proof: Use the identities/estimates `chebyshev1.SineJacobi.leading_fourier`,
`chebyshev1.SineJacobi.endpoint_sum`, `chebyshev1.SineJacobi.coefficient_pos` with the
arguments shown in the proof.
-/
theorem leading_endpoint_max (N s : ℕ) (hs : s < N) (x : ℝ) (hx : x ∈ Set.Icc (-1) 1) :
    |((data N).leading s).eval x| ≤ ((data N).leading s).eval 1 := by
  -- Use the identities/estimates `chebyshev1.SineJacobi.leading_fourier`,
  -- `chebyshev1.SineJacobi.endpoint_sum`, `chebyshev1.SineJacobi.coefficient_pos` with
  -- the arguments shown in the proof.
  have hf := leading_fourier N s hs (arccos x)
  rw [cos_arccos hx.1 hx.2] at hf
  have hb : |(2:ℝ)^s*((data N).leading s).eval x| ≤ endpoint N s := by
    rw [hf, endpoint_sum N s hs]
    calc
      _ ≤ ∑ k ∈ Finset.range (s+1), |coefficient N s k*cos (((s:ℝ)-2*(k:ℝ))*arccos x)| :=
        Finset.abs_sum_le_sum_abs _ _
      _ ≤ _ := by
        apply Finset.sum_le_sum
        intro k hk
        have hc := (coefficient_pos N s k hs (by have := Finset.mem_range.mp hk; omega)).le
        rw [abs_mul, abs_of_nonneg hc]
        simpa only [mul_one] using mul_le_mul_of_nonneg_left (abs_cos_le_one _) hc
  rw [abs_mul, abs_of_pos (pow_pos (by norm_num : (0:ℝ) < 2) s)] at hb
  exact (mul_le_mul_iff_right₀ (pow_pos (by norm_num : (0:ℝ) < 2) s)).mp hb

/--
Defines `normalizedCoefficient` of type `ℝ` by `coefficient N s k / endpoint N s`.

Use: `chebyshev1.SineJacobi.normalizedCoefficient_sum` uses this definition to establish
exact identity `∑ k ∈ Finset.range (s+1), normalizedCoefficient N s k = 1`.

Article: chebyshev1, Lemma E.2 via `chebyshev1.SineJacobi.normalized_fourier`.
-/
def normalizedCoefficient (N s k : ℕ) : ℝ := coefficient N s k / endpoint N s

/--
The stated quantitative bound `0 ≤ normalizedCoefficient N s k`.

Use: a standalone supporting bound for the article chain below; no retained declaration
currently has an explicit proof dependency on it.

Article: chebyshev1, Lemma E.2.

Proof: Use the identities/estimates `chebyshev1.SineJacobi.coefficient_pos`,
`chebyshev1.SineJacobi.endpoint_pos` with the arguments shown in the proof.
-/
theorem normalizedCoefficient_nonneg (N s k : ℕ) (hs : s < N) (hk : k ≤ s) :
    0 ≤ normalizedCoefficient N s k :=
  div_nonneg (coefficient_pos N s k hs hk).le (endpoint_pos N s hs).le

/--
Exact identity `∑ k ∈ Finset.range (s+1), normalizedCoefficient N s k = 1`.

Use: the ordered `Article` showcase checks this article-facing formulation directly.

Article: chebyshev1, Lemma E.2.

Proof: Use the identities/estimates `chebyshev1.SineJacobi.endpoint_sum`,
`chebyshev1.SineJacobi.endpoint_pos` with the arguments shown in the proof.
-/
theorem normalizedCoefficient_sum (N s : ℕ) (hs : s < N) :
    ∑ k ∈ Finset.range (s+1), normalizedCoefficient N s k = 1 := by
  unfold normalizedCoefficient
  rw [← Finset.sum_div, ← endpoint_sum N s hs, div_self (ne_of_gt (endpoint_pos N s hs))]

/--
The endpoint-normalized nonnegative cosine expansion in E.2.

Exact identity `((data N).leading s).eval (cos theta) / ((data N).leading s).eval 1 = ∑ k ∈
Finset.range (s+1), normalizedCoefficient N s k*cos (((s:ℝ)-2*(k:ℝ))*theta)`.

Use: the ordered `Article` showcase checks this article-facing formulation directly.

Article: chebyshev1, Lemma E.2.

Proof: Clear the denominators using the available nonzero hypotheses, then verify the remaining
algebraic identity.
-/
theorem normalized_fourier (N s : ℕ) (hs : s < N) (theta : ℝ) :
    ((data N).leading s).eval (cos theta) / ((data N).leading s).eval 1 =
      ∑ k ∈ Finset.range (s+1), normalizedCoefficient N s k*cos (((s:ℝ)-2*(k:ℝ))*theta) := by
  -- Clear the denominators using the available nonzero hypotheses, then verify the remaining
  -- algebraic identity.
  have hf := leading_fourier N s hs theta
  have hn := ne_of_gt (leading_eval_one_pos N s hs)
  have hp : (2:ℝ)^s ≠ 0 := pow_ne_zero s (by norm_num)
  simp only [normalizedCoefficient, div_mul_eq_mul_div]
  rw [← Finset.sum_div, ← hf]
  unfold endpoint
  field_simp

end
end chebyshev1.SineJacobi
