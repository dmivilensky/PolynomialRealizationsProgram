import chebyshev2.SineContinuum.MercerExpansion
import Mathlib.Topology.UniformSpace.Dini

/-!
Article: chebyshev2, Lemma 5.
Dini's theorem supplies uniform diagonal convergence on the full closed interval, including the
singular endpoints.
Use: `chebyshev2.SineContinuum.green_mercer_diagonal_uniform` feeds
`chebyshev2.SineContinuum.green_mercer_uniform_absolute` (Uniform absolute convergence of the
literal Mercer series on the entire closed square, expressed as a uniform bound on every infinite
absolute tail).
Source: Riesz and Sz.-Nagy, Functional Analysis, §98 — Mercer diagonal expansion. The needed form is
proved here.
-/
namespace chebyshev2.SineContinuum
noncomputable section
open Set Real MeasureTheory Filter
open scoped BigOperators Topology
attribute [local instance] Measure.Subtype.measureSpace
set_option backward.isDefEq.respectTransparency true

/--
Exact identity `upsilon j 0=0`.

Use: `chebyshev2.SineContinuum.green_mercer_closed` rewrites with this identity to
establish the value of a convergent infinite sum: `HasSum (fun j => upsilon j t*upsilon j s/mu
j) (green t s)`.

Article: chebyshev2, Lemma 5 via `chebyshev2.SineContinuum.green_mercer_uniform`.

Source: Riesz and Sz.-Nagy, Functional Analysis, §98 — Mercer diagonal expansion.

Proof: Rewrite the definitions and library identities explicitly named in the proof, then
discharge the resulting algebraic or order relation.
-/
theorem upsilon_zero (j : ℕ) : upsilon j 0=0 := by
  simp [upsilon,chebyshev1.SineJacobi.profileWeight]
/--
Exact identity `upsilon j 1=0`.

Use: `chebyshev2.SineContinuum.green_mercer_closed` rewrites with this identity to
establish the value of a convergent infinite sum: `HasSum (fun j => upsilon j t*upsilon j s/mu
j) (green t s)`.

Article: chebyshev2, Lemma 5 via `chebyshev2.SineContinuum.green_mercer_uniform`.

Source: Riesz and Sz.-Nagy, Functional Analysis, §98 — Mercer diagonal expansion.

Proof: Rewrite the definitions and library identities explicitly named in the proof, then
discharge the resulting algebraic or order relation.
-/
theorem upsilon_one (j : ℕ) : upsilon j 1=0 := by simp [upsilon,chebyshev1.SineJacobi.profileWeight]

/--
The value of a convergent infinite sum: `HasSum (fun j => upsilon j t*upsilon j s/mu j) (green
t s)`.

Use: `chebyshev2.SineContinuum.green_mercer_diagonal_closed` uses this infinite-sum formula
to establish the value of a convergent infinite sum: `HasSum (fun j => upsilon j t^2/mu j)
(green t t)`.

Article: chebyshev2, Lemma 5 via `chebyshev2.SineContinuum.green_mercer_uniform`.

Source: Riesz and Sz.-Nagy, Functional Analysis, §98 — Mercer diagonal expansion.

Proof: Use the identities/estimates `chebyshev2.SineContinuum.upsilon_zero`,
`chebyshev2.SineContinuum.l_zero`, `chebyshev2.SineContinuum.upsilon_one` with the
arguments shown in the proof.
-/
theorem green_mercer_closed {t s : ℝ} (ht : t ∈ Icc (0:ℝ) 1) (hs : s ∈ Icc (0:ℝ) 1) :
    HasSum (fun j => upsilon j t*upsilon j s/mu j) (green t s) := by
  -- Use the identities/estimates `chebyshev2.SineContinuum.upsilon_zero`,
  -- `chebyshev2.SineContinuum.l_zero`, `chebyshev2.SineContinuum.upsilon_one` with the
  -- arguments shown in the proof.
  rcases eq_endpoints_or_mem_Ioo_of_mem_Icc ht with rfl | rfl | ht
  · simp only [upsilon_zero,zero_mul,zero_div]
    have hg : green 0 s=0 := by simp [green,min_eq_left hs.1,max_eq_right hs.1,l_zero]
    rw [hg]
    exact hasSum_zero
  · simp only [upsilon_one,zero_mul,zero_div]
    have hg : green 1 s=0 := by simp [green,min_eq_right hs.2,max_eq_left hs.2,r_one]
    rw [hg]
    exact hasSum_zero
  rcases eq_endpoints_or_mem_Ioo_of_mem_Icc hs with rfl | rfl | hs
  · simp only [upsilon_zero,mul_zero,zero_div]
    have hg : green t 0=0 := by simp [green,min_eq_right ht.1.le,max_eq_left ht.1.le,l_zero]
    rw [hg]
    exact hasSum_zero
  · simp only [upsilon_one,mul_zero,zero_div]
    have hg : green t 1=0 := by simp [green,min_eq_left ht.2.le,max_eq_right ht.2.le,r_one]
    rw [hg]
    exact hasSum_zero
  · exact green_mercer_hasSum ht hs

/--
The value of a convergent infinite sum: `HasSum (fun j => upsilon j t^2/mu j) (green t t)`.

Use: `chebyshev2.SineContinuum.green_mercer_absolute` uses this infinite-sum formula to
establish summability of the displayed sequence: `Summable (fun j => |upsilon j t*upsilon j
s/mu j|)`.

Article: chebyshev2, Lemma 5 via
`chebyshev2.SineContinuum.green_mercer_diagonal_uniform`.

Source: Riesz and Sz.-Nagy, Functional Analysis, §98 — Mercer diagonal expansion.

Proof: Use the identities/estimates `chebyshev2.SineContinuum.green_mercer_closed` with the
arguments shown in the proof.
-/
theorem green_mercer_diagonal_closed {t : ℝ} (ht : t ∈ Icc (0:ℝ) 1) :
    HasSum (fun j => upsilon j t^2/mu j) (green t t) := by simpa only [pow_two] using green_mercer_closed ht ht

/--
The stated quantitative bound `|upsilon j t*upsilon j s/mu j| ≤ (upsilon j t^2/mu j+upsilon j
s^2/mu j)/2`.

Use: `chebyshev2.SineContinuum.green_mercer_absolute` uses this bound to establish
summability of the displayed sequence: `Summable (fun j => |upsilon j t*upsilon j s/mu j|)`.

Article: chebyshev2, Lemma 5 via `chebyshev2.SineContinuum.green_mercer_uniform`.

Source: Riesz and Sz.-Nagy, Functional Analysis, §98 — Mercer diagonal expansion.

Proof: Clear the denominators using the available nonzero hypotheses, then verify the remaining
algebraic identity.
-/
theorem mercer_term_abs_le (j : ℕ) (t s : ℝ) :
    |upsilon j t*upsilon j s/mu j| ≤
      (upsilon j t^2/mu j+upsilon j s^2/mu j)/2 := by
  -- Clear the denominators using the available nonzero hypotheses, then verify the remaining
  -- algebraic identity.
  rw [abs_div,abs_of_pos (mu_positive j)]
  apply (div_le_iff₀ (mu_positive j)).mpr
  have h : 2*|upsilon j t*upsilon j s| ≤ upsilon j t^2+upsilon j s^2 := by
    rw [abs_mul]
    nlinarith [sq_nonneg (|upsilon j t|-|upsilon j s|),sq_abs (upsilon j t),sq_abs (upsilon j s)]
  field_simp [(mu_positive j).ne']
  nlinarith

/--
Summability of the displayed sequence: `Summable (fun j => |upsilon j t*upsilon j s/mu j|)`.

Use: `chebyshev2.SineContinuum.mercer_absolute_tail_bound` uses this summability result to
establish the stated quantitative bound `(∑' j, |upsilon (j+N) t*upsilon (j+N) s/mu (j+N)|) ≤
(mercerDiagonalTail N t+mercerDiagonalTail N s)/2`.

Article: chebyshev2, Lemma 5 via `chebyshev2.SineContinuum.green_mercer_uniform`.

Source: Riesz and Sz.-Nagy, Functional Analysis, §98 — Mercer diagonal expansion.

Proof: Use the identities/estimates
`chebyshev2.SineContinuum.green_mercer_diagonal_closed`,
`chebyshev2.SineContinuum.mercer_term_abs_le` with the arguments shown in the proof.
-/
theorem green_mercer_absolute {t s : ℝ} (ht : t ∈ Icc (0:ℝ) 1) (hs : s ∈ Icc (0:ℝ) 1) :
    Summable (fun j => |upsilon j t*upsilon j s/mu j|) := by
  apply (((green_mercer_diagonal_closed ht).summable.add
    (green_mercer_diagonal_closed hs).summable).div_const 2).of_nonneg_of_le
  · intro j; exact abs_nonneg _
  · intro j; exact mercer_term_abs_le j t s

/--
Defines `mercerDiagonalPartial` of type `ℝ` by `∑ j ∈ Finset.range N, upsilon j t^2/mu j`.

Use: `chebyshev2.SineContinuum.mercerDiagonalPartial_monotone` rewrites with this
definition to establish monotonicity in increasing order: `Monotone (fun N =>
mercerDiagonalPartial N t)`.

Article: chebyshev2, Lemma 5 via
`chebyshev2.SineContinuum.green_mercer_diagonal_uniform`.

Source: Riesz and Sz.-Nagy, Functional Analysis, §98 — Mercer diagonal expansion.
-/
def mercerDiagonalPartial (N : ℕ) (t : ℝ) : ℝ :=
  ∑ j ∈ Finset.range N, upsilon j t^2/mu j

/--
Continuity of the displayed function: `Continuous (mercerDiagonalPartial N)`.

Use: `chebyshev2.SineContinuum.green_mercer_diagonal_uniform` uses this continuity result
to prove the bound `TendstoUniformlyOn mercerDiagonalPartial (fun t =>
green t t) atTop (Icc (0:ℝ) 1)`.

Article: chebyshev2, Lemma 5 via
`chebyshev2.SineContinuum.green_mercer_diagonal_uniform`.

Source: Riesz and Sz.-Nagy, Functional Analysis, §98 — Mercer diagonal expansion.

Proof: Use the identities/estimates `chebyshev2.SineContinuum.upsilon_continuous` with the
arguments shown in the proof.
-/
theorem mercerDiagonalPartial_continuous (N : ℕ) : Continuous (mercerDiagonalPartial N) := by
  apply continuous_finsetSum
  intro j _
  exact (upsilon_continuous j).pow 2 |>.div_const (mu j)

/--
Monotonicity in increasing order: `Monotone (fun N => mercerDiagonalPartial N t)`.

Use: `chebyshev2.SineContinuum.green_mercer_diagonal_uniform` uses this identity to
establish the stated quantitative bound `TendstoUniformlyOn mercerDiagonalPartial (fun t =>
green t t) atTop (Icc (0:ℝ) 1)`.

Article: chebyshev2, Lemma 5 via
`chebyshev2.SineContinuum.green_mercer_diagonal_uniform`.

Source: Riesz and Sz.-Nagy, Functional Analysis, §98 — Mercer diagonal expansion.

Proof: Use the identities/estimates `chebyshev2.SineContinuum.mu_positive` with the
arguments shown in the proof.
-/
theorem mercerDiagonalPartial_monotone (t : ℝ) : Monotone (fun N => mercerDiagonalPartial N t) := by
  apply monotone_nat_of_le_succ
  intro N
  simp only [mercerDiagonalPartial,Finset.sum_range_succ]
  exact le_add_of_nonneg_right (div_nonneg (sq_nonneg _) (mu_positive N).le)

/--
Dini's theorem supplies uniform diagonal convergence on the full closed interval, including the
singular endpoints.

The stated quantitative bound `TendstoUniformlyOn mercerDiagonalPartial (fun t => green t t)
atTop (Icc (0:ℝ) 1)`.

Use: `chebyshev2.SineContinuum.green_mercer_uniform_absolute` uses this limit to establish
constructs witnesses with the exact properties `∃ N : ℕ, ∀ n ≥ N, ∀ t ∈ Icc (0:ℝ) 1, ∀ s ∈ Icc
(0:ℝ) 1, (∑' j, |upsilon (j+n) t*upsilon (j+n) s/mu (j+n)|) < ε`.

Article: chebyshev2, Lemma 5.

Source: Riesz and Sz.-Nagy, Functional Analysis, §98 — Mercer diagonal expansion.

Proof: Use the identities/estimates
`chebyshev2.SineContinuum.mercerDiagonalPartial_continuous`,
`chebyshev2.SineContinuum.mercerDiagonalPartial_monotone`,
`chebyshev2.SineContinuum.green_continuousOn` with the arguments shown in the proof.
-/
theorem green_mercer_diagonal_uniform :
    TendstoUniformlyOn mercerDiagonalPartial (fun t => green t t) atTop (Icc (0:ℝ) 1) := by
  -- Use the identities/estimates
  -- `chebyshev2.SineContinuum.mercerDiagonalPartial_continuous`,
  -- `chebyshev2.SineContinuum.mercerDiagonalPartial_monotone`,
  -- `chebyshev2.SineContinuum.green_continuousOn` with the arguments shown in the proof.
  apply Monotone.tendstoUniformlyOn_of_forall_tendsto isCompact_Icc
    (fun N => (mercerDiagonalPartial_continuous N).continuousOn)
    (fun t _ => mercerDiagonalPartial_monotone t)
  · exact green_continuousOn.comp (f := fun t : ℝ => (t,t))
      (continuous_id.prodMk continuous_id).continuousOn
      (fun _ ht => ⟨ht,ht⟩)
  · intro t ht
    exact (green_mercer_diagonal_closed ht).tendsto_sum_nat

end
end chebyshev2.SineContinuum
