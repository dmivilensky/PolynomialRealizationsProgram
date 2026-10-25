import chebyshev1.SineJacobi.LocalPotential
import chebyshev1.SineJacobi.LeadingBounds

/-!
Article: chebyshev1, Theorem E.3.
The exact second-difference equation appearing in E.3.
Use: `chebyshev1.SineJacobi.endpoint_second_difference_nonpos` feeds
`chebyshev1.SineJacobi.endpoint_midpoint_control` (endpoint midpoint control).
Proof chain: `chebyshev1.SineJacobi.endpoint_global_bound` — chebyshev1, Theorem E.3;
Hard-edge recurrence, singular ODE, uniqueness and endpoint limits.
-/
namespace chebyshev1.SineJacobi
noncomputable section
open Polynomial Polynomial.Chebyshev Real

/--
Exact identity `endpoint N 0 = 1`.

Use: `chebyshev1.SineJacobi.endpoint_half_bound` rewrites with this identity to establish
the stated quantitative bound `endpoint N s ≤ (Real.pi^2/2)*Real.sqrt ((s:ℝ)+1)`.

Article: chebyshev1, Theorem E.3 via `chebyshev1.SineJacobi.endpoint_global_bound`.

Proof: Rewrite the definitions and library identities explicitly named in the proof, then
discharge the resulting algebraic or order relation.
-/
@[simp] theorem endpoint_zero (N : ℕ) : endpoint N 0 = 1 := by simp [endpoint]
/--
Exact identity `endpoint N 1 = 2`.

Use: registered as a simplification rule for the displayed expression. The rule remains
available even when kernel reduction eliminates an explicit reference to this lemma.

Article: chebyshev1, Theorem E.3.

Proof: Rewrite the definitions and library identities explicitly named in the proof, then
discharge the resulting algebraic or order relation.
-/
@[simp] theorem endpoint_one (N : ℕ) : endpoint N 1 = 2 := by simp [endpoint]

/--
Exact identity `endpoint N N = 2`.

Use: `chebyshev1.SineJacobi.endpoint_global_bound` rewrites with this identity to establish
the stated quantitative bound `0 < endpoint N s ∧ endpoint N s ≤ (3*Real.pi^2/2)*Real.sqrt
(N:ℝ)`.

Article: chebyshev1, Theorem E.3 via `chebyshev1.SineJacobi.endpoint_global_bound`.

Proof: Clear the denominators using the available nonzero hypotheses, then verify the remaining
algebraic identity.
-/
theorem endpoint_terminal (N : ℕ) (hN : 0 < N) : endpoint N N = 2 := by
  rw [endpoint, terminal N hN]
  simp only [eval_mul, eval_C, T_eval_one, mul_one]
  field_simp

/--
Exact identity `endpoint N (n+2) = 2*endpoint N (n+1) - 4*(data N).aSq (n+1)*endpoint N n`.

Use: `chebyshev1.SineJacobi.endpoint_second_difference` rewrites with this identity to
establish exact identity `endpoint N (n+2)-2*endpoint N (n+1)+endpoint N n = -(sin (h N/2)^2 /
(sin (((n+1:ℕ):ℝ)*h N)^2-sin (h N/2)^2))*endpoint N n`.

Article: chebyshev1, Theorem E.3 via `chebyshev1.SineJacobi.endpoint_second_difference`.

Proof: Rewrite the definitions and library identities explicitly named in the proof, then
discharge the resulting algebraic or order relation.
-/
theorem endpoint_recurrence (N n : ℕ) :
    endpoint N (n+2) = 2*endpoint N (n+1) - 4*(data N).aSq (n+1)*endpoint N n := by
  have he : ((data N).leading (n+2)).eval 1 =
      ((data N).leading (n+1)).eval 1 -
        (data N).aSq (n+1)*((data N).leading n).eval 1 := by
    simp [JacobiData.leading, JacobiData.block]
  simp only [endpoint, he, pow_succ]
  ring

/--
The exact second-difference equation appearing in E.3.

Exact identity `endpoint N (n+2)-2*endpoint N (n+1)+endpoint N n = -(sin (h N/2)^2 / (sin
(((n+1:ℕ):ℝ)*h N)^2-sin (h N/2)^2))*endpoint N n`.

Use: `chebyshev1.SineJacobi.endpoint_second_difference_nonpos` rewrites with this identity
to prove the bound `endpoint N (n+2)-2*endpoint N (n+1)+endpoint N n ≤
0`.

Article: chebyshev1, Theorem E.3.

Proof: Clear the denominators using the available nonzero hypotheses, then verify the remaining
algebraic identity.
-/
theorem endpoint_second_difference (N n : ℕ) (hn : n+1 < N) :
    endpoint N (n+2)-2*endpoint N (n+1)+endpoint N n =
      -(sin (h N/2)^2 /
        (sin (((n+1:ℕ):ℝ)*h N)^2-sin (h N/2)^2))*endpoint N n := by
  -- Clear the denominators using the available nonzero hypotheses, then verify the remaining
  -- algebraic identity.
  have hs : 0 < n+1 := by omega
  rw [endpoint_recurrence, data_aSq N (n+1) hs hn]
  have hc := couplingSq_sub_quarter N (n+1) hs hn
  have h4 : 4*couplingSq N (n+1)-1 =
      sin (h N/2)^2/(sin (((n+1:ℕ):ℝ)*h N)^2-sin (h N/2)^2) := by
    calc
      _ = 4*(couplingSq N (n+1)-1/4) := by ring
      _ = _ := by rw [hc]; field_simp
  rw [← h4]
  ring

/--
The stated quantitative bound `endpoint N (n+2)-2*endpoint N (n+1)+endpoint N n ≤ 0`.

Use: `chebyshev1.SineJacobi.endpoint_midpoint_control` uses this bound to establish the
stated quantitative bound `endpoint N s ≤ 3*endpoint N (N/2)`.

Article: chebyshev1, Theorem E.3 via `chebyshev1.SineJacobi.endpoint_global_bound`.

Proof: Use the identities/estimates `chebyshev1.SineJacobi.endpoint_second_difference`,
`chebyshev1.SineJacobi.coupling_den_eq`, `chebyshev1.SineJacobi.coupling_den_pos` with
the arguments shown in the proof.
-/
theorem endpoint_second_difference_nonpos (N n : ℕ) (hn : n+1 < N) :
    endpoint N (n+2)-2*endpoint N (n+1)+endpoint N n ≤ 0 := by
  rw [endpoint_second_difference N n hn]
  have hd : 0 < sin (((n+1:ℕ):ℝ)*h N)^2-sin (h N/2)^2 := by
    rw [← coupling_den_eq]
    exact coupling_den_pos N (n+1) (by omega) hn
  exact mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (div_nonneg (sq_nonneg _) hd.le))
    (endpoint_pos N n (by omega)).le

end
end chebyshev1.SineJacobi
