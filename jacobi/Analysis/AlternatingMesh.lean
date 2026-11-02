import jacobi.Analysis.QuadraticError
import Mathlib.Data.Nat.Init

/-!
Article: jacobi, Appendix C.4 (uniform Cholesky limit).
Adjacent-pair cancellation controls the entire finite alternating sum
by the neighbor modulus and one bounded leftover endpoint term.
Use: compact-family GL cross-edge mesh sums vanish uniformly after division by the true growing matrix dimension.
-/
namespace jacobi.Analysis
noncomputable section

/-- The absolute alternating prefix sum is bounded by the number of
complete adjacent pairs times the neighbor oscillation, plus one
uniform endpoint bound, with both parity cases included.
Use: compact-family GL cross-edge mesh sums vanish uniformly after
division by the true growing matrix dimension.
Article: jacobi, Appendix C.4 (uniform Cholesky limit).
Proof: use induction in steps of two. Each new adjacent pair is
(-1)^m*(f_m-f_(m+1)), whose actual absolute value is at most delta.
The even base is zero and the odd base is the single bounded endpoint. -/
theorem alternating_sum_bound (f:ℕ→ℝ) {B δ:ℝ} (hB:0≤B)
    (m:ℕ) (hb:∀j<m, |f j|≤B) (hd:∀j, j+1<m → |f j-f (j+1)|≤δ) :
    |∑ j∈Finset.range m, (-1:ℝ)^j*f j|≤(m/2:ℕ)*δ+B := by
  -- Adding two coordinates contributes one bounded adjacent difference, regardless of parity.
  induction m using Nat.twoStepInduction with
  | zero => simpa using hB
  | one => simpa using hb 0 (by omega)
  | more m ih _ =>
    have hm := ih (fun j hj => hb j (by omega)) (fun j hj => hd j (by omega))
    have he : (∑ j∈Finset.range (m+2), (-1:ℝ)^j*f j)=
        (∑ j∈Finset.range m, (-1:ℝ)^j*f j)+(-1:ℝ)^m*(f m-f (m+1)) := by
      simp only [Finset.sum_range_succ,pow_succ]
      ring
    rw [he]
    have hpair : |(-1:ℝ)^m*(f m-f (m+1))|≤δ := by
      simpa only [abs_mul,abs_pow,abs_neg,abs_one,one_pow,one_mul] using hd m (by omega)
    have hcount : (m+2)/2=m/2+1 := by omega
    rw [hcount,Nat.cast_add,Nat.cast_one]
    exact (abs_add_le _ _).trans (by nlinarith)

end
end jacobi.Analysis
