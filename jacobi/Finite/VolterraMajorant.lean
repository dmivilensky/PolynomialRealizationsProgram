import jacobi.Finite.VolterraBinomial

/-!
Article: jacobi, Appendix C.3 (discrete Volterra equation and cosh estimates).
The exact positive polynomial majorant for the original weighted linear
Volterra kernel. It has the genuine finite recurrence and terminates
automatically by the actual binomial zeros.
Use: linear_majorant_recurrence and linear_majorant_bound give the full factorial/cosh estimate for genuine support waves.
-/
namespace jacobi.Finite
noncomputable section
open Finset

/-- The exact original finite polynomial majorant of a positive linear Volterra kernel on a fixed finite prefix.
Use: linear_majorant_recurrence and linear_majorant_bound give the full factorial/cosh estimate for genuine support waves.
Article: jacobi, Appendix C.3 (discrete Volterra equation and cosh estimates).
-/
def linearMajorant (M : ℕ) (a : ℝ) (m : ℕ) : ℝ :=
  ∑k∈range (M+1),a^k*((m+k).choose (2*k):ℝ)

/-- The exact finite binomial majorant satisfies the original linear-kernel Volterra equation on its entire actual prefix.
Use: linear_majorant_bound compares arbitrary genuine triangular norm inequalities with this actual explicit positive majorant.
Article: jacobi, Appendix C.3 (discrete Volterra equation and cosh estimates).
Proof: interchange the two genuine finite sums and apply the exact proved binomial kernel integral. The original zero-degree term is one and the final unused iterate is genuinely zero by its actual binomial index. -/
theorem linear_majorant_recurrence (M m : ℕ) (a : ℝ) (hm:m≤M) :
    linearMajorant M a m=1+a*∑j∈range m,((m-j:ℕ):ℝ)*linearMajorant M a j := by
  -- Finite binomial zeros discharge the last iterate; no infinite formal power series is used.
  have hs : a*(∑j∈range m,((m-j:ℕ):ℝ)*linearMajorant M a j)=
      ∑k∈range (M+1),a^(k+1)*((m+(k+1)).choose (2*(k+1)):ℝ) := by
    simp only [linearMajorant,mul_sum]
    rw [sum_comm]
    apply sum_congr rfl
    intro k hk
    calc
      _ = a^(k+1)*∑j∈range m,((m-j:ℕ):ℝ)*((j+k).choose (2*k):ℝ) := by
        rw [mul_sum]
        apply sum_congr rfl
        intro j hj
        rw [pow_succ]
        ring
      _ = _ := by
        rw [linear_kernel_choose]
        congr 2
  rw [hs]
  have hz : a^(M+1)*((m+(M+1)).choose (2*(M+1)):ℝ)=0 := by
    rw [Nat.choose_eq_zero_of_lt (show m+(M+1)<2*(M+1) by omega),Nat.cast_zero,mul_zero]
  rw [sum_range_succ (fun k => a^(k+1)*((m+(k+1)).choose (2*(k+1)):ℝ)) M,hz,add_zero]
  rw [linearMajorant,sum_range_succ']
  simp only [Nat.mul_zero,Nat.choose_zero_right,Nat.cast_one,pow_zero,mul_one]
  ring

/-- Every actual finite-prefix triangular inequality with the genuine positive linear kernel is bounded by the same exact finite binomial majorant.
Use: linear_volterra_cosh combines this actual finite comparison with the community binomial and hyperbolic-cosine series bounds.
Article: jacobi, Appendix C.3 (discrete Volterra equation and cosh estimates).
Proof: strong induction on the actual original row compares every earlier value in the genuine finite sum; the proved exact majorant recurrence closes the same original inequality. -/
theorem linear_majorant_bound {v : ℕ→ℝ} {C a : ℝ} (ha:0≤a) (M : ℕ)
    (hv:∀j≤M,v j≤C+a*∑k∈range j,((j-k:ℕ):ℝ)*v k) :
    v M≤C*linearMajorant M a M := by
  -- Only the genuine original finite row prefix is used by the induction hypothesis.
  have hall : ∀j≤M,v j≤C*linearMajorant M a j := by
    intro j
    induction j using Nat.strong_induction_on with
    | h j ih =>
      intro hj
      calc
        v j≤C+a*∑k∈range j,((j-k:ℕ):ℝ)*v k := hv j hj
        _ ≤ C+a*∑k∈range j,((j-k:ℕ):ℝ)*(C*linearMajorant M a k) := by
          apply add_le_add le_rfl
          apply mul_le_mul_of_nonneg_left _ ha
          apply sum_le_sum
          intro k hk
          have hkj := mem_range.mp hk
          exact mul_le_mul_of_nonneg_left (ih k hkj (by omega)) (Nat.cast_nonneg _)
        _ = C*linearMajorant M a j := by
          rw [linear_majorant_recurrence M j a hj]
          simp only [mul_add,mul_one,mul_sum]
          ring
  exact hall M le_rfl

end
end jacobi.Finite
