import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Tactic

/-!
Article: jacobi, Appendix C.3 (complex edge-wave convergence).
A finite-prefix discrete Gronwall inequality with no conditions beyond
the prefix being estimated. This is used for genuine weighted support
waves and the discrete-to-continuum error equation.
Source: discrete Gronwall inequality, proved here in the needed finite-prefix form.
Use: weighted_volterra_bound applies it to actual support-wave norms; the actual support edge limit applies the same bound to its discrete approximation error.
-/
namespace jacobi.Finite
noncomputable section
open Real Finset

/-- A genuine finite-prefix triangular sum inequality has the classical exponential Gronwall bound, without any assumptions on an unused sequence tail.
Use: weighted_volterra_bound applies it to actual support-wave norms; the actual support edge limit applies the same bound to its discrete approximation error.
Article: jacobi, Appendix C.3 (complex edge-wave convergence).
Source: discrete Gronwall inequality.
Proof: the original majorant W_j=C+a*sum_(k<j)v_k satisfies W_(j+1)<= (1+a)*W_j on the actual finite prefix. Induct to get its exact geometric bound, then use 1+a<=exp(a) and multiply by the original nonnegative constant. -/
theorem prefix_gronwall {v : ℕ→ℝ} {C a : ℝ} (hC:0≤C) (ha:0≤a) (M : ℕ)
    (hv:∀j≤M,v j≤C+a*∑k∈range j,v k) :
    v M≤C*exp (a*(M:ℝ)) := by
  -- The recurrence of the actual finite majorant is used only at original indices already controlled by the hypothesis.
  have hmajor : ∀j≤M,C+a*∑k∈range j,v k≤C*(1+a)^j := by
    intro j
    induction j with
    | zero => intro _; simp
    | succ j ih =>
      intro hj
      have hprev := ih (by omega)
      have hpoint := hv j (by omega)
      rw [sum_range_succ]
      calc
        _ = (C+a*∑k∈range j,v k)+a*v j := by ring
        _ ≤ (C+a*∑k∈range j,v k)+a*(C+a*∑k∈range j,v k) :=
          add_le_add le_rfl (mul_le_mul_of_nonneg_left hpoint ha)
        _ = (1+a)*(C+a*∑k∈range j,v k) := by ring
        _ ≤ (1+a)*(C*(1+a)^j) := mul_le_mul_of_nonneg_left hprev (by positivity)
        _ = _ := by rw [pow_succ]; ring
  have hp : (1+a)^M≤(exp a)^M := pow_le_pow_left₀ (by positivity)
    (by simpa only [add_comm] using Real.add_one_le_exp a) M
  have he : (exp a)^M=exp (a*(M:ℝ)) := by rw [← Real.exp_nat_mul]; congr 1; ring
  exact (hv M le_rfl).trans ((hmajor M le_rfl).trans
    (mul_le_mul_of_nonneg_left (by rwa [he] at hp) hC))

end
end jacobi.Finite
