import Mathlib.Tactic

/-!
Article: jacobi, Theorem 5.1.
The original insertion-weight sum has its exact fifth-degree expression.
Use: NesterovGain and the uniform U block energy evaluate the genuine
finite sums, retaining both finite-horizon corrections and leading constants.
Source: finite polynomial summation by a discrete antiderivative.
-/
namespace jacobi.Applications
noncomputable section

/-- The exact finite sum of the squared endpoint propagation weights.
Use: evaluates the original Nesterov gain and the uniform U-chain cofactor energy.
Article: jacobi, Theorem 5.1.
Proof: the displayed polynomial primitive is the combination (k+1)^2*S_2-2*(k+1)*S_3+S_4 of the usual power-sum primitives. Its finite difference is the actual summand. Telescope and evaluate the two endpoints by ring arithmetic. -/
theorem nesterov_endpoint_sum (k:ℕ) :
    (∑ s∈Finset.range k,((s:ℝ)+1)^2*((k:ℝ)-s)^2)=(((k:ℝ)+1)^5-((k:ℝ)+1))/30 := by
  -- One exact discrete antiderivative proves all horizons, including the empty sum.
  let P : ℝ→ℝ := fun j => j*(j+1)/30*(5*((k:ℝ)+1)^2*(2*j+1)-
    15*((k:ℝ)+1)*j*(j+1)+(2*j+1)*(3*j^2+3*j-1))
  have hd (s:ℕ) : ((s:ℝ)+1)^2*((k:ℝ)-s)^2=P ((s+1:ℕ):ℝ)-P s := by
    dsimp [P]
    push_cast
    ring
  simp_rw [hd]
  rw [Finset.sum_range_sub (fun s:ℕ => P (s:ℝ)) k]
  dsimp [P]
  ring

end
end jacobi.Applications
