import jacobi.Applications.NesterovSums
import jacobi.Counterexample.UFamily
import chebyshev2.Finite.Gain

/-!
Article: jacobi, Theorem 5.1.
The displayed uniform U Jacobi chain is constructed with its actual
finite coefficient extension. Every principal continuant, resolvent
diagonal and finite energy is evaluated with the original normalization.
Use: UniformBlockGain computes the sharp gain of the canonical even-horizon
Nesterov blocks and supplies the upper candidate in BlockComparison.
-/
namespace jacobi.Applications
noncomputable section
open chebyshev1 chebyshev2 Polynomial Polynomial.Chebyshev Matrix jacobi.Finite
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

/-- The literal uniform U chain, with zero diagonal and every actual off-diagonal entry one half.
Use: uniformU_block evaluates all of its original monic continuants and uniformU_energy evaluates its genuine inverse energy.
Article: jacobi, Theorem 5.1.
-/
def uniformUChain (m:ℕ) : Jacobi m where
  data.b _ := 0
  data.aSq i := if 0 < i ∧ i < m then 1/4 else 0
  coupling_nonneg i := by dsimp; split_ifs <;> norm_num
  coupling_zero := by simp
  diagonal_tail _ _ := rfl
  coupling_tail i hi := by simp [not_lt.mpr hi]

/-- Every genuine principal block of the uniform U chain has exactly the monic second-kind Chebyshev continuant.
Use: its full characteristic polynomial fixes the original U fibre; its two complementary blocks give the exact source resolvent diagonal.
Article: jacobi, Theorem 5.1.
Proof: the two initial continuants and the positive-interior coupling one quarter give the ordinary Chebyshev recurrence. Normalize its exact two-step identity by powers of one half. -/
theorem uniformU_block (m r n:ℕ) (hn:r+n≤m) :
    (uniformUChain m).data.block r n=C ((1/2:ℝ)^n)*U ℝ (n:ℤ) := by
  -- Incoming boundary couplings do not enter the actual block determinant recurrence.
  induction n using Nat.twoStepInduction with
  | zero => simp [JacobiData.block]
  | one =>
    apply Polynomial.funext
    intro x
    simp [JacobiData.block,uniformUChain]
  | more n h0 h1 =>
    rw [JacobiData.block,h0 (by omega),h1 (by omega)]
    have hc : (uniformUChain m).data.aSq (r+n+1)=1/4 := by
      simp [uniformUChain,show 0<r+n+1 ∧ r+n+1<m by omega]
    rw [hc]
    simp only [uniformUChain,map_zero,sub_zero]
    rw [show ((n+2:ℕ):ℤ)=(n:ℤ)+2 by omega,U_add_two]
    apply Polynomial.funext
    intro x
    simp only [eval_sub,eval_mul,eval_C,eval_X,eval_ofNat,pow_succ]
    rw [show (n:ℤ)+1=((n+1:ℕ):ℤ) by omega]
    ring

/-- The genuine original full uniform U chain belongs to precisely the prescribed half-integer Jacobi fibre.
Use: its exact finite energy is an admissible upper candidate in the full block-class optimum.
Article: jacobi, Theorem 5.1.
Proof: all true couplings are strictly positive, and the actual full matrix characteristic polynomial equals its monic continuant, which is the already identified U node polynomial. -/
theorem uniformU_inFiber (m:ℕ) : InFiber (uniformUChain m)
    (jacobi.Jacobi.nodes (1/2) (1/2) (by norm_num) (by norm_num) m).polynomial := by
  constructor
  · intro i hi him
    simp [uniformUChain,show 0 < i ∧ i < m from ⟨hi,him⟩]
  · change ((uniformUChain m).data.matrix 0 m).charpoly=_
    rw [← JacobiData.block_eq_charpoly _ (uniformUChain m).coupling_nonneg 0 m,
      uniformU_block m 0 m (by omega),jacobi.Counterexample.u_base_polynomial]

/-- The true resolvent diagonal of the uniform U chain has its exact finite cofactor value.
Use: uniformU_energy evaluates its original sum of squared diagonal entries; UniformBlockGain then evaluates the complete spectral gain.
Article: jacobi, Theorem 5.1.
Proof: apply the previously proved genuine diagonal cofactor formula, substitute the three exact Chebyshev block values at one, and cancel their positive powers of one half. -/
theorem uniformU_green (m:ℕ) (i:Fin m) :
    (uniformUChain m).green i i=2*((i:ℝ)+1)*((m:ℝ)-i)/((m:ℝ)+1) := by
  -- All three continuants are the actual complementary principal determinants of this same original inverse.
  have hm : 0<m := Nat.zero_lt_of_lt i.isLt
  rw [Jacobi.green_diagonal _ hm]
  simp only [JacobiData.leading]
  rw [
    uniformU_block m 0 i.val (by omega),uniformU_block m (i.val+1) (m-(i.val+1)) (by omega),
    uniformU_block m 0 m (by omega)]
  simp only [eval_mul,eval_C,U_eval_one,Int.cast_natCast]
  have hpow : (1/2:ℝ)^i.val*(1/2:ℝ)^(m-(i.val+1))=2*(1/2:ℝ)^m := by
    rw [← pow_add,show i.val+(m-(i.val+1))=m-1 by omega]
    have hm : m=m-1+1 := by omega
    conv_rhs => rw [hm,pow_succ]
    ring
  rw [show (1/2:ℝ)^i.val*((i.val:ℝ)+1)*((1/2:ℝ)^(m-(i.val+1))*((m-(i.val+1):ℕ)+1))=
    ((1/2:ℝ)^i.val*(1/2:ℝ)^(m-(i.val+1)))*((i.val:ℝ)+1)*((m-(i.val+1):ℕ)+1) by ring,hpow]
  rw [Nat.cast_sub (by omega : i.val+1≤m)]
  push_cast
  field_simp
  ring

/-- The actual finite U-chain energy has exactly the article's cubic expression and reciprocal correction.
Use: computes the canonical block gain and its optimal leading constant without a numerical premise.
Article: jacobi, Theorem 5.1.
Proof: square the genuine cofactor formula, turn the full finite index sum into its original natural range, and apply the exact fifth-degree endpoint-weight sum. -/
theorem uniformU_energy (m:ℕ) :
    (uniformUChain m).energy=(2/15:ℝ)*(((m:ℝ)+1)^3-1/((m:ℝ)+1)) := by
  -- The discrete-antiderivative sum retains the complete finite correction, including the empty-chain convention.
  unfold Jacobi.energy
  simp_rw [uniformU_green]
  rw [Fin.sum_univ_eq_sum_range (f := fun i:ℕ => (2*((i:ℝ)+1)*((m:ℝ)-i)/((m:ℝ)+1))^2)]
  have he : (∑ i∈Finset.range m,(2*((i:ℝ)+1)*((m:ℝ)-i)/((m:ℝ)+1))^2)=
      4/((m:ℝ)+1)^2*∑ i∈Finset.range m,((i:ℝ)+1)^2*((m:ℝ)-i)^2 := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    field_simp
    ring
  rw [he,nesterov_endpoint_sum]
  field_simp
  ring

end
end jacobi.Applications
