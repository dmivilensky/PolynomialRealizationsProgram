import bezout.Comparisons.Competitors.Prefix
import bezout.Comparisons.Competitors.Sine
import bezout.Comparisons.Classical.Gains
import bezout.Balanced.Gains

/-!
Article: bezout, Equation `eq:experiment-endpoint-transfer`.
Use: Prefix, sine--Jacobi and Balanced have one common temporal direction at
both spectral endpoints, and that direction attains their full spectral gain.
Proof: zero-diagonal continuants and stopped parity sums have their stated
parity; the established endpoint maximum principles identify the norm.
-/

namespace bezout.Comparisons.Competitors
noncomputable section
open chebyshev1 Polynomial Polynomial.Chebyshev
open scoped BigOperators

/-- The upper physical endpoint is minus one in the spectral chart. -/
theorem z_upper (I : SpectralInterval) : I.z I.L = -1 := by
  unfold SpectralInterval.z SpectralInterval.delta
  field_simp [sub_ne_zero.mpr I.mu_lt_L.ne']
  ring

/-- A zero-diagonal Jacobi continuant has the parity of its block length. -/
theorem block_parity (J : JacobiData) (hb : ∀ s, J.b s=0) (a n : ℕ) (x : ℝ) :
    (J.block a n).eval (-x)=(-1:ℝ)^n*(J.block a n).eval x := by
  induction n using Nat.twoStepInduction with
  | zero => simp [JacobiData.block]
  | one => simp [JacobiData.block,hb]
  | more n ih ih1 =>
    simp only [JacobiData.block,eval_sub,eval_mul,eval_X,eval_C,hb,sub_zero,ih,ih1,
      pow_succ]
    ring

/-- The two diagonal endpoint time profiles of a zero-diagonal Jacobi method
agree up to a single global sign, independent of the physical call. -/
theorem jacobi_endpoint_profile (J : JacobiData) (I : SpectralInterval) (N : ℕ)
    (ha : J.Admissible I N) (hb : ∀ s, J.b s=0) (s : Fin N) :
    (J.realization I).kernel N s.val I.L I.L=
      (-1:ℝ)^(N-1)*(J.realization I).kernel N s.val I.mu I.mu := by
  rw [J.kernel_eq I ha s.val s.isLt,J.kernel_eq I ha s.val s.isLt,z_upper I,I.z_mu]
  change -(2/(I.delta*J.den I N))*(J.block (s.val+1) (N-(s.val+1))).eval (-1)*
      (J.block 0 s.val).eval (-1)=_
  rw [block_parity J hb _ _ 1,block_parity J hb _ _ 1]
  have he : N-(s.val+1)+s.val=N-1 := by omega
  rw [← he,pow_add]
  unfold JacobiData.leading
  ring

namespace Prefix
/-- The literal Prefix execution has the common signed endpoint profile. -/
theorem endpoint_profile (I : SpectralInterval) (N : ℕ) (hN : 0<N) (s : Fin N) :
    bezout.Lower.physicalKernel (history I N) s I.L I.L=
      (-1:ℝ)^(N-1)*bezout.Lower.physicalKernel (history I N) s I.mu I.mu := by
  rw [history_eq_classical,bezout.Classical.physicalKernel_eq_prefix I N hN,
    bezout.Classical.physicalKernel_eq_prefix I N hN,← chebyshev1.Prefix.jacobi_realization]
  exact jacobi_endpoint_profile _ I N (chebyshev1.Prefix.jacobi_admissible I N)
    chebyshev1.Prefix.jacobiData_b s

/-- The actual Prefix gain is attained by its lower-endpoint time profile. -/
theorem gain_endpoint (I : SpectralInterval) (N : ℕ) (hN : 0<N) :
    (history I N).spectralGain I=Real.sqrt (bezout.Lower.physicalKernelSq (history I N) I.mu I.mu) := by
  rw [history_eq_classical,bezout.Classical.spectralGain_eq_prefix I N hN,
    chebyshev1.Prefix.gain_eq_endpoint]
  rw [← bezout.History.realization_kernelNorm]
  unfold Realization.kernelNorm
  congr 1
  apply Finset.sum_congr rfl
  intro s hs
  rw [(bezout.Classical.history I N).realization_kernel ⟨s,Finset.mem_range.mp hs⟩]
  exact congrArg (fun t : ℝ => t^2)
    (bezout.Classical.physicalKernel_eq_prefix I N hN ⟨s,Finset.mem_range.mp hs⟩ I.mu I.mu).symm
end Prefix

namespace Sine
/-- The literal sine--Jacobi execution has the same global endpoint parity. -/
theorem endpoint_profile (I : SpectralInterval) (N : ℕ) (hN : 0<N) (s : Fin N) :
    bezout.Lower.physicalKernel (history I N) s I.L I.L=
      (-1:ℝ)^(N-1)*bezout.Lower.physicalKernel (history I N) s I.mu I.mu := by
  change ((history I N).response s).eval I.L*((history I N).query s).eval I.L=_
  rw [← bezout.History.realization_kernel,realization_kernel I N hN]
  change _=(-1:ℝ)^(N-1)*(((history I N).response s).eval I.mu*((history I N).query s).eval I.mu)
  rw [← bezout.History.realization_kernel,realization_kernel I N hN]
  exact jacobi_endpoint_profile _ I N (SineJacobi.admissible I N hN) (SineJacobi.data_b N) s

/-- The actual sine gain is the norm of its common endpoint time profile. -/
theorem gain_endpoint (I : SpectralInterval) (N : ℕ) (hN : 0<N) :
    (history I N).spectralGain I=Real.sqrt (bezout.Lower.physicalKernelSq (history I N) I.mu I.mu) := by
  rw [gain_eq I N hN,SineJacobi.gain_eq_endpoint I N hN,← bezout.History.realization_kernelNorm]
  unfold Realization.kernelNorm
  congr 1
  apply Finset.sum_congr rfl
  intro s hs
  rw [realization_kernel I N hN ⟨s,Finset.mem_range.mp hs⟩]
end Sine

namespace BalancedEndpoints
/-- The stopped query polynomial keeps exactly its degree parity. -/
theorem psi_parity (N s : ℕ) (x : ℝ) :
    (Balanced.psi N s).eval (-x)=(-1:ℝ)^s*(Balanced.psi N s).eval x := by
  induction s using Nat.twoStepInduction with
  | zero => simp
  | one => simp [T_one]
  | more s ih _ =>
    rw [Balanced.psi_add_two]
    simp only [eval_add,eval_mul,eval_sub,eval_C,T_eval_neg,
      Int.negOnePow_add,Int.cast_negOnePow_natCast,ih,pow_succ]
    norm_num
    ring

/-- Equal parity is precisely what is needed for a real minus-one power. -/
theorem sign_eq_of_mod {a b : ℕ} (h : a%2=b%2) : (-1:ℝ)^a=(-1:ℝ)^b := by
  exact (neg_one_pow_eq_pow_mod_two a).trans ((congrArg (fun n : ℕ => (-1:ℝ)^n) h).trans (neg_one_pow_eq_pow_mod_two b).symm)

/-- Every term in a reverse parity tail has one common response parity. -/
theorem tail_parity (N s r : ℕ) (hs : s<N) (hp : s%2=r%2) (x : ℝ) :
    (Balanced.tail N r).eval (-x)=(-1:ℝ)^(N-1-s)*(Balanced.tail N r).eval x := by
  simp only [Balanced.tail,eval_finsetSum,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro t ht
  by_cases hc : r≤t ∧ r%2=t%2
  · rw [ite_eq_left hc]
    simp only [Balanced.originalFactor,eval_mul,eval_C,U_eval_neg,
      Int.cast_negOnePow_natCast]
    have he : (N-1-t)%2=(N-1-s)%2 := by have := Finset.mem_range.mp ht; omega
    rw [sign_eq_of_mod he]
    ring
  · simp [hc]

/-- The full stopped response factor has the remaining-degree parity. -/
theorem factor_parity (N s : ℕ) (hs : s<N) (x : ℝ) :
    (Balanced.factor N s).eval (-x)=(-1:ℝ)^(N-1-s)*(Balanced.factor N s).eval x := by
  simp only [Balanced.factor,eval_sub,eval_mul,eval_C,tail_parity N s s hs rfl,
    tail_parity N s (s+2) hs (by omega)]
  ring

/-- Balanced's two diagonal endpoint time profiles agree up to the same global sign. -/
theorem endpoint_profile (I : SpectralInterval) (N : ℕ) (hN : 2≤N) (s : Fin N) :
    bezout.Lower.physicalKernel (Balanced.history I N hN) s I.L I.L=
      (-1:ℝ)^(N-1)*bezout.Lower.physicalKernel (Balanced.history I N hN) s I.mu I.mu := by
  unfold bezout.Lower.physicalKernel
  rw [Balanced.history_response_eval,Balanced.history_query_eval,Balanced.history_response_eval,
    Balanced.history_query_eval,z_upper I,I.z_mu,factor_parity N s.val s.isLt 1,psi_parity N s.val 1]
  have he : N-1-s.val+s.val=N-1 := by omega
  conv_rhs => lhs; rw [← he,pow_add]
  ring

/-- Balanced's actual spectral gain is attained at the common endpoint profile. -/
theorem gain_endpoint (I : SpectralInterval) (N : ℕ) (hN : 2≤N) :
    (Balanced.history I N hN).spectralGain I=
      Real.sqrt (bezout.Lower.physicalKernelSq (Balanced.history I N hN) I.mu I.mu) := by
  rw [Balanced.spectralGain_eq,Balanced.endpoint_energy,Real.sqrt_sq (bezout.Lower.linearGain_nonneg I N)]
end BalancedEndpoints

end
end bezout.Comparisons.Competitors
