import bezout.Channel.Roots.Actual
import bezout.Channel.Roots.Interior
import bezout.Comparisons.Classical.Gains

/-!
Article: bezout, Proposition D.1, endpoint and interior profile estimates.
Use: the estimates concern the actual LF/root and Prefix histories, at every
valid horizon. Their explicit bulk constants are independent of the horizon.
Proof: exact omitted-factor energies, the sine bound for U, and the actual
Prefix response-query factorization.
-/

namespace bezout.Comparisons.RootAsymptotics
noncomputable section
open Polynomial Polynomial.Chebyshev
open scoped BigOperators

/-- The common positive physical squared scale in all first variations. -/
def scaleSq (I : chebyshev1.SpectralInterval) (N : ℕ) : ℝ :=
  (2*I.epsilon N/I.delta)^2

/-- The physical scale never vanishes, even though it decays with the horizon. -/
theorem scaleSq_pos (I : chebyshev1.SpectralInterval) (N : ℕ) : 0<scaleSq I N := by
  have he : 0<I.epsilon N := one_div_pos.mpr (I.den_pos N)
  have hd := I.delta_pos
  unfold scaleSq
  positivity

/-- An explicit, horizon-independent Prefix bulk constant. -/
def prefixInteriorConstant (x : ℝ) : ℝ := 4/(1-x^2)

/-- Every actual root-ordering profile has only quadratic energy at a fixed interior mode. -/
theorem root_interior_energy (I : chebyshev1.SpectralInterval) (N : ℕ)
    (e : Equiv.Perm (Fin N)) {lam : ℝ} (hlam : |I.z lam|<1) :
    Lower.physicalKernelSq (Channel.Roots.history (Channel.Roots.steps I N e)) lam lam≤
      scaleSq I N*Channel.Roots.interiorConstant (I.z lam)*(N:ℝ)^2 := by
  unfold Lower.physicalKernelSq
  simp only [pow_two]
  rw [Channel.Roots.history_crossEnergy]
  simpa only [Channel.Roots.schedule_eq_extend,scaleSq,pow_two] using
    Channel.Roots.diagonalEnergy_interior_le _ I N
      (Channel.Roots.schedule_finalExact I N e) hlam

/-- Prefix's physical kernel after cancellation of its query normalization. -/
theorem prefix_kernel (I : chebyshev1.SpectralInterval) (N : ℕ) (hN : 0<N)
    (s : Fin N) (x y : ℝ) :
    Lower.physicalKernel (Classical.history I N) s x y =
      (-4*I.epsilon N/I.delta)*Classical.initialWeight s*
      (U ℝ ((N-1-s.val:ℕ):ℤ)).eval (I.z x)*(T ℝ s.val).eval (I.z y) := by
  rw [Lower.physicalKernel,Classical.response_eval I N hN,Classical.query_eval]
  field_simp [I.den_ne s]

/-- The exceptional Prefix startup weight is bounded by one. -/
theorem prefix_initialWeight_le (s : ℕ) : Classical.initialWeight s≤1 := by
  unfold Classical.initialWeight
  split_ifs <;> norm_num

/-- At a strict interior mode every actual Prefix insertion is uniformly bounded. -/
theorem prefix_interior_kernel (I : chebyshev1.SpectralInterval) (N : ℕ) (hN : 0<N)
    (s : Fin N) {lam : ℝ} (hlam : |I.z lam|<1) :
    |Lower.physicalKernel (Classical.history I N) s lam lam|≤
      (4*I.epsilon N/I.delta)/Real.sqrt (1-(I.z lam)^2) := by
  have hw := Classical.initialWeight_pos s
  have hc : 0<4*I.epsilon N/I.delta := by
    have he : 0<I.epsilon N := one_div_pos.mpr (I.den_pos N)
    have hd := I.delta_pos
    positivity
  have hs := Real.sqrt_pos.mpr (Channel.Roots.interior_sine_pos hlam)
  have hu := (le_div_iff₀ hs).mpr
    (Channel.Roots.abs_U_interior_mul_sine ((N-1-s.val:ℕ):ℤ) hlam)
  have ht := abs_eval_T_real_le_one (s.val:ℤ) hlam.le
  rw [prefix_kernel I N hN,abs_mul,abs_mul,abs_mul,
    show |-4*I.epsilon N/I.delta|=4*I.epsilon N/I.delta by
      rw [show -4*I.epsilon N/I.delta= -(4*I.epsilon N/I.delta) by ring,
        abs_neg,abs_of_pos hc],abs_of_pos hw]
  calc
    _ ≤ (4*I.epsilon N/I.delta)*1*(1/Real.sqrt (1-(I.z lam)^2))*1 := by
      gcongr
      exact prefix_initialWeight_le s
    _ = _ := by ring

/-- The complete actual Prefix profile has only linear energy at fixed interior modes. -/
theorem prefix_interior_energy (I : chebyshev1.SpectralInterval) (N : ℕ) (hN : 0<N)
    {lam : ℝ} (hlam : |I.z lam|<1) :
    Lower.physicalKernelSq (Classical.history I N) lam lam≤
      scaleSq I N*prefixInteriorConstant (I.z lam)*(N:ℝ) := by
  have hs := Channel.Roots.interior_sine_pos hlam
  have hc : 0≤(4*I.epsilon N/I.delta)/Real.sqrt (1-(I.z lam)^2) := by
    have he : 0<I.epsilon N := one_div_pos.mpr (I.den_pos N)
    have hd := I.delta_pos
    positivity
  calc
    _ ≤ ∑ _s : Fin N, ((4*I.epsilon N/I.delta)/Real.sqrt (1-(I.z lam)^2))^2 := by
      apply Finset.sum_le_sum
      intro s _
      simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg _) hc).mpr
        (prefix_interior_kernel I N hN s hlam)
    _ = _ := by
      simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]
      unfold scaleSq prefixInteriorConstant
      rw [div_pow,Real.sq_sqrt hs.le]
      ring

/-- The actual lower-endpoint Prefix profile has its exact cubic shape energy. -/
theorem prefix_endpoint_energy (I : chebyshev1.SpectralInterval) (N : ℕ) (hN : 0<N) :
    Lower.physicalKernelSq (Classical.history I N) I.mu I.mu =
      scaleSq I N*chebyshev1.Prefix.shape N := by
  obtain ⟨n,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : N≠0)
  unfold Lower.physicalKernelSq
  simp_rw [Classical.physicalKernel_eq_prefix I (n+1) (by omega)]
  rw [Fin.sum_univ_eq_sum_range
    (fun s => ((chebyshev1.Prefix.realization I).kernel (n+1) s I.mu I.mu)^2),
    chebyshev1.Prefix.endpoint_square_sum]
  unfold scaleSq chebyshev1.SpectralInterval.epsilon
  ring

/-- At even horizons the two actual endpoint Prefix profiles are negatives. -/
theorem prefix_endpoint_neg (I : chebyshev1.SpectralInterval) (N : ℕ) (hN : 0<N)
    (hEven : Even N) (s : Fin N) :
    Lower.physicalKernel (Classical.history I N) s I.L I.L =
      -Lower.physicalKernel (Classical.history I N) s I.mu I.mu := by
  rw [prefix_kernel I N hN,prefix_kernel I N hN,Channel.Roots.z_upper,I.z_mu,
    U_eval_neg_one,T_eval_neg_one,U_eval_one,T_eval_one]
  simp only [Int.cast_natCast,Int.cast_negOnePow_natCast,mul_one]
  have hexp : N-1-s.val+s.val=N-1 := by omega
  have hOdd : Odd (N-1) := by
    rcases hEven with ⟨m,hm⟩
    exact ⟨m-1,by omega⟩
  have hp : (-1:ℝ)^(N-1-s.val)*(-1:ℝ)^s.val= -1 := by
    rw [← pow_add,hexp,hOdd.neg_one_pow]
  calc
    _ = ((-4*I.epsilon N/I.delta)*Classical.initialWeight s*
      (((N-1-s.val:ℕ):ℝ)+1))*((-1:ℝ)^(N-1-s.val)*(-1:ℝ)^s.val) := by ring
    _ = _ := by rw [hp]; ring

end
end bezout.Comparisons.RootAsymptotics
