import chebyshev1.Realization.StaticShift
import chebyshev1.Realization.GainBounds

/-! The endpoint lower bound uses final exactness alone. Its signed profile
requires neither positive steps nor a Jacobi representation. -/
namespace chebyshev1.Realization
noncomputable section
open scoped BigOperators
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Signed endpoint profile of an arbitrary realization. -/
def signedEndpointProfile (R : Realization ι) (I : SpectralInterval) (N s : ℕ) : ℝ :=
  -(I.delta/(2*I.epsilon N))*R.kernel N s I.mu I.mu

def signedEndpointEnergy (R : Realization ι) (I : SpectralInterval) (N : ℕ) : ℝ :=
  ∑ s ∈ Finset.range N, (R.signedEndpointProfile I N s)^2

theorem kernel_eq_signedEndpointProfile (R : Realization ι) (I : SpectralInterval)
    (N s : ℕ) :
    R.kernel N s I.mu I.mu = -(2*I.epsilon N/I.delta)*R.signedEndpointProfile I N s := by
  have he : I.epsilon N ≠ 0 := (one_div_pos.mpr (I.den_pos N)).ne'
  unfold signedEndpointProfile
  field_simp [he,I.delta_pos.ne']

/-- Final exactness forces the endpoint mass for every realization. -/
theorem signedEndpointProfile_mass (R : Realization ι) (I : SpectralInterval) (N : ℕ)
    (hexact : R.residualPolynomial N = I.residual N) :
    ∑ s ∈ Finset.range N, R.signedEndpointProfile I N s = (N:ℝ)^2 := by
  unfold signedEndpointProfile
  rw [← Finset.mul_sum, R.kernel_sum_derivative, hexact, I.residual_derivative_eval_mu]
  have he : I.epsilon N ≠ 0 := (one_div_pos.mpr (I.den_pos N)).ne'
  field_simp [he,I.delta_pos.ne']

/-- The complete energy gap, without a positivity assumption on the profile. -/
theorem signedEndpointEnergy_gap (R : Realization ι) (I : SpectralInterval) (N : ℕ)
    (hexact : R.residualPolynomial N = I.residual N) :
    (∑ s ∈ Finset.range N, (R.signedEndpointProfile I N s-(N:ℝ))^2) =
      R.signedEndpointEnergy I N-(N:ℝ)^3 := by
  have he : (∑ s ∈ Finset.range N, (R.signedEndpointProfile I N s-(N:ℝ))^2) =
      R.signedEndpointEnergy I N-2*(N:ℝ)*
        (∑ s ∈ Finset.range N, R.signedEndpointProfile I N s)+(N:ℝ)^3 := by
    simp only [sub_sq,signedEndpointEnergy,Finset.sum_add_distrib,Finset.sum_sub_distrib,
      ← Finset.sum_mul,Finset.sum_const,Finset.card_range,nsmul_eq_mul]
    rw [← Finset.mul_sum (Finset.range N) (fun s => R.signedEndpointProfile I N s) 2]
    ring
  rw [he,R.signedEndpointProfile_mass I N hexact]
  ring

theorem signedEndpointEnergy_ge_cube (R : Realization ι) (I : SpectralInterval) (N : ℕ)
    (hexact : R.residualPolynomial N = I.residual N) :
    (N:ℝ)^3 ≤ R.signedEndpointEnergy I N := by
  have h := Finset.sum_nonneg (fun s (_ : s ∈ Finset.range N) =>
    sq_nonneg (R.signedEndpointProfile I N s-(N:ℝ)))
  rw [R.signedEndpointEnergy_gap I N hexact] at h
  linarith

theorem signedEndpointEnergy_eq_cube_iff (R : Realization ι) (I : SpectralInterval) (N : ℕ)
    (hexact : R.residualPolynomial N = I.residual N) :
    R.signedEndpointEnergy I N = (N:ℝ)^3 ↔
      ∀ s < N, R.signedEndpointProfile I N s = (N:ℝ) := by
  rw [← sub_eq_zero,← R.signedEndpointEnergy_gap I N hexact]
  constructor
  · intro he s hs
    have hz := (Finset.sum_eq_zero_iff_of_nonneg (fun s (_ : s ∈ Finset.range N) =>
      sq_nonneg (R.signedEndpointProfile I N s-(N:ℝ)))).mp he s (Finset.mem_range.mpr hs)
    exact sub_eq_zero.mp (sq_eq_zero_iff.mp hz)
  · intro hflat
    apply Finset.sum_eq_zero
    intro s hs
    rw [hflat s (Finset.mem_range.mp hs),sub_self,zero_pow (by norm_num : (2:ℕ)≠0)]

theorem kernelNorm_eq_signedEndpointEnergy (R : Realization ι) (I : SpectralInterval)
    (N : ℕ) :
    R.kernelNorm N I.mu I.mu = 2*I.epsilon N/I.delta*Real.sqrt (R.signedEndpointEnergy I N) := by
  have he : (∑ s ∈ Finset.range N, (R.kernel N s I.mu I.mu)^2) =
      (2*I.epsilon N/I.delta)^2*R.signedEndpointEnergy I N := by
    unfold signedEndpointEnergy
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro s _
    rw [R.kernel_eq_signedEndpointProfile I N s]
    ring
  have hc : 0 < 2*I.epsilon N/I.delta :=
    div_pos (mul_pos (by norm_num) (one_div_pos.mpr (I.den_pos N))) I.delta_pos
  rw [kernelNorm,he,Real.sqrt_mul (sq_nonneg _),Real.sqrt_sq_eq_abs,abs_of_pos hc]

/-- Every final-exact realization has the universal lower bound, irrespective
of signs of its coefficients or of the existence of Jacobi coordinates. -/
theorem finalExact_gain_lower_bound (R : Realization ι) (I : SpectralInterval) (N : ℕ)
    (hexact : R.residualPolynomial N = I.residual N) :
    2*I.epsilon N/I.delta*Real.sqrt ((N:ℝ)^3) ≤ R.gain I N := by
  calc
    _ ≤ 2*I.epsilon N/I.delta*Real.sqrt (R.signedEndpointEnergy I N) :=
      mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt (R.signedEndpointEnergy_ge_cube I N hexact))
        (div_pos (mul_pos (by norm_num) (one_div_pos.mpr (I.den_pos N))) I.delta_pos).le
    _ = R.kernelNorm N I.mu I.mu := (R.kernelNorm_eq_signedEndpointEnergy I N).symm
    _ ≤ _ := R.kernelNorm_le_gain I N ⟨le_rfl,I.mu_lt_L.le⟩ ⟨le_rfl,I.mu_lt_L.le⟩

/-- Equality in the universal bound requires a flat signed endpoint profile. -/
theorem finalExact_gain_eq_lower_imp_flat (R : Realization ι) (I : SpectralInterval) (N : ℕ)
    (hexact : R.residualPolynomial N = I.residual N)
    (heq : R.gain I N = 2*I.epsilon N/I.delta*Real.sqrt ((N:ℝ)^3)) :
    ∀ s < N, R.signedEndpointProfile I N s = (N:ℝ) := by
  apply (R.signedEndpointEnergy_eq_cube_iff I N hexact).mp
  have hc : 0 < 2*I.epsilon N/I.delta :=
    div_pos (mul_pos (by norm_num) (one_div_pos.mpr (I.den_pos N))) I.delta_pos
  have hb := R.kernelNorm_le_gain I N ⟨le_rfl,I.mu_lt_L.le⟩ ⟨le_rfl,I.mu_lt_L.le⟩
  rw [R.kernelNorm_eq_signedEndpointEnergy I N,heq] at hb
  have hs := (mul_le_mul_iff_right₀ hc).mp hb
  exact le_antisymm ((Real.sqrt_le_sqrt_iff (by positivity : 0 ≤ (N:ℝ)^3)).mp hs)
    (R.signedEndpointEnergy_ge_cube I N hexact)

end
end chebyshev1.Realization
