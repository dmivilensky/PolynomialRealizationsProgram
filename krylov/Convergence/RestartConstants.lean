import krylov.Design.HyperbolicDictionary

/-!
Article: main_krylov, thm:D and apG:D, exact restarted spectral constants.
Use: identify FC's weighted Chebyshev sum with its printed hyperbolic
constant and establish the strict no-extra-gradient cancellation improvement.
Source: consecutive hyperbolic tangent differences and the exact Chebyshev
profile already proved for the original physical interval.
-/
namespace krylov.Convergence
noncomputable section
open Real Finset jacobi.Young
open scoped BigOperators

/-- The actual finite weighted Chebyshev product entering restarted FC.
Article: main_krylov, thm:D. -/
def fcRestartConstant (θ : ℝ) (K : ℕ) : ℝ :=
  ∑ l∈range K,sech ((l:ℝ)*θ)*sech (((l:ℝ)+1)*θ)

/-- The printed data-midpoint DC constant on the same finite profile.
Article: main_krylov, thm:D. -/
def dcRestartConstant (θ ρ : ℝ) (K : ℕ) : ℝ :=
  ∑ l∈range K,sech ((l:ℝ)*θ)*
    sqrt (ρ^2*sech (((l:ℝ)+1)*θ)^2+(1-ρ^2)*sech ((K:ℝ)*θ)^2)

/-- Consecutive tanh differences give the exact adjacent-sech product.
Article: main_krylov, apG:D, telescoping identity. -/
theorem adjacent_sech_product (θ : ℝ) (hθ : 0<θ) (l : ℕ) :
    sech ((l:ℝ)*θ)*sech (((l:ℝ)+1)*θ)=
      (tanh (((l:ℝ)+1)*θ)-tanh ((l:ℝ)*θ))/sinh θ := by
  have hs : sinh θ≠0 := (Real.sinh_pos_iff.mpr hθ).ne'
  have hid := Real.sinh_sub (((l:ℝ)+1)*θ) ((l:ℝ)*θ)
  rw [show ((l:ℝ)+1)*θ-(l:ℝ)*θ=θ by ring] at hid
  rw [sech,sech,Real.tanh_eq_sinh_div_cosh,Real.tanh_eq_sinh_div_cosh]
  field_simp [hs,(Real.cosh_pos ((l:ℝ)*θ)).ne',(Real.cosh_pos (((l:ℝ)+1)*θ)).ne']
  ring_nf at hid ⊢
  nlinarith only [hid]

/-- FC's actual finite Chebyshev product sum is the literal printed
constant, independent of a separate sum estimate. Article: thm:D. -/
theorem fcRestartConstant_eq (θ : ℝ) (hθ : 0<θ) (K : ℕ) :
    fcRestartConstant θ K=tanh ((K:ℝ)*θ)/sinh θ := by
  induction K with
  | zero => simp [fcRestartConstant]
  | succ K ih =>
    rw [fcRestartConstant,sum_range_succ]
    change fcRestartConstant θ K+_= _
    rw [ih,adjacent_sech_product θ hθ K]
    push_cast
    ring

/-- The restarted FC constant never exceeds one over the true spectral
spacing's sinh. Article: main_krylov, thm:D. -/
theorem fcRestartConstant_le_inverse_sinh (θ : ℝ) (hθ : 0<θ) (K : ℕ) :
    fcRestartConstant θ K≤(sinh θ)⁻¹ := by
  rw [fcRestartConstant_eq θ hθ K,←one_div]
  exact div_le_div_of_nonneg_right (Real.tanh_lt_one _).le (Real.sinh_pos_iff.mpr hθ).le

/-- The actual spectral spacing has the literal condition-number
constant used in the restarted FC bound. Article: main_krylov, thm:D. -/
theorem inverse_sinh_designSpacing (I : chebyshev1.SpectralInterval) :
    (sinh (krylov.Design.designSpacing I))⁻¹=(I.kappa-1)/(2*sqrt I.kappa) := by
  have hkg : 1<I.kappa := (one_lt_div I.mu_pos).mpr I.mu_lt_L
  have hg : 0<I.kappa-1 := sub_pos.mpr hkg
  have hk : 0<I.kappa := lt_trans (by norm_num : (0:ℝ)<1) hkg
  have hsg : sqrt (I.kappa-1)≠0 := (sqrt_pos.mpr hg).ne'
  have hsk : sqrt I.kappa≠0 := (sqrt_pos.mpr hk).ne'
  obtain ⟨hs,ht⟩ := krylov.Design.designSpacing_half_angle I
  have hc : cosh (krylov.Design.designSpacing I/2)=sqrt I.kappa/sqrt (I.kappa-1) := by
    rw [Real.tanh_eq_sinh_div_cosh,hs] at ht
    field_simp [hsg,hsk,(Real.cosh_pos (krylov.Design.designSpacing I/2)).ne'] at ht ⊢
    nlinarith only [ht]
  rw [show krylov.Design.designSpacing I=2*(krylov.Design.designSpacing I/2) by ring,
    Real.sinh_two_mul,hs,hc]
  have hsq := Real.sq_sqrt hg.le
  field_simp [hsg,hsk]
  nlinarith only [hsq]

/-- The finite FC restart constant is bounded by the original simple
condition-number expression. Article: main_krylov, thm:D. -/
theorem fcRestartConstant_le_condition (I : chebyshev1.SpectralInterval) (K : ℕ) :
    fcRestartConstant (krylov.Design.designSpacing I) K≤(I.kappa-1)/(2*sqrt I.kappa) := by
  rw [←inverse_sinh_designSpacing I]
  exact fcRestartConstant_le_inverse_sinh _ (krylov.Design.designSpacing_pos I) K

private theorem sech_strict_decrease {a b : ℝ} (ha : 0≤a) (hab : a<b) : sech b<sech a := by
  unfold sech
  exact inv_lt_inv₀ (Real.cosh_pos b) (Real.cosh_pos a) |>.mpr
    (Real.cosh_strictMonoOn ha (ha.trans hab.le) hab)

/-- DC's actual data-midpoint Chebyshev constant is strictly smaller than
FC's for every original n>=3 and every |rho|<1.
Article: main_krylov, thm:D, strict no-extra-gradient comparison. -/
theorem dcRestartConstant_lt_fc (θ ρ : ℝ) (hθ : 0<θ) (hρ : |ρ|<1)
    (K : ℕ) (hK : 2≤K) : dcRestartConstant θ ρ K<fcRestartConstant θ K := by
  have hρ₂ : ρ^2<1 := by nlinarith only [sq_abs ρ,abs_nonneg ρ,hρ]
  have hρc : 0<1-ρ^2 := sub_pos.mpr hρ₂
  have hterm (l : ℕ) (hl : l∈range K) :
      sqrt (ρ^2*sech (((l:ℝ)+1)*θ)^2+(1-ρ^2)*sech ((K:ℝ)*θ)^2)≤
        sech (((l:ℝ)+1)*θ) := by
    have hi : ((l:ℝ)+1)*θ≤(K:ℝ)*θ := by
      apply mul_le_mul_of_nonneg_right _ hθ.le
      exact_mod_cast Nat.succ_le_of_lt (mem_range.mp hl)
    have hs := krylov.Design.sech_antitoneOn (by positivity : 0≤((l:ℝ)+1)*θ) (by positivity : 0≤(K:ℝ)*θ) hi
    have hsq := (sq_le_sq₀ (sech_pos _).le (sech_pos _).le).mpr hs
    have hh := mul_le_mul_of_nonneg_left hsq hρc.le
    have hb : ρ^2*sech (((l:ℝ)+1)*θ)^2+(1-ρ^2)*sech ((K:ℝ)*θ)^2≤sech (((l:ℝ)+1)*θ)^2 := by
      nlinarith only [hh]
    exact (Real.sqrt_le_sqrt hb).trans_eq (Real.sqrt_sq (sech_pos _).le)
  have hfirst :
      sqrt (ρ^2*sech θ^2+(1-ρ^2)*sech ((K:ℝ)*θ)^2)<sech θ := by
    have hidx : θ<(K:ℝ)*θ := by
      have hk : (1:ℝ)<K := by exact_mod_cast (by omega : 1<K)
      nlinarith only [hk,hθ]
    have hs := sech_strict_decrease hθ.le hidx
    have hsq := (sq_lt_sq₀ (sech_pos _).le (sech_pos _).le).mpr hs
    have hh := mul_lt_mul_of_pos_left hsq hρc
    have hb : ρ^2*sech θ^2+(1-ρ^2)*sech ((K:ℝ)*θ)^2<sech θ^2 := by nlinarith only [hh]
    exact (Real.sqrt_lt_sqrt (by positivity) hb).trans_eq (Real.sqrt_sq (sech_pos _).le)
  unfold dcRestartConstant fcRestartConstant
  apply sum_lt_sum
  · intro l hl
    exact mul_le_mul_of_nonneg_left (hterm l hl) (sech_pos _).le
  · refine ⟨0,mem_range.mpr (by omega),?_⟩
    simpa only [Nat.cast_zero,zero_mul,zero_add,one_mul] using
      mul_lt_mul_of_pos_left hfirst (sech_pos (0*θ))

end
end krylov.Convergence
