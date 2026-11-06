import nesterov.Spectral.Feasibility
import nesterov.Flow.SmallLag

/-!
Article: Lemma D.4. The common value charge is controlled by the lag-one
constraints of the actual probability spectrum; arbitrary measures are allowed.
-/
namespace nesterov.Slow
noncomputable section
open Spectral MeasureTheory Filter

def measureCharge (ν : Spectrum) (a : SymbolPair) (t : ℝ) : ℝ :=
  (∫ x,2*skew a x*Real.arccos x ∂ν)/t

theorem feasible_lag_one_abs {ν : Spectrum} {a : SymbolPair} {t C : ℝ}
    (h : Feasible a t ν C) : |meanB ν a 1-C*Real.sinh t|≤meanA ν a t 1 := by
  obtain ⟨hl,hu⟩ := h.2 1 le_rfl
  simp only [Nat.cast_one,one_mul] at hl hu
  exact abs_le.mpr ⟨by linarith,by linarith⟩

theorem charge_difference_estimate {ν : Spectrum} {a : SymbolPair} {t C C₀ A B : ℝ}
    (h : Feasible a t ν C) (hA : meanA ν a t 1≤A)
    (hB : |meanB ν a 1-C₀*Real.sinh t|≤B) :
    |C-C₀| * |Real.sinh t|≤A+B := by
  have hl := feasible_lag_one_abs h
  have he : (C-C₀)*Real.sinh t=
      (meanB ν a 1-C₀*Real.sinh t)-(meanB ν a 1-C*Real.sinh t) := by ring
  rw [←abs_mul,he]
  exact (abs_sub _ _).trans (by linarith)

theorem forced_cubic_of_bounds {ν : Spectrum} {a : SymbolPair} {t C C₀ ε c K₂ K₃ : ℝ}
    (h : Feasible a t ν C) (hε : 0<ε) (hε1 : ε≤1) (hc : 0<c) (hK₃ : 0≤K₃)
    (hA : meanA ν a t 1≤K₂*ε^4)
    (hB : |meanB ν a 1-C₀*Real.sinh t|≤K₃*ε^5)
    (hsinh : c*ε≤|Real.sinh t|) :
    |C-C₀|≤((K₂+K₃)/c)*ε^3 := by
  have he := charge_difference_estimate h hA hB
  have h₅ : ε^5≤ε^4 := by
    have hh := mul_le_mul_of_nonneg_left hε1 (pow_nonneg hε.le 4)
    simpa only [←pow_succ,mul_one] using hh
  have hk := mul_le_mul_of_nonneg_left h₅ hK₃
  have hs := mul_le_mul_of_nonneg_left hsinh (abs_nonneg (C-C₀))
  have hb : |C-C₀| *(c*ε)≤(K₂+K₃)*ε^4 := by linarith
  calc
    _ ≤ ((K₂+K₃)*ε^4)/(c*ε) := (le_div_iff₀ (mul_pos hc hε)).mpr hb
    _ = _ := by field_simp

theorem measure_charge_residual (ν : Spectrum) (a : SymbolPair) (t : ℝ) :
    meanB ν a 1-measureCharge ν a t*Real.sinh t=
      ∫ x,2*skew a x*(Real.sin (Real.arccos x)-Real.arccos x*Real.sinh t/t) ∂ν := by
  have hi₁ := polyak.Spectral.integrable_continuous ν (show Continuous
    (fun x : Frequency=>2*skew a x*Real.sin (Real.arccos x)) by unfold skew;fun_prop)
  have hi₂ := polyak.Spectral.integrable_continuous ν (show Continuous
    (fun x : Frequency=>2*skew a x*Real.arccos x) by unfold skew;fun_prop)
  have hf (x : Frequency) : 2*skew a x*(Real.sin (Real.arccos x)-Real.arccos x*Real.sinh t/t)=
      2*skew a x*Real.sin (Real.arccos x)-(2*skew a x*Real.arccos x)*(Real.sinh t/t) := by ring
  simp_rw [hf]
  rw [integral_sub hi₁ (hi₂.mul_const _),integral_mul_const]
  simp only [meanB,lagB,Nat.cast_one,one_mul,measureCharge]
  ring

/-- The source's exact formula for C_* after extracting the common slow scale. -/
 theorem slow_measure_charge {ν : Spectrum} {a : SymbolPair} {ε c scale : ℝ}
    (hε : ε≠0) (hc : c≠0) (S : Frequency→ℝ)
    (hs : ∀ᵐ x ∂(ν : Measure Frequency),2*skew a x=scale*S x) :
    measureCharge ν a (-c*ε)= -scale/c*∫ (x : Frequency),(Real.arccos x/ε)*S x ∂ν := by
  have he : (∫ x,2*skew a x*Real.arccos x ∂ν)=
      (scale*ε)*∫ (x : Frequency),(Real.arccos x/ε)*S x ∂ν := by
    rw [←integral_const_mul]
    apply integral_congr_ae
    filter_upwards [hs] with x hx
    rw [hx]
    field_simp
  rw [measureCharge,he]
  field_simp

/-- The lag-one estimates are uniform over all probability measures on a slow band. -/
theorem forced_on_band {ν : Spectrum} {a : SymbolPair} {C ε c c₀ c₁ Γ K : ℝ}
    (h : Feasible a (-c*ε) ν C) (hε : 0<ε) (hε1 : ε≤1)
    (hc₀ : 0<c₀) (hc : c₀≤c) (hc₁ : c≤c₁) (hΓ : 0≤Γ) (hK : 0≤K)
    (hcε : c₁*ε≤1) (hΓε : Γ*ε≤1)
    (hband : ∀ᵐ (x : Frequency) ∂(ν : Measure Frequency),Real.arccos x≤ε*Γ)
    (hcoeff : ∀ᵐ x ∂(ν : Measure Frequency),
      |g a x|≤K*ε^2 ∧ |2*skew a x|≤K*ε^2) :
    |C-measureCharge ν a (-c*ε)|≤
      ((K*(c₁^2+Γ^2)+K*Γ*(c₁^2+Γ^2))/c₀)*ε^3 := by
  have hcp : 0<c := hc₀.trans_le hc
  have hc₁p : 0≤c₁ := (hcp.trans_le hc₁).le
  have hcε' : c*ε≤1 := (mul_le_mul_of_nonneg_right hc₁ hε.le).trans hcε
  have hbound : ∀ᵐ x ∂(ν : Measure Frequency),
      ‖lagA a (-c*ε) 1 x‖≤K*(c₁^2+Γ^2)*ε^4 ∧
      ‖2*skew a x*(Real.sin (Real.arccos x)-
        Real.arccos x*Real.sinh (-c*ε)/(-c*ε))‖≤K*Γ*(c₁^2+Γ^2)*ε^5 := by
    filter_upwards [hband,hcoeff] with x hx ha
    let γ := Real.arccos x/ε
    have hγ : 0≤γ := div_nonneg (Real.arccos_nonneg _) hε.le
    have hγΓ : γ≤Γ := (div_le_iff₀ hε).mpr (by simpa only [mul_comm] using hx)
    have heq : γ*ε=Real.arccos x := div_mul_cancel₀ _ hε.ne'
    have hγsmall : γ*ε≤1 := (mul_le_mul_of_nonneg_right hγΓ hε.le).trans hΓε
    have hsq : c^2+γ^2≤c₁^2+Γ^2 := add_le_add
      (pow_le_pow_left₀ hcp.le hc₁ 2) (pow_le_pow_left₀ hγ hγΓ 2)
    have hA := (Flow.kernelA_small_bounds hcp.le hγ hε.le hcε' hγsmall).2
    have hA₀ := Flow.kernelA_nonneg c γ ε
    have hB := Flow.kernelB_small_upper hcp hγ hε.le hcε'
    have hB₀ := Flow.kernelB_nonneg hcp hγ hε.le
    have hAeq : Real.cosh (-(c*ε))-Real.cos (Real.arccos x)=Flow.kernelA c γ ε := by
      simp only [Flow.kernelA,heq,Real.cosh_neg]
    have hBeq : Real.sin (Real.arccos x)-Real.arccos x*Real.sinh (-c*ε)/(-c*ε)=
        -Flow.kernelB c γ ε := by
      rw [show -c*ε= -(c*ε) by ring,Real.sinh_neg]
      dsimp [Flow.kernelB]
      rw [←heq]
      field_simp
      ring
    constructor
    · simp only [lagA,Nat.cast_one,one_mul,show -c*ε= -(c*ε) by ring,hAeq,norm_mul,
        Real.norm_eq_abs,abs_of_nonneg hA₀]
      calc
        |g a x| *Flow.kernelA c γ ε≤(K*ε^2)*((c^2+γ^2)*ε^2) :=
          mul_le_mul ha.1 hA hA₀ (by positivity)
        _≤(K*ε^2)*((c₁^2+Γ^2)*ε^2) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hsq (sq_nonneg ε)) (by positivity)
        _=_ := by ring
    · rw [hBeq,norm_mul,Real.norm_eq_abs,Real.norm_eq_abs,abs_neg,abs_of_nonneg hB₀]
      have hB' : Flow.kernelB c γ ε≤Γ*(c₁^2+Γ^2)*ε^3 := by
        have hh := mul_le_mul hγΓ hsq (by positivity : 0≤c^2+γ^2) hΓ
        have hi := mul_le_mul_of_nonneg_right hh (pow_nonneg hε.le 3)
        nlinarith [mul_nonneg (mul_nonneg hγ (by positivity : 0≤c^2+γ^2))
          (pow_nonneg hε.le 3)]
      calc
        |2*skew a x| *Flow.kernelB c γ ε≤(K*ε^2)*(Γ*(c₁^2+Γ^2)*ε^3) :=
          mul_le_mul ha.2 hB' hB₀ (by positivity)
        _=_ := by ring
  have hA : meanA ν a (-c*ε) 1≤K*(c₁^2+Γ^2)*ε^4 := by
    have hh := norm_integral_le_of_norm_le_const (μ := (ν : Measure Frequency))
      (hbound.mono fun _ hx=>hx.1)
    have he : ‖meanA ν a (-c*ε) 1‖≤K*(c₁^2+Γ^2)*ε^4 := by simpa [meanA] using hh
    exact (le_abs_self _).trans he
  have hB : |meanB ν a 1-measureCharge ν a (-c*ε)*Real.sinh (-c*ε)|≤
      K*Γ*(c₁^2+Γ^2)*ε^5 := by
    rw [measure_charge_residual]
    simpa using norm_integral_le_of_norm_le_const (μ := (ν : Measure Frequency))
        (hbound.mono fun _ hx=>hx.2)
  apply forced_cubic_of_bounds h hε hε1 hc₀ (by positivity) hA hB
  rw [show -c*ε= -(c*ε) by ring,Real.sinh_neg,abs_neg,
    abs_of_nonneg (Real.sinh_nonneg_iff.mpr (mul_nonneg hcp.le hε.le))]
  exact (mul_le_mul_of_nonneg_right hc hε.le).trans
    (Real.self_le_sinh_iff.mpr (mul_nonneg hcp.le hε.le))

end
end nesterov.Slow
