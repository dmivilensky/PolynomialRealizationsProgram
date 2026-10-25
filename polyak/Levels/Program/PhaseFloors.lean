import polyak.Levels.Program.Monotonicity
import polyak.Levels.Lattice.Residues
import Mathlib.Analysis.SpecialFunctions.Complex.Arg

/-! Literal Zames--Falb multipliers and their phase floors. -/
noncomputable section
open scoped BigOperators
namespace polyak.Levels

def zfMultiplier (F : Finset ℤ) (a : ℤ→ℝ) (γ : ℝ) (ω : ℝ) : ℂ :=
  (γ:ℂ)+(∑n∈F,(a n:ℂ)*(1-Complex.exp ((((n:ℝ)*ω:ℝ):ℂ)*Complex.I)))

def phaseFloor (F : Finset ℤ) (a : ℤ→ℝ) (γ : ℝ) (ω : ℝ) : ℝ :=
  (zfMultiplier F a γ ω).arg+Real.pi/2

theorem zfMultiplier_re (F : Finset ℤ) (a : ℤ→ℝ) (γ ω : ℝ) :
    (zfMultiplier F a γ ω).re=γ+(∑n∈F,a n*(1-Real.cos ((n:ℝ)*ω))) := by
  simp only [zfMultiplier,Complex.add_re,Complex.re_sum,Complex.ofReal_re,Complex.mul_re,
    Complex.ofReal_im,Complex.sub_re,Complex.one_re,Complex.exp_ofReal_mul_I_re,zero_mul,sub_zero]

theorem zfMultiplier_im (F : Finset ℤ) (a : ℤ→ℝ) (γ ω : ℝ) :
    (zfMultiplier F a γ ω).im=-(∑n∈F,a n*Real.sin ((n:ℝ)*ω)) := by
  simp only [zfMultiplier,Complex.add_im,Complex.im_sum,Complex.ofReal_im,Complex.mul_im,
    Complex.ofReal_re,Complex.sub_im,Complex.one_im,Complex.exp_ofReal_mul_I_im,zero_mul,add_zero,
    zero_sub,mul_neg,Finset.sum_neg_distrib,zero_add]

theorem zfMultiplier_re_pos (F : Finset ℤ) (a : ℤ→ℝ) {γ : ℝ} (hγ : 0<γ)
    (ha : ∀n∈F,0≤a n) (ω : ℝ) : 0<(zfMultiplier F a γ ω).re := by
  rw [zfMultiplier_re]
  exact add_pos_of_pos_of_nonneg hγ (Finset.sum_nonneg fun n hn =>
    mul_nonneg (ha n hn) (sub_nonneg.mpr (Real.cos_le_one _)))

theorem complex_rotated_negative_iff {z : ℂ} (hz : 0<z.re) {θ : ℝ}
    (hθ : 0<θ) (hθπ : θ≤Real.pi) :
    z.re*Real.cos θ+z.im*Real.sin θ<0 ↔ z.arg+Real.pi/2<θ := by
  have ha := abs_lt.mp (Complex.abs_arg_lt_pi_div_two_iff.mpr (Or.inl hz))
  have hz0 : z≠0 := by intro he; rw [he,Complex.zero_re] at hz; exact lt_irrefl _ hz
  have hn : 0<‖z‖ := norm_pos_iff.mpr hz0
  have he : z.re*Real.cos θ+z.im*Real.sin θ=‖z‖*Real.cos (θ-z.arg) := by
    rw [Real.cos_sub,mul_add]
    have hc := Complex.norm_mul_cos_arg z
    have hs := Complex.norm_mul_sin_arg z
    calc
      _=(‖z‖*Real.cos z.arg)*Real.cos θ+(‖z‖*Real.sin z.arg)*Real.sin θ := by rw [hc,hs]
      _=_ := by ring
  rw [he]
  constructor
  · intro h
    by_contra hnot
    have hc : 0≤Real.cos (θ-z.arg) := Real.cos_nonneg_of_neg_pi_div_two_le_of_le
      (by linarith [ha.2]) (by linarith)
    exact (not_lt_of_ge (mul_nonneg hn.le hc)) h
  · intro h
    exact mul_neg_of_pos_of_neg hn (Real.cos_neg_of_pi_div_two_lt_of_lt
      (by linarith) (by linarith [ha.1]))

theorem CertificateSymbol.eval_eq_multiplier {Θ : Curve} {𝒩 : Set ℤ}
    (S : CertificateSymbol Θ 𝒩) (ω : Frequency) :
    S.eval ω=(zfMultiplier S.lags S.weight S.gamma ω).re*Real.cos (Θ ω)+
      (zfMultiplier S.lags S.weight S.gamma ω).im*Real.sin (Θ ω) := by
  rw [S.eval_eq_parts,zfMultiplier_re,zfMultiplier_im]
  rfl

theorem strictSymbol_iff_phaseFloors (Θ : Curve) (𝒩 : Set ℤ) :
    Nonempty (StrictSymbol Θ 𝒩) ↔ ∃S : CertificateSymbol Θ 𝒩,0<S.gamma ∧
      ∀ω : Frequency,0<(ω:ℝ)→phaseFloor S.lags S.weight S.gamma ω<Θ ω := by
  constructor
  · rintro ⟨S⟩
    refine ⟨S.symbol,S.gamma_pos,fun ω _ => ?_⟩
    apply (complex_rotated_negative_iff
      (zfMultiplier_re_pos _ _ S.gamma_pos S.symbol.weight_nonneg ω) (Θ.pos ω) (Θ.le_pi ω)).mp
    rw [← S.symbol.eval_eq_multiplier]
    exact lt_of_le_of_lt (S.strict ω) (neg_neg_of_pos S.epsilon_pos)
  · rintro ⟨S,hγ,hphase⟩
    apply strictSymbol_of_pointwise_negative S
    intro ω
    rcases eq_or_lt_of_le ω.property.1 with h0|h0
    · have he : ω=frequencyZero := Subtype.ext h0.symm
      rw [he]
      simp only [CertificateSymbol.eval,Curve.lag_at_zero,mul_zero,Finset.sum_const_zero,
        Curve.minimizer_at_zero,mul_neg,mul_one,zero_add]
      exact neg_neg_of_pos hγ
    · rw [S.eval_eq_multiplier]
      exact (complex_rotated_negative_iff (zfMultiplier_re_pos _ _ hγ S.weight_nonneg ω)
        (Θ.pos ω) (Θ.le_pi ω)).mpr (hphase ω h0)

theorem rational_lag_nonneg_at_floor {k : ℕ} (hk : 1≤k) (j : ℕ) (n : ℤ) :
    0≤Lattice.lagValue (Real.pi/k) ((n:ℝ)*(2*Real.pi*j/k)) := by
  have hkR : (0:ℝ)<k := by exact_mod_cast (by omega : 0<k)
  by_contra hn
  have he := (Lattice.rational_lag_neg_iff (by omega : 0<k) j n
    (div_pos Real.pi_pos hkR) ((div_le_self Real.pi_pos.le (by exact_mod_cast hk)))).mp
    (lt_of_not_ge hn)
  have hunit : (k:ℝ)*(Real.pi/k)/Real.pi=1 := by field_simp
  rw [hunit] at he
  have hi : (1:ℤ)≤(n*(j:ℤ))%(k:ℤ) := by omega
  have hiR : (1:ℝ)≤((n*(j:ℤ))%(k:ℤ):ℤ) := by exact_mod_cast hi
  linarith

theorem phaseFloor_rational_lower (F : Finset ℤ) (a : ℤ→ℝ) {γ : ℝ}
    (ha : ∀n∈F,0≤a n) (hγ : 0<γ) {k : ℕ} (hk : 2≤k) (j : ℕ) :
    Real.pi/k≤phaseFloor F a γ (2*Real.pi*j/k) := by
  have hkR : (0:ℝ)<k := by exact_mod_cast (by omega : 0<k)
  have hk2R : (2:ℝ)≤k := by exact_mod_cast hk
  by_contra hn
  have hphase : phaseFloor F a γ (2*Real.pi*j/k)<Real.pi/k := lt_of_not_ge hn
  have hneg := (complex_rotated_negative_iff
    (zfMultiplier_re_pos F a hγ ha _) (div_pos Real.pi_pos hkR)
    (div_le_self Real.pi_pos.le (by exact_mod_cast (by omega : 1≤k)))).mpr hphase
  rw [zfMultiplier_re,zfMultiplier_im] at hneg
  have hsum : 0≤(∑n∈F,a n*Lattice.lagValue (Real.pi/k) ((n:ℝ)*(2*Real.pi*j/k))) :=
    Finset.sum_nonneg (fun n hn => mul_nonneg (ha n hn) (rational_lag_nonneg_at_floor (by omega) j n))
  have hcos : 0≤Real.cos (Real.pi/k) := Real.cos_nonneg_of_neg_pi_div_two_le_of_le
    (by have hp : 0≤Real.pi/(k:ℝ) := div_nonneg Real.pi_pos.le hkR.le; linarith [Real.pi_pos])
    (by apply (div_le_iff₀ hkR).mpr; nlinarith [Real.pi_pos])
  have he : (zfMultiplier F a γ (2*Real.pi*j/k)).re*Real.cos (Real.pi/k)+
      (zfMultiplier F a γ (2*Real.pi*j/k)).im*Real.sin (Real.pi/k)=
      γ*Real.cos (Real.pi/k)+(∑n∈F,a n*Lattice.lagValue (Real.pi/k) ((n:ℝ)*(2*Real.pi*j/k))) := by
    rw [zfMultiplier_re,zfMultiplier_im,add_mul,neg_mul,Finset.sum_mul,Finset.sum_mul]
    have he (n:ℤ) : a n*Lattice.lagValue (Real.pi/k) ((n:ℝ)*(2*Real.pi*j/k))=
        a n*(1-Real.cos ((n:ℝ)*(2*Real.pi*j/k)))*Real.cos (Real.pi/k)-
        a n*Real.sin ((n:ℝ)*(2*Real.pi*j/k))*Real.sin (Real.pi/k) := by
      dsimp [Lattice.lagValue]
      rw [Real.cos_sub]
      ring
    simp_rw [he]
    rw [Finset.sum_sub_distrib]
    ring
  rw [zfMultiplier_re,zfMultiplier_im] at he
  have hpos := add_nonneg (mul_nonneg hγ.le hcos) hsum
  linarith

end polyak.Levels
