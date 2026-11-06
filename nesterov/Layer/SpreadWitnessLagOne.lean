import nesterov.Layer.SpreadWitnessSymbols
import nesterov.Spread.Slacks

/-! The negative characteristic symbol verifies the remaining first-lag
condition at the source's extreme charge. -/
namespace nesterov.TwoStep.Spread
noncomputable section
open Spectral Phase Set

theorem lagOneSymbol_eq (a : SymbolPair) (t : ℝ) (c : Frequency) :
    nesterov.Spread.lagOneSymbol a t c=Phase.lagOne a t c := by
  have hre : (polyak.Waves.z t (Real.arccos c)).re=Real.exp t*Real.cos (Real.arccos c) := by
    simpa using polyak.Waves.z_pow_re t (Real.arccos c) 1
  have him : (polyak.Waves.z t (Real.arccos c)).im=Real.exp t*Real.sin (Real.arccos c) := by
    simpa using polyak.Waves.z_pow_im t (Real.arccos c) 1
  unfold nesterov.Spread.lagOneSymbol nesterov.Spread.lowerOsc Phase.lagOne
  simp only [Nat.cast_one,one_mul,Complex.mul_re,Complex.mul_im,Complex.sub_re,
    Complex.sub_im,Complex.one_re,Complex.one_im,Complex.ofReal_re,Complex.ofReal_im,
    Complex.I_re,Complex.I_im,hre,him]
  norm_num
  ring

theorem lagOneSymbol_momentum (q : Momentum.Tuning) {μ L r ω : ℝ}
    (hμL : μ<L) (hr : 0<r) (hω : ω∈Icc (0:ℝ) Real.pi) :
    nesterov.Spread.lagOneSymbol (pair q μ L r) (Real.log r) (frequency ω)=
      -scale q μ L*((1-circle r ω)*product q μ L r ω).re := by
  rw [lagOneSymbol_eq]
  unfold pair
  rw [Phase.lagOne_momentum hμL q.step_pos.ne',
    arccos_frequency hω,wave_log_radius hr]
  simp only [scale,product,mul_assoc]

theorem exp_sinh_log_identity {r : ℝ} (hr : 0<r) (hr1 : r<1) :
    Real.exp (Real.log r)*Real.sinh |Real.log r|=(1-r^2)/2 := by
  rw [Real.exp_log hr,abs_of_neg (Real.log_neg hr hr1),Real.sinh_neg,
    Real.sinh_eq,Real.exp_log hr,Real.exp_neg,Real.exp_log hr]
  field_simp
  ring

theorem first_lag_pointwise (q : Momentum.Tuning) {μ L ε c η lam X ω : ℝ}
    (hμL : μ<L) (hε : 0<ε) (hc : 0<c) (hr : 0<1-c*ε)
    (hη : 0<η) (hlam : 0<lam) (hX : 0<X) (hηc : η*c≤lam/2)
    (hω : ω∈Icc (0:ℝ) Real.pi)
    (hg : 0≤g (pair q μ L (1-c*ε)) (frequency ω))
    (hprod : ‖product q μ L (1-c*ε) ω‖≤X)
    (hH : ((1-circle (1-c*ε) ω)*product q μ L (1-c*ε) ω).re≤ -lam*ε*X) :
    η*Real.exp (Real.log (1-c*ε))*Real.sinh |Real.log (1-c*ε)| *
      g (pair q μ L (1-c*ε)) (frequency ω)<
        nesterov.Spread.lagOneSymbol (pair q μ L (1-c*ε)) (Real.log (1-c*ε)) (frequency ω) := by
  have hk := scale_pos q hμL
  have hr1 : 1-c*ε<1 := by nlinarith [mul_pos hc hε]
  have hex : Real.exp (Real.log (1-c*ε))*Real.sinh |Real.log (1-c*ε)|≤c*ε := by
    rw [exp_sinh_log_identity hr hr1]
    nlinarith [sq_nonneg (c*ε)]
  have hcoord := (coordinates q hμL hr hω).1
  have hG : g (pair q μ L (1-c*ε)) (frequency ω)≤scale q μ L*X := by
    have hreal : -(product q μ L (1-c*ε) ω).re≤X :=
      (neg_le_abs _).trans ((Complex.abs_re_le_norm _).trans hprod)
    rw [hcoord]
    nlinarith [mul_le_mul_of_nonneg_left hreal hk.le]
  rw [lagOneSymbol_momentum q hμL hr hω]
  have hsym : lam*ε*scale q μ L*X≤
      -scale q μ L*((1-circle (1-c*ε) ω)*product q μ L (1-c*ε) ω).re := by
    have hh := mul_le_mul_of_nonpos_left hH (neg_nonpos.mpr hk.le)
    nlinarith only [hh]
  calc
    _=η*(Real.exp (Real.log (1-c*ε))*Real.sinh |Real.log (1-c*ε)|)*
      g (pair q μ L (1-c*ε)) (frequency ω) := by ring
    _≤η*(c*ε)*g (pair q μ L (1-c*ε)) (frequency ω) := by gcongr
    _≤η*(c*ε)*(scale q μ L*X) := mul_le_mul_of_nonneg_left hG (by positivity)
    _=(η*c)*(ε*scale q μ L*X) := by ring
    _≤(lam/2)*(ε*scale q μ L*X) := mul_le_mul_of_nonneg_right hηc (by positivity)
    _<lam*ε*scale q μ L*X := by nlinarith [mul_pos (mul_pos (mul_pos hlam hε) hk) hX]
    _≤_ := hsym

end
end nesterov.TwoStep.Spread
