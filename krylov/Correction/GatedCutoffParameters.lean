import Mathlib.Tactic

/-!
Article: main_krylov, thm:UCg, genuine uniform cutoff invariant.
Use: Construct and preserve actual recorded-prefix angle and quadratic
residual bounds with one set of constants chosen before the real run.
Source: proved genuine spectral-gated step, actual measured Gram/angle
identities, real projected-residual propagation and scalar cutoff algebra.
-/

namespace krylov.Correction
noncomputable section

/-- Positive angle, quadratic-residual, line-cutoff and perturbation-radius allowances can be chosen uniformly before every actual reference and trajectory.
Use: Assemble the genuine uniform gated-RFC finite-cycle cutoff induction.
Article: main_krylov, thm:UCg, actual uniform cutoff invariant.
Proof: Construct the angle from the actual spectral threshold gap and horizon, then choose the residual allowance and positive cutoff. A finite minimum of explicit positive scalar radii gives the pair, correction-ratio and residual-contraction inequalities simultaneously.
-/
theorem uniform_cutoff_allowances (N : ℕ) (hN : 1≤N) (γ K F H L : ℝ)
    (hγ : 0≤γ) (hγ1 : γ<1) (hK : 0≤K) (hF : 0<F) (hH : 0<H) (hL : 0≤L) :
    ∃ a C M ε₀ : ℝ, 0<a ∧ a<1 ∧ 0<C ∧ 0<M ∧ 0<ε₀ ∧
      (N : ℝ)*a≤(1-γ)/8 ∧ 4*F*H*L≤C ∧
      ∀ ε : ℝ, 0≤ε → ε≤ε₀ →
        (1+K)*ε≤a/2 ∧ 4*C/M+4*H*ε≤a/4 ∧ F*ε≤1/2 := by
  have hN' : (1 : ℝ)≤N := by exact_mod_cast hN
  have hNpos : (0 : ℝ)<N := by linarith
  let a := (1-γ)/(8*(N : ℝ))
  let C := 4*F*H*L+1
  let M := 32*C/a
  have ha : 0<a := div_pos (by linarith) (by positivity)
  have hNa : (N : ℝ)*a=(1-γ)/8 := by dsimp only [a]; field_simp
  have ha1 : a<1 := by
    have ht := mul_le_mul_of_nonneg_right hN' ha.le
    rw [hNa] at ht
    linarith
  have hC : 0<C := by dsimp only [C]; positivity
  have hM : 0<M := div_pos (by positivity) ha
  have hratio : 4*C/M=a/8 := by dsimp only [M]; field_simp; norm_num
  let ε₀ := min (a/(2*(1+K))) (min (a/(32*H)) (1/(2*F)))
  have hε₀ : 0<ε₀ := lt_min (div_pos ha (by positivity))
    (lt_min (div_pos ha (by positivity)) (by positivity))
  refine ⟨a,C,M,ε₀,ha,ha1,hC,hM,hε₀,hNa.le,?_,?_⟩
  · dsimp only [C]
    linarith
  · intro ε _hε he
    have h₁ := (le_div_iff₀ (by positivity : 0<2*(1+K))).mp (he.trans (min_le_left _ _))
    have h₂ := (le_div_iff₀ (by positivity : 0<32*H)).mp (he.trans ((min_le_right _ _).trans (min_le_left _ _)))
    have h₃ := (le_div_iff₀ (by positivity : 0<2*F)).mp (he.trans ((min_le_right _ _).trans (min_le_right _ _)))
    rw [hratio]
    constructor
    · nlinarith
    · constructor <;> nlinarith

end
end krylov.Correction
