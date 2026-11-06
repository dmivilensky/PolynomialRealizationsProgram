import nesterov.Layer.SpreadWitnessProduct

/-! Uniform O(σ) cross-characteristic bound whenever ε≤σ and ξ≤bσ. -/
namespace nesterov.TwoStep
noncomputable section
open Set Filter
open scoped Topology

theorem product_bound_at_scale_of_compact {ε σ θ h τ c b M : ℝ}
    (hε : 0<ε) (hε1 : ε≤1) (hεσ : ε≤σ) (hb : 0<b) (hM : 1≤M)
    (hθ : |θ|≤M) (hh : |h|≤M) (hτ : |τ|≤M) :
    ∀ ω : ℝ,1-Real.cos ω≤b*σ →
      ‖Quadratic.characteristic (1-θ*ε) τ h (ε^2) (circle (1-c*ε) ω)*
        star (Quadratic.characteristic (1-θ*ε) τ h 1 (circle (1-c*ε) ω))‖≤layerProductConstant c b M*σ := by
  let R : ℝ := 1+|c|
  let N : ℝ := R+1
  let Q : ℝ := (1+M)*R+M
  let Cs : ℝ := c^2+2*R*b+M*N+M*Q
  let Cf : ℝ := N^2+M*N+M*Q
  have hR : 0<R := by dsimp [R];positivity
  have hN : 0<N := by dsimp [N];positivity
  have hQ : 0<Q := by dsimp [Q];positivity
  have hCs : 0<Cs := by dsimp [Cs];positivity
  have hCf : 0<Cf := by dsimp [Cf];positivity
  intro ω hξ
  change _≤Cs*Cf*σ
  let z := circle (1-c*ε) ω
  let n : ℝ := ‖z-1‖
  have hσ : 0<σ := hε.trans_le hεσ
  have heS : ε≤σ := hεσ
  have he2S : ε^2≤σ := by nlinarith
  have hz : ‖z‖≤R := by
    rw [show z=circle (1-c*ε) ω from rfl,circle_norm]
    calc
      _ ≤ |(1:ℝ)|+|c*ε| := abs_sub _ _
      _ = 1+|c| * ε := by rw [abs_one,abs_mul,abs_of_pos hε]
      _ ≤ R := by dsimp [R];nlinarith [abs_nonneg c]
  have hn : n≤N := by
    have hn' := norm_sub_le z (1:ℂ)
    simp only [norm_one] at hn'
    exact hn'.trans (by dsimp [N];linarith)
  have hn0 : 0≤n := norm_nonneg _
  have hnn : n^2≤N^2 := pow_le_pow_left₀ hn0 hn 2
  have hξ0 : 0≤1-Real.cos ω := sub_nonneg.mpr (Real.cos_le_one ω)
  have hnS : n^2≤(c^2+2*R*b)*σ := by
    have heq := circle_sub_one_norm_sq (1-c*ε) ω
    have hr : 1-c*ε≤R := by
      have hh := le_abs_self (1-c*ε)
      rw [←circle_norm _ ω] at hh
      exact hh.trans hz
    have h1 := mul_le_mul_of_nonneg_right hr hξ0
    have h2 := mul_le_mul_of_nonneg_left hξ hR.le
    have h3 := mul_le_mul_of_nonneg_left he2S (sq_nonneg c)
    change n^2=(1-c*ε-1)^2+2*(1-c*ε)*(1-Real.cos ω) at heq
    nlinarith
  have hquery : (1+|τ|)*‖z‖+|τ|≤Q := by
    have hm := mul_le_mul (by linarith : 1+|τ|≤1+M) hz (norm_nonneg z) (by linarith)
    dsimp [Q]
    linarith
  have hbet : |1-(1-θ*ε)|=|θ| * ε := by rw [show 1-(1-θ*ε)=θ*ε by ring,abs_mul,abs_of_pos hε]
  have hcross : |1-(1-θ*ε)| * n≤M*N*ε := by
    rw [hbet]
    have hm := mul_le_mul hθ hn hn0 (by linarith : 0≤M)
    nlinarith [mul_le_mul_of_nonneg_right hm hε.le]
  have hslow : ‖Quadratic.characteristic (1-θ*ε) τ h (ε^2) z‖≤Cs*σ := by
    have hpol := characteristic_norm_slow_bound (1-θ*ε) τ h (ε^2) z
    have hcoef : |h*ε^2|≤M*ε^2 := by rw [abs_mul,abs_of_nonneg (sq_nonneg ε)];exact mul_le_mul_of_nonneg_right hh (sq_nonneg ε)
    have hprod := mul_le_mul hcoef hquery (by positivity) (by positivity : 0≤M*ε^2)
    have hc1 := mul_le_mul_of_nonneg_left heS (by positivity : 0≤M*N)
    have hc2 := mul_le_mul_of_nonneg_left he2S (by positivity : 0≤M*Q)
    dsimp [Cs]
    change _≤n^2+|1-(1-θ*ε)| * n+|h*ε^2| *((1+|τ|)*‖z‖+|τ|) at hpol
    nlinarith
  have hfast : ‖Quadratic.characteristic (1-θ*ε) τ h 1 z‖≤Cf := by
    have hpol := characteristic_norm_slow_bound (1-θ*ε) τ h 1 z
    simp only [mul_one] at hpol
    have hp := mul_le_mul hh hquery (by positivity) (by linarith : 0≤M)
    have hc := mul_le_mul_of_nonneg_left hε1 (by positivity : 0≤M*N)
    dsimp [Cf]
    change _≤n^2+|1-(1-θ*ε)| * n+|h| *((1+|τ|)*‖z‖+|τ|) at hpol
    nlinarith
  rw [norm_mul,norm_star]
  have hp := mul_le_mul hslow hfast (norm_nonneg _) (mul_nonneg hCs.le hσ.le)
  nlinarith

end
end nesterov.TwoStep
