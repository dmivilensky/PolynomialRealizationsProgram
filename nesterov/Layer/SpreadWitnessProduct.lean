import nesterov.Layer.SpreadWitnessSymbols
import nesterov.TwoStep.AsymptoticsModel

/-! The characteristic product is uniformly O(sqrt ε) on every layer band.
Only the scaling limits are used; quadratic stability is not needed. -/
namespace nesterov.TwoStep
noncomputable section
open Set Filter
open scoped Topology

theorem circle_norm (r ω : ℝ) : ‖circle r ω‖=|r| := by
  apply (sq_eq_sq₀ (norm_nonneg _) (abs_nonneg _)).mp
  rw [←Complex.normSq_eq_norm_sq,circle_normSq,sq_abs]

theorem circle_sub_one_norm_sq (r ω : ℝ) :
    ‖circle r ω-1‖^2=(r-1)^2+2*r*(1-Real.cos ω) := by
  have hr : (circle r ω).re=r*Real.cos ω := by simpa using circle_pow_re r ω 1
  have hz := circle_normSq r ω
  rw [←Complex.normSq_eq_norm_sq,Complex.normSq_apply]
  simp only [Complex.sub_re,Complex.sub_im,Complex.one_re,Complex.one_im,sub_zero]
  rw [Complex.normSq_apply] at hz
  nlinarith

theorem characteristic_slow_factor (β τ h lam : ℝ) (z : ℂ) :
    Quadratic.characteristic β τ h lam z=(z-1)^2+((1-β:ℝ):ℂ)*(z-1)+
      ((h*lam:ℝ):ℂ)*(((1+τ:ℝ):ℂ)*z-(τ:ℂ)) := by
  unfold Quadratic.characteristic Quadratic.queryPolynomial
  push_cast
  ring

theorem characteristic_norm_slow_bound (β τ h lam : ℝ) (z : ℂ) :
    ‖Quadratic.characteristic β τ h lam z‖≤
      ‖z-1‖^2+|1-β| * ‖z-1‖+|h*lam| *((1+|τ|)*‖z‖+|τ|) := by
  have hq : ‖((1+τ:ℝ):ℂ)*z-(τ:ℂ)‖≤(1+|τ|)*‖z‖+|τ| := by
    have hh := norm_sub_le (((1+τ:ℝ):ℂ)*z) (τ:ℂ)
    rw [norm_mul,Complex.norm_real,Complex.norm_real,Real.norm_eq_abs,Real.norm_eq_abs] at hh
    have ha : |1+τ|≤1+|τ| := by simpa only [abs_one] using abs_add_le (1:ℝ) τ
    have hm := mul_le_mul_of_nonneg_right ha (norm_nonneg z)
    linarith
  have h0 := norm_add_le ((z-1)^2+((1-β:ℝ):ℂ)*(z-1))
    (((h*lam:ℝ):ℂ)*(((1+τ:ℝ):ℂ)*z-(τ:ℂ)))
  have h1 := norm_add_le ((z-1)^2) (((1-β:ℝ):ℂ)*(z-1))
  rw [norm_mul,Complex.norm_real,Real.norm_eq_abs] at h0
  rw [norm_pow,norm_mul,Complex.norm_real,Real.norm_eq_abs] at h1
  have hm := mul_le_mul_of_nonneg_left hq (abs_nonneg (h*lam))
  rw [characteristic_slow_factor]
  linarith

def layerProductConstant (c b M : ℝ) : ℝ :=
  let R := 1+|c|
  let N := R+1
  let Q := (1+M)*R+M
  (c^2+2*R*b+M*N+M*Q)*(N^2+M*N+M*Q)

private theorem product_bound_of_compact {ε θ h τ c b M : ℝ}
    (hε : 0<ε) (hε1 : ε≤1) (hb : 0<b) (hM : 1≤M)
    (hθ : |θ|≤M) (hh : |h|≤M) (hτ : |τ|≤M) :
    ∀ ω : ℝ,1-Real.cos ω≤b*Real.sqrt ε →
      ‖Quadratic.characteristic (1-θ*ε) τ h (ε^2) (circle (1-c*ε) ω)*
        star (Quadratic.characteristic (1-θ*ε) τ h 1 (circle (1-c*ε) ω))‖≤layerProductConstant c b M*Real.sqrt ε := by
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
  change _≤Cs*Cf*Real.sqrt ε
  let z := circle (1-c*ε) ω
  let n : ℝ := ‖z-1‖
  have hs := Real.sq_sqrt hε.le
  have heS : ε≤Real.sqrt ε := by nlinarith [Real.sqrt_nonneg ε]
  have he2S : ε^2≤Real.sqrt ε := by nlinarith
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
  have hnS : n^2≤(c^2+2*R*b)*Real.sqrt ε := by
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
  have hslow : ‖Quadratic.characteristic (1-θ*ε) τ h (ε^2) z‖≤Cs*Real.sqrt ε := by
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
  have hp := mul_le_mul hslow hfast (norm_nonneg _) (mul_nonneg hCs.le (Real.sqrt_nonneg ε))
  nlinarith

namespace Scaling
variable {A : Type*} {l : Filter A} {θ y τ : ℝ} (F : Scaling A l θ y τ)

theorem layer_characteristic_product_bound (c b : ℝ) (hb : 0<b) :
    ∃ C : ℝ,0<C ∧ ∀ᶠ a in l,∀ ω : ℝ,
      1-Real.cos ω≤b*Real.sqrt (F.epsilon a) →
      ‖Spread.product (F.tuning a) (F.epsilon a^2) 1 (1-c*F.epsilon a) ω‖≤
        C*Real.sqrt (F.epsilon a) := by
  let M : ℝ := 2+|θ|+|y|+|τ|
  have hM : 1≤M := by dsimp [M];linarith [abs_nonneg θ,abs_nonneg y,abs_nonneg τ]
  have hMp : 0<M := by linarith
  have hθM : |θ|<M := by dsimp [M];linarith [abs_nonneg y,abs_nonneg τ]
  have hyM : |y|<M := by dsimp [M];linarith [abs_nonneg θ,abs_nonneg τ]
  have hτM : |τ|<M := by dsimp [M];linarith [abs_nonneg θ,abs_nonneg y]
  refine ⟨layerProductConstant c b M,?_,?_⟩
  · unfold layerProductConstant
    positivity
  · filter_upwards [F.epsilon_pos,F.epsilon_zero.eventually (eventually_lt_nhds (by norm_num : (0:ℝ)<1)),
      F.theta_tendsto.abs.eventually (eventually_lt_nhds hθM),
      F.step_tendsto.abs.eventually (eventually_lt_nhds hyM),
      F.tau_tendsto.abs.eventually (eventually_lt_nhds hτM),F.beta_eq]
      with a he he1 ht hy htau hbeta
    intro ω hω
    unfold Spread.product
    rw [hbeta]
    exact product_bound_of_compact he he1.le hb hM ht.le hy.le htau.le ω hω
end Scaling
end
end nesterov.TwoStep
