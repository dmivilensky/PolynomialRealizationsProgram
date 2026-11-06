import nesterov.Robust.TMM
import Mathlib.Tactic.Module

/-! Elimination of the auxiliary HNAG state and the exact HNAG+/TMM dictionary. -/
namespace nesterov.Momentum.HNAG
noncomputable section

/-- Arbitrary HNAG initial states correspond to arbitrary consecutive query iterates. -/
def queryStateEquiv {E : Type*} [AddCommGroup E] [Module ℝ E]
    (g : E→E) (a b γ : ℝ) (hγa : γ*a≠0) (hD : 1+γ*a≠0) : (E × E) ≃ (E × E) where
  toFun p := (p.1,(1+γ*a)⁻¹ • (p.1+(γ*a) • p.2-(a*b) • g p.1))
  invFun q := (q.1,(γ*a)⁻¹ • ((1+γ*a) • q.2-q.1+(a*b) • g q.1))
  left_inv p := by
    apply Prod.ext
    · rfl
    · change (γ*a)⁻¹ • ((1+γ*a) • ((1+γ*a)⁻¹ •
        (p.1+(γ*a) • p.2-(a*b) • g p.1))-p.1+(a*b) • g p.1)=p.2
      rw [smul_smul,mul_inv_cancel₀ hD,one_smul]
      rw [show p.1+(γ*a) • p.2-(a*b) • g p.1-p.1+(a*b) • g p.1=(γ*a) • p.2 by abel]
      rw [smul_smul,inv_mul_cancel₀ hγa,one_smul]
  right_inv q := by
    apply Prod.ext
    · rfl
    · change (1+γ*a)⁻¹ • (q.1+(γ*a) • ((γ*a)⁻¹ •
        ((1+γ*a) • q.2-q.1+(a*b) • g q.1))-(a*b) • g q.1)=q.2
      rw [smul_smul,mul_inv_cancel₀ hγa,one_smul]
      rw [show q.1+((1+γ*a) • q.2-q.1+(a*b) • g q.1)-(a*b) • g q.1=(1+γ*a) • q.2 by abel]
      rw [smul_smul,inv_mul_cancel₀ hD,one_smul]

private theorem affine_norm_bound {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {g : E→E} {L : ℝ} (hL : 0≤L) (hg : ∀ x,‖g x‖≤L*‖x‖)
    (c₁ c₂ c₃ : ℝ) (x y : E) :
    ‖c₁ • x+c₂ • y+c₃ • g x‖≤
      (|c₁|+|c₂|+|c₃| *L)*(‖x‖+‖y‖) := by
  calc
    _≤‖c₁ • x‖+‖c₂ • y‖+‖c₃ • g x‖ :=
      (norm_add_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)
    _=|c₁| *‖x‖+|c₂| *‖y‖+|c₃| *‖g x‖ := by simp only [norm_smul,Real.norm_eq_abs]
    _≤|c₁| *(‖x‖+‖y‖)+|c₂| *(‖x‖+‖y‖)+|c₃| *(L*(‖x‖+‖y‖)) := by
      gcongr
      · exact le_add_of_nonneg_right (norm_nonneg y)
      · exact le_add_of_nonneg_left (norm_nonneg x)
      · exact (hg x).trans (mul_le_mul_of_nonneg_left
          (le_add_of_nonneg_right (norm_nonneg y)) hL)
    _=_ := by ring

/-- Uniform objective-independent comparisons for the HNAG change of state. -/
theorem queryStateEquiv_norms {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {g : E→E} {L : ℝ} (hL : 0≤L) (hg : ∀ x,‖g x‖≤L*‖x‖)
    (a b γ : ℝ) (hγa : γ*a≠0) (hD : 1+γ*a≠0) :
    let e := queryStateEquiv g a b γ hγa hD
    (∀ p,‖(e p).1‖+‖(e p).2‖≤
      (1+|(1+γ*a)⁻¹| *(1+|γ*a|+|a*b| *L))*(‖p.1‖+‖p.2‖)) ∧
    (∀ q,‖(e.symm q).1‖+‖(e.symm q).2‖≤
      (1+|(γ*a)⁻¹| *(1+|1+γ*a|+|a*b| *L))*(‖q.1‖+‖q.2‖)) := by
  constructor
  · intro p
    have h := affine_norm_bound hL hg 1 (γ*a) (-(a*b)) p.1 p.2
    simp only [one_smul,neg_smul,←sub_eq_add_neg,abs_one,abs_neg] at h
    change ‖p.1‖+‖(1+γ*a)⁻¹ • (p.1+(γ*a) • p.2-(a*b) • g p.1)‖≤_
    rw [norm_smul,Real.norm_eq_abs]
    calc
      _≤(‖p.1‖+‖p.2‖)+|(1+γ*a)⁻¹| *
          ((1+|γ*a|+|a*b| *L)*(‖p.1‖+‖p.2‖)) :=
        add_le_add (le_add_of_nonneg_right (norm_nonneg p.2))
          (mul_le_mul_of_nonneg_left h (abs_nonneg _))
      _=_ := by ring
  · intro q
    have h := affine_norm_bound hL hg (-1) (1+γ*a) (a*b) q.1 q.2
    have he : (-1:ℝ) • q.1+(1+γ*a) • q.2+(a*b) • g q.1=
        (1+γ*a) • q.2-q.1+(a*b) • g q.1 := by module
    rw [he] at h
    norm_num only [abs_neg,abs_one] at h
    change ‖q.1‖+‖(γ*a)⁻¹ • ((1+γ*a) • q.2-q.1+(a*b) • g q.1)‖≤_
    rw [norm_smul,Real.norm_eq_abs]
    calc
      _≤(‖q.1‖+‖q.2‖)+|(γ*a)⁻¹| *
          ((1+|1+γ*a|+|a*b| *L)*(‖q.1‖+‖q.2‖)) :=
        add_le_add (le_add_of_nonneg_right (norm_nonneg q.2))
          (mul_le_mul_of_nonneg_left h (abs_nonneg _))
      _=_ := by ring

/-- The three consecutive IMEX updates imply the physical two-step recurrence. -/
theorem eliminate {E : Type*} [AddCommGroup E] [Module ℝ E]
    (a b γ μ : ℝ) (x₀ x₁ x₂ y₀ y₁ g₀ g₁ : E)
    (hx₀ : (1+γ*a) • x₁=x₀+(γ*a) • y₀-(a*b) • g₀)
    (hy : (1+a) • y₁=y₀+a • x₁-(a/μ) • g₁)
    (hx₁ : (1+γ*a) • x₂=x₁+(γ*a) • y₁-(a*b) • g₁) :
    ((1+a)*(1+γ*a)) • x₂=(((1+a)*(1+γ*a))+1) • x₁-x₀-
      (γ*a^2/μ+a*b*(1+a)) • g₁+(a*b) • g₀ := by
  have he : (γ*a) • y₀=(1+γ*a) • x₁-x₀+(a*b) • g₀ := by
    rw [hx₀]
    abel
  calc
    _=(1+a) • ((1+γ*a) • x₂) := by module
    _=(1+a) • (x₁+(γ*a) • y₁-(a*b) • g₁) := by rw [hx₁]
    _=(1+a) • x₁+(γ*a) • ((1+a) • y₁)-(a*b*(1+a)) • g₁ := by module
    _=(1+a) • x₁+(γ*a) • (y₀+a • x₁-(a/μ) • g₁)-(a*b*(1+a)) • g₁ := by rw [hy]
    _=((1+a)+γ*a^2) • x₁+(γ*a) • y₀-(γ*a^2/μ+a*b*(1+a)) • g₁ := by
      simp only [div_eq_mul_inv]
      module
    _=_ := by rw [he];module

theorem correction_parameters {a γ μ : ℝ} (ha : 0<a) (hγ : 0<γ) (hμ : 0<μ) :
    let D := (1+a)*(1+γ*a)
    let h := (γ*a^2/μ+a)/D
    let τ := 1/(γ*a^2/μ+a)
    h*(1+τ)=(γ*a^2/μ+1+a)/D ∧ h*τ=1/D := by
  dsimp
  have hd : (1+a)*(1+γ*a)≠0 := by positivity
  have hs : γ*a^2/μ+a≠0 := by positivity
  constructor
  · field_simp [hd,hs]
    ring
  · field_simp [hd,hs]

/-- The normalized γ=1, a=√2 ε update gives the literal HNAG++ tuning. -/
theorem plusPlus_parameters {ε : ℝ} (hε : 0<ε) :
    let a := Real.sqrt 2*ε
    let D := (1+a)^2
    (a^2/ε^2+a)/D=(2+a)/D ∧
      (1/D)/((2+a)/D)=1/(2+a) := by
  dsimp
  have h1 : 1+Real.sqrt 2*ε≠0 := by positivity
  have h2 : 2+Real.sqrt 2*ε≠0 := by positivity
  have hs := Real.sq_sqrt (by norm_num : (0:ℝ)≤2)
  constructor
  · field_simp [hε.ne']
    nlinarith
  · field_simp [h1,h2]

/-- At the HNAG+ step a=ε/(1−ε), all three parameters are exactly TMM's. -/
theorem plus_parameters {ε : ℝ} (hε : 0<ε) (hε1 : ε<1) :
    let a := ε/(1-ε)
    let D := (1+a)*(1+2*a)
    1/D=(1-ε)^2/(1+ε) ∧
      (2*a^2/ε^2+a)/D=2-ε ∧
        (1/D)/((2*a^2/ε^2+a)/D)=(1-ε)^2/((2-ε)*(1+ε)) := by
  dsimp
  have h0 : ε≠0 := hε.ne'
  have h1 : 1-ε≠0 := by linarith
  have hp : 1+ε≠0 := by positivity
  have hm : 2-ε≠0 := by linarith
  have hd : (1+ε/(1-ε))*(1+2*(ε/(1-ε)))=(1+ε)/(1-ε)^2 := by
    field_simp [h1]
    ring
  have he : (2*(ε/(1-ε))^2/ε^2+ε/(1-ε))/
      ((1+ε/(1-ε))*(1+2*(ε/(1-ε))))=2-ε := by
    rw [hd]
    field_simp [h0,h1,hp]
    ring
  refine ⟨?_,he,?_⟩
  · rw [hd]
    field_simp [h1,hp]
  · rw [he,hd]
    field_simp [h1,hp,hm]

/-- The complete normalized HNAG+ tuning equals the proved TMM design. -/
theorem plus_eq_tmm (D : Robust.Design) (hT : D.kappa*(1-D.rho)^2=1) :
    let ε := 1-D.rho
    let a := ε/(1-ε)
    let R := (1+a)*(1+2*a)
    D.beta=1/R ∧ D.step=(2*a^2/ε^2+a)/R ∧
      D.tau=(1/R)/((2*a^2/ε^2+a)/R) := by
  have h := plus_parameters D.gap_pos (show 1-D.rho<1 by linarith [D.rho_pos])
  dsimp only at h ⊢
  rw [h.2.2,h.2.1,h.1]
  constructor
  · rw [D.tmm_beta hT]
    congr 1 <;> ring
  constructor
  · rw [D.tmm_step hT]
    ring
  · rw [D.tmm_tau hT]
    congr 1 <;> ring

end
end nesterov.Momentum.HNAG
