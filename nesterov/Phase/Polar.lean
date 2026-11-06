import nesterov.Spectral.Feasibility
import Mathlib.Analysis.SpecialFunctions.Complex.Arg
import polyak.General.Regions.SingleHarmonic

/-!
Article: Equation (Theta), Lemma `lem:angle` and the rational phase criterion.
Use: a branch-correct actual complex argument and exact two-direction geometry.
-/
namespace nesterov.Phase
noncomputable section
open Set

def mode (g s : ℝ) : ℂ := (g:ℂ)+2*Complex.I*s
def angle (g s : ℝ) : ℝ := (mode g s).arg
def magnitude (g s : ℝ) : ℝ := ‖mode g s‖

@[simp] theorem mode_re (g s : ℝ) : (mode g s).re=g := by simp [mode]
@[simp] theorem mode_im (g s : ℝ) : (mode g s).im=2*s := by simp [mode]

theorem magnitude_pos {g s : ℝ} (h : g≠0 ∨ s≠0) : 0<magnitude g s := by
  apply norm_pos_iff.mpr
  intro hz
  have hre := congrArg Complex.re hz
  have him := congrArg Complex.im hz
  simp only [mode_re,mode_im,Complex.zero_re,Complex.zero_im] at hre him
  rcases h with h|h
  · exact h hre
  · exact h (by linarith)

theorem magnitude_cos_angle (g s : ℝ) : magnitude g s*Real.cos (angle g s)=g := by
  simpa only [magnitude,angle,mode_re] using Complex.norm_mul_cos_arg (mode g s)

theorem magnitude_sin_angle (g s : ℝ) : magnitude g s*Real.sin (angle g s)=2*s := by
  simpa only [magnitude,angle,mode_im] using Complex.norm_mul_sin_arg (mode g s)

theorem angle_range (g s : ℝ) : -Real.pi<angle g s ∧ angle g s≤Real.pi :=
  ⟨Complex.neg_pi_lt_arg _,Complex.arg_le_pi _⟩

theorem angle_pos_lt_pi {g s : ℝ} (hs : 0<s) : 0<angle g s ∧ angle g s<Real.pi := by
  have hnonneg : 0≤angle g s := Complex.arg_nonneg_iff.mpr (by simpa using hs.le)
  have hne : angle g s≠0 := by
    intro hz
    have hh := magnitude_sin_angle g s
    rw [hz,Real.sin_zero,mul_zero] at hh
    linarith
  refine ⟨lt_of_le_of_ne hnonneg (Ne.symm hne),?_⟩
  exact Complex.arg_lt_pi_iff.mpr (Or.inr (by simpa using hs.ne'))

/-- Both exact identities in (defect), with an arbitrary polar representative. -/
theorem lag_one_polar_identity (R Θ ω : ℝ) :
    R*Real.cos Θ*(1-Real.cos ω)-R*Real.sin Θ*Real.sin ω=
      2*R*Real.sin (ω/2)*Real.sin ((ω-2*Θ)/2) ∧
    R*Real.cos Θ*(1-Real.cos ω)+R*Real.sin Θ*Real.sin ω=
      2*R*Real.sin (ω/2)*Real.sin ((ω+2*Θ)/2) := by
  have h₁ := Real.two_mul_sin_mul_sin (ω/2) ((ω-2*Θ)/2)
  have h₂ := Real.two_mul_sin_mul_sin (ω/2) ((ω+2*Θ)/2)
  rw [show ω/2-(ω-2*Θ)/2=Θ by ring,
    show ω/2+(ω-2*Θ)/2=ω-Θ by ring,Real.cos_sub] at h₁
  rw [show ω/2-(ω+2*Θ)/2= -Θ by ring,
    show ω/2+(ω+2*Θ)/2=ω+Θ by ring,Real.cos_neg,Real.cos_add] at h₂
  constructor
  · linear_combination -R*h₁
  · linear_combination -R*h₂

theorem lag_one_phase_identity (g s ω : ℝ) :
    g*(1-Real.cos ω)-2*s*Real.sin ω=
      2*magnitude g s*Real.sin (ω/2)*Real.sin ((ω-2*angle g s)/2) ∧
    g*(1-Real.cos ω)+2*s*Real.sin ω=
      2*magnitude g s*Real.sin (ω/2)*Real.sin ((ω+2*angle g s)/2) := by
  have hh := lag_one_polar_identity (magnitude g s) (angle g s) ω
  rwa [magnitude_cos_angle,magnitude_sin_angle] at hh

theorem two_directions_abs (ω Θ : ℝ) :
    (∀ n : ℕ,1≤n → Real.cos (n*ω-Θ)≤Real.cos Θ ∧ Real.cos (n*ω+Θ)≤Real.cos Θ) ↔
    (∀ n : ℕ,1≤n → Real.cos (n*ω-|Θ|)≤Real.cos |Θ| ∧ Real.cos (n*ω+|Θ|)≤Real.cos |Θ|) := by
  by_cases hΘ : 0≤Θ
  · simp only [abs_of_nonneg hΘ]
  · rw [abs_of_nonpos (le_of_not_ge hΘ),Real.cos_neg]
    simp only [sub_neg_eq_add,←sub_eq_add_neg]
    exact ⟨fun h n hn=>(h n hn).symm,fun h n hn=>(h n hn).symm⟩

/-- Exact source rational criterion for both signs of the principal phase. -/
theorem rational_phase_criterion {j K : ℕ} (hcop : j.Coprime K) (hK : 2≤K)
    {Θ : ℝ} (hΘ : |Θ|≤Real.pi) :
    (∀ n : ℕ,1≤n → Real.cos (n*(2*Real.pi*j/K)-Θ)≤Real.cos Θ ∧
      Real.cos (n*(2*Real.pi*j/K)+Θ)≤Real.cos Θ) ↔ |Θ|≤Real.pi/K := by
  rw [two_directions_abs]
  exact polyak.General.Regions.single_harmonic_phase_criterion hcop hK (abs_nonneg _) hΘ

end
end nesterov.Phase
