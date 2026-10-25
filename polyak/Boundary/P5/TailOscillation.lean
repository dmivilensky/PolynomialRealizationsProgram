import polyak.Boundary.P5.TailHyperbolic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

/-!
Article: Lemma p5tail, perturbation of the exact three-cycle.
Use: separate the uniformly small phase/amplitude changes from the radial growth.
-/

noncomputable section
namespace polyak.Boundary.P5
open Spectral

/-- Article: the signed oscillatory part removed from the growing radial term. -/
def tailOsc (u : ℝ) (n : ℕ) (σ : ℝ) (c : Frequency) : ℝ :=
  g u c*chebT n c-σ*lagB u n c

/-- Article: the oscillatory part of the exact three-cycle. -/
def cycleOsc (n : ℕ) (σ : ℝ) : ℝ :=
  (1/2 : ℝ)*Real.cos (n*(2*Real.pi/3))-
    σ*(Real.sqrt 3/2)*Real.sin (n*(2*Real.pi/3))

/-- Article: a generic Lipschitz bound for simultaneous changes of phase and amplitudes. -/
theorem phase_amplitude_change (a b a₀ b₀ θ θ₀ : ℝ) :
    |a*Real.cos θ+b*Real.sin θ-(a₀*Real.cos θ₀+b₀*Real.sin θ₀)| ≤
      |a-a₀|+|b-b₀|+(|a₀|+|b₀|)*|θ-θ₀| := by
  let r₀ := (a-a₀)*Real.cos θ
  let r₁ := (b-b₀)*Real.sin θ
  let r₂ := a₀*(Real.cos θ-Real.cos θ₀)
  let r₃ := b₀*(Real.sin θ-Real.sin θ₀)
  have he : a*Real.cos θ+b*Real.sin θ-(a₀*Real.cos θ₀+b₀*Real.sin θ₀)=r₀+r₁+r₂+r₃ := by
    dsimp [r₀,r₁,r₂,r₃]
    ring
  have h₀ : |r₀| ≤ |a-a₀| := by
    dsimp [r₀]
    rw [abs_mul]
    simpa only [mul_one] using mul_le_mul_of_nonneg_left (Real.abs_cos_le_one θ) (abs_nonneg (a-a₀))
  have h₁ : |r₁| ≤ |b-b₀| := by
    dsimp [r₁]
    rw [abs_mul]
    simpa only [mul_one] using mul_le_mul_of_nonneg_left (Real.abs_sin_le_one θ) (abs_nonneg (b-b₀))
  have h₂ : |r₂| ≤ |a₀| * |θ-θ₀| := by
    dsimp [r₂]
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_left (Real.abs_cos_sub_cos_le θ θ₀) (abs_nonneg a₀)
  have h₃ : |r₃| ≤ |b₀| * |θ-θ₀| := by
    dsimp [r₃]
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_left (Real.abs_sin_sub_sin_le θ θ₀) (abs_nonneg b₀)
  rw [he]
  have htri₀ := abs_add_le r₀ r₁
  have htri₁ := abs_add_le (r₀+r₁) r₂
  have htri₂ := abs_add_le (r₀+r₁+r₂) r₃
  nlinarith

/-- Article: source main-atom bounds give an error at most 3h+nh/2. -/
theorem main_oscillation_change {h u : ℝ} {x : Frequency} (_hh : 0 ≤ h)
    (hg : |g u x-1/2| ≤ h)
    (ha : |2*u*Real.sin (Real.arccos x)-Real.sqrt 3/2| ≤ 2*h)
    (hθ : |Real.arccos (x : ℝ)-2*Real.pi/3| ≤ h/3)
    (n : ℕ) (hn : 1 ≤ n) (σ : ℝ) (hσ : σ=1 ∨ σ= -1) :
    |tailOsc u n σ x-cycleOsc n σ| ≤ 3*h+n*h/2 := by
  have hs : |σ|=1 := by rcases hσ with rfl | rfl <;> norm_num
  have hsqrt : 0 ≤ Real.sqrt 3 := Real.sqrt_nonneg _
  have hsqrt2 : Real.sqrt 3 ≤ 2 := by nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3)]
  have hweight : |(1/2 : ℝ)|+|(-σ)*(Real.sqrt 3/2)| ≤ 3/2 := by
    rw [abs_mul,abs_neg,hs,one_mul]
    rw [abs_of_nonneg (by positivity : (0 : ℝ) ≤ Real.sqrt 3/2)]
    norm_num
    linarith
  have hb : |(-σ)*(2*u*Real.sin (Real.arccos x))-(-σ)*(Real.sqrt 3/2)| ≤ 2*h := by
    rw [← mul_sub,abs_mul,abs_neg,hs,one_mul]
    exact ha
  have hphase : |(n : ℝ)*Real.arccos (x : ℝ)-n*(2*Real.pi/3)| ≤ n*h/3 := by
    rw [← mul_sub,abs_mul,abs_of_nonneg (Nat.cast_nonneg n)]
    have hm := mul_le_mul_of_nonneg_left hθ (Nat.cast_nonneg n)
    nlinarith
  have hp := mul_le_mul_of_nonneg_right hweight
    (abs_nonneg ((n : ℝ)*Real.arccos (x : ℝ)-n*(2*Real.pi/3)))
  have hp' := mul_le_mul_of_nonneg_left hphase (by norm_num : (0 : ℝ) ≤ 3/2)
  have he := phase_amplitude_change (g u x) ((-σ)*(2*u*Real.sin (Real.arccos x)))
    (1/2) ((-σ)*(Real.sqrt 3/2)) (n*Real.arccos (x : ℝ)) (n*(2*Real.pi/3))
  have heq : tailOsc u n σ x-cycleOsc n σ=
      g u x*Real.cos (n*Real.arccos (x : ℝ))+(-σ)*(2*u*Real.sin (Real.arccos x))*
        Real.sin (n*Real.arccos (x : ℝ))-
      ((1/2)*Real.cos (n*(2*Real.pi/3))+(-σ)*(Real.sqrt 3/2)*Real.sin (n*(2*Real.pi/3))) := by
    rw [tailOsc,Waves.chebT_arccos,lagB_trig u n hn x]
    unfold cycleOsc
    ring
  rw [heq]
  nlinarith

/-- Article: each actual atom has oscillatory amplitude at most two in this parameter box. -/
theorem tailOsc_abs_le_two {u : ℝ} (hu : 0 ≤ u) (hu1 : u ≤ 11/20)
    (n : ℕ) (hn : 1 ≤ n) (σ : ℝ) (hσ : σ=1 ∨ σ= -1) (c : Frequency) :
    |tailOsc u n σ c| ≤ 2 := by
  have hδ : -σ=1 ∨ -σ= -1 := by rcases hσ with rfl | rfl <;> norm_num
  have he := lag_oscillation_bound u n hn c (-σ) hδ
  have hs : u^2 ≤ 1 := by nlinarith
  dsimp only [tailOsc]
  have hh : g u c*chebT n c-σ*lagB u n c=g u c*chebT n c+(-σ)*lagB u n c := by ring
  rw [hh]
  exact he.trans (by nlinarith [sq_nonneg (c : ℝ)])

/-- Article: the two trigonometric amplitudes are compared with the exact three-cycle. -/
theorem mixed_oscillation_change {h u p : ℝ} {x y : Frequency}
    (hh : 0 ≤ h) (hu : 0 ≤ u) (hu1 : u ≤ 11/20) (hp : 0 ≤ p) (hp3 : p ≤ 3*h)
    (hg : |g u x-1/2| ≤ h)
    (ha : |2*u*Real.sin (Real.arccos x)-Real.sqrt 3/2| ≤ 2*h)
    (hθ : |Real.arccos (x : ℝ)-2*Real.pi/3| ≤ h/3)
    (n : ℕ) (hn : 1 ≤ n) (σ : ℝ) (hσ : σ=1 ∨ σ= -1) :
    |(1-p)*tailOsc u n σ x+p*tailOsc u n σ y-cycleOsc n σ| ≤ 15*h+n*h/2 := by
  have hx := main_oscillation_change hh hg ha hθ n hn σ hσ
  have hax := tailOsc_abs_le_two hu hu1 n hn σ hσ x
  have hay := tailOsc_abs_le_two hu hu1 n hn σ hσ y
  have hd : |tailOsc u n σ y-tailOsc u n σ x| ≤ 4 :=
    (abs_sub _ _).trans (by linarith)
  have hpd : |p*(tailOsc u n σ y-tailOsc u n σ x)| ≤ 12*h := by
    rw [abs_mul,abs_of_nonneg hp]
    have hm := mul_le_mul_of_nonneg_left hd hp
    nlinarith
  have he : (1-p)*tailOsc u n σ x+p*tailOsc u n σ y-cycleOsc n σ=
      (tailOsc u n σ x-cycleOsc n σ)+p*(tailOsc u n σ y-tailOsc u n σ x) := by ring
  rw [he]
  exact (abs_add_le _ _).trans (by linarith)

/-- Article: the exact critical three-cycle has nonnegative raw slacks at every lag. -/
theorem cycle_raw_nonneg (n : ℕ) (hn : 1 ≤ n) (σ : ℝ) (hσ : σ=1 ∨ σ= -1) :
    0 ≤ (1/2 : ℝ)-cycleOsc n σ := by
  have h := (Spiral.feasibleU 0).2 n hn
  rw [meanA_eq_integral,meanB_eq_integral,Spiral.avg_spectrum,Spiral.avg_spectrum] at h
  have hangle : Real.arccos (Spiral.atom 0 : ℝ)=2*Real.pi/3 := Spiral.angle_zero
  have hs : Real.sin (2*Real.pi/3)=Real.sqrt 3/2 := by
    rw [show 2*Real.pi/3=Real.pi-Real.pi/3 by ring,Real.sin_pi_sub,Real.sin_pi_div_three]
  simp only [Spiral.twist_zero,Spiral.valueConstant_zero,zero_mul,mul_zero,add_zero,sub_zero] at h
  rw [lagA,lagD,Waves.chebT_arccos,lagB_trig (1/2) n hn (Spiral.atom 0),hangle,hs] at h
  have hg : g (1/2) (Spiral.atom 0)=(1/2 : ℝ) := by
    norm_num [g,Spiral.atom,Spiral.cosine,Spiral.G]
  rw [hg] at h
  simp only [mul_zero,Real.cosh_zero] at h
  unfold cycleOsc
  rcases hσ with rfl | rfl <;> norm_num at * <;> linarith [h.1,h.2]

end polyak.Boundary.P5
