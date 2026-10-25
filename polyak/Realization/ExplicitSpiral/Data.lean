import polyak.Realization.Polyak
import polyak.Spiral.Feasibility

/-!
Article: (spirallower), the initialized special spiral with Y=2.
Use: keep its function values unchanged at time zero, while correcting only
the initial gradient and adjoining the explicit decaying scalar coordinate.
Proof: the data below are the independently specified source formulas.
-/

namespace polyak.Realization.ExplicitSpiral
noncomputable section
open Interpolation

/-- Article: the planar geometric wave, including its minimizer datum. -/
def modePosition (z : ℂ) : Option ℕ → ℂ
  | none => 0
  | some k => z^k

/-- Article: stationary planar gradients before the initialization correction. -/
def modeGradient (z s : ℂ) (i : Option ℕ) : ℂ := s*modePosition z i

/-- Article: the unchanged wave values, including time zero. -/
def modeValue (z s : ℂ) (C : ℝ) : Option ℕ → ℝ
  | none => 0
  | some k => (C+2*s.re)/4*Complex.normSq (z^k)

/-- Article: initialized positions with the fixed scalar amplitude Y=2. -/
def position (z : ℂ) (q : ℝ) : Option ℕ → WithLp 2 (ℂ × ℝ) :=
  startupPosition (modePosition z) 0 (2*q) (q^2) 0 2

/-- Article: the first-step correction is imposed by the prescribed zero impulse. -/
def gradient (z s : ℂ) (q : ℝ) : Option ℕ → WithLp 2 (ℂ × ℝ) :=
  startupGradient (modeGradient z s) (initialGradient (modePosition z) 0 (2*q) (q^2))
    0 (2*q) (q^2) 0 2

/-- Article: the extra coordinate has τ=0, hence contributes no function value. -/
def value (z s : ℂ) (C : ℝ) : Option ℕ → ℝ := modeValue z s C

/-- Article: the source initial position is exactly (1,2). -/
theorem position_zero (z : ℂ) (q : ℝ) :
    position z q (some 0)=WithLp.toLp 2 ((1 : ℂ),(2 : ℝ)) := by
  simp [position,startupPosition,productPosition,modePosition,scalarPosition,response_zero]

/-- Article: the prescribed initial norm is √5, independently of the condition number. -/
theorem norm_position_zero (z : ℂ) (q : ℝ) : ‖position z q (some 0)‖=Real.sqrt 5 := by
  have hs : ‖position z q (some 0)‖^2=5 := by
    rw [position_zero,WithLp.prod_norm_sq_eq_of_L2]
    norm_num
  have hr := Real.sq_sqrt (show (0 : ℝ) ≤ 5 by norm_num)
  nlinarith [norm_nonneg (position z q (some 0)),Real.sqrt_nonneg (5 : ℝ)]

/-- Article: the added coordinate has exactly the source even/odd powers. -/
theorem scalar_even_odd (z : ℂ) (q : ℝ) (n : ℕ) :
    (position z q (some (2*n))).snd=2*(-q^2)^n ∧
    (position z q (some (2*n+1))).snd=2*(-q^2)^(n+1) := by
  simp only [position,startupPosition,productPosition,scalarPosition,mul_zero,zero_add,
    WithLp.toLp_snd]
  exact And.intro (congrArg (fun a => 2*a) (response_polyak_even q n).1)
    (congrArg (fun a => 2*a) (response_polyak_even q n).2)

/-- Article: the planar component gives the quantitative norm lower bound. -/
theorem norm_mode_le_position (z : ℂ) (q : ℝ) (k : ℕ) :
    ‖z‖^k ≤ ‖position z q (some k)‖ := by
  rw [← norm_pow]
  exact norm_le_startupPosition (modePosition z) 0 (2*q) (q^2) 0 2 k

/-- Article: the exact correction Δ=q(1-z⁻¹)/2. -/
def defect (z : ℂ) (q : ℝ) : ℂ := (q : ℂ)/2*(1-z⁻¹)

/-- Article: the source stationary multiplier. -/
def multiplier (z : ℂ) (q : ℝ) : ℂ := (z+(q : ℂ)^2/z)/(2*(q : ℂ))

/-- Article: s+Δ equals the actual gradient required by the first step. -/
theorem initialGradient_eq (z : ℂ) (hz : z≠0) {q : ℝ} (hq : q≠0) :
    initialGradient (modePosition z) 0 (2*q) (q^2)=multiplier z q+defect z q := by
  have hqc : (q : ℂ)≠0 := by exact_mod_cast hq
  simp only [initialGradient,modePosition,pow_one,pow_zero,zero_sub,neg_smul,
    Complex.real_smul,Complex.ofReal_div,Complex.ofReal_one,Complex.ofReal_mul,
    Complex.ofReal_ofNat,Complex.ofReal_pow]
  unfold multiplier defect
  simp only [div_eq_mul_inv]
  field_simp [hz]
  ring

end
end polyak.Realization.ExplicitSpiral
