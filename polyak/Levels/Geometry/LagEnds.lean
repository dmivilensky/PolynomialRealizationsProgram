import polyak.Levels.Geometry.Ends
import polyak.Levels.Program.Pinning

/-! The endpoint lag jet of the actual analytic extension. The first
second-order coefficient is independent of the cotangent shift. -/
noncomputable section
namespace polyak.Levels.Geometry
open General Filter
open scoped Topology

def tau (q : Tuning) : ℝ := -1/q.Xi 1

theorem tau_pos (q : Tuning) : 0<tau q := div_pos_of_neg_of_neg (by norm_num) q.Xi_one_neg

theorem hasDerivAt_endAngle_zero (q : Tuning) (s : ℝ) :
    HasDerivAt (endAngle q s) (-tau q) 0 := by
  have hn : -shiftNumerator q s 0≠0 := by
    simpa only [shiftNumerator,Real.cos_zero,Real.sin_zero,mul_zero,add_zero,neg_ne_zero] using q.Xi_one_neg.ne
  have hd := (analyticAt_shiftNumerator q s 0).differentiableAt.hasDerivAt.neg
  have hquot:=(Real.hasDerivAt_sin 0).div hd hn
  have hh:=hquot.arctan.const_sub Real.pi
  unfold endAngle
  convert hh using 1
  simp [tau,shiftNumerator]
  field_simp

def extendedLag (θ : ℝ→ℝ) (n : ℤ) (ω : ℝ) : ℝ :=
  Real.cos (θ ω)-Real.cos ((n:ℝ)*ω-θ ω)

def extendedLagFirst (θ : ℝ→ℝ) (n : ℤ) (ω : ℝ) : ℝ :=
  -deriv θ ω*Real.sin (θ ω)+((n:ℝ)-deriv θ ω)*Real.sin ((n:ℝ)*ω-θ ω)

theorem analytic_lag_first_zero {θ : ℝ→ℝ} (hθ : AnalyticAt ℝ θ 0)
    (h0 : θ 0=Real.pi) (n : ℤ) : deriv (extendedLag θ n) 0=0 := by
  unfold extendedLag
  rw [(hasDerivAt_lag_phase hθ.differentiableAt.hasDerivAt n).deriv]
  simp only [h0,Real.sin_pi,mul_zero,zero_sub,Real.sin_neg,neg_zero,add_zero]

/-- The general analytic lag jet at a phase-pi endpoint. -/
theorem analytic_lag_second_zero {θ : ℝ→ℝ} (hθ : AnalyticAt ℝ θ 0)
    (h0 : θ 0=Real.pi) (n : ℤ) :
    deriv^[2] (extendedLag θ n) 0= -(n:ℝ)*((n:ℝ)-2*deriv θ 0) := by
  have he : deriv (extendedLag θ n)=ᶠ[𝓝 0] extendedLagFirst θ n := by
    filter_upwards [hθ.eventually_analyticAt] with x hx
    exact (hasDerivAt_lag_phase hx.differentiableAt.hasDerivAt n).deriv
  have hv := hθ.deriv.differentiableAt.hasDerivAt
  have ht := hθ.differentiableAt.hasDerivAt
  have hline : HasDerivAt (fun x : ℝ=>(n:ℝ)*x-θ x) ((n:ℝ)-deriv θ 0) 0 := by
    convert ((hasDerivAt_id 0).const_mul (n:ℝ)).sub ht using 1 <;> first | rfl | ring
  have hh := (hv.neg.mul ht.sin).add (((hasDerivAt_const 0 (n:ℝ)).sub hv).mul hline.sin)
  have hh' : HasDerivAt (extendedLagFirst θ n) (-(n:ℝ)*((n:ℝ)-2*deriv θ 0)) 0 := by
    convert hh using 1
    · funext x
      simp only [extendedLagFirst,Pi.add_apply,Pi.mul_apply,Pi.sub_apply,Pi.neg_apply]
    · simp [h0]
      ring
  change deriv (deriv (extendedLag θ n)) 0=_
  rw [he.deriv_eq]
  exact hh'.deriv

def endLag (q : Tuning) (s : ℝ) (n : ℤ) : ℝ→ℝ := extendedLag (endAngle q s) n

@[simp] theorem endLag_zero (q : Tuning) (s : ℝ) (n : ℤ) : endLag q s n 0=0 := by
  simp [endLag,extendedLag]

theorem endLag_deriv_zero (q : Tuning) (s : ℝ) (n : ℤ) : deriv (endLag q s n) 0=0 :=
  analytic_lag_first_zero (analyticAt_endAngle q s (by
    simpa only [shiftNumerator,Real.cos_zero,Real.sin_zero,mul_zero,add_zero] using q.Xi_one_neg.ne))
    (endAngle_zero q s) n

/-- Literal second-derivative formula of Lemma ends, for every signed lag
and every real shift. -/
theorem endLag_second_zero (q : Tuning) (s : ℝ) (n : ℤ) :
    deriv^[2] (endLag q s n) 0= -(n:ℝ)*((n:ℝ)+2*tau q) := by
  rw [endLag,analytic_lag_second_zero (analyticAt_endAngle q s (by
    simpa only [shiftNumerator,Real.cos_zero,Real.sin_zero,mul_zero,add_zero] using q.Xi_one_neg.ne))
    (endAngle_zero q s) n,(hasDerivAt_endAngle_zero q s).deriv]
  ring

end polyak.Levels.Geometry
