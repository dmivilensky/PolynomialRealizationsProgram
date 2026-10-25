import chebyshev1.SineJacobi.EllipticDerivatives
import Mathlib.Analysis.SpecialFunctions.Trigonometric.InverseDeriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
Article: chebyshev1, Theorem 5.2.
The rational companion of K has an elementary exact integral.
Use: `chebyshev1.SineJacobi.ellipticRational_integral` feeds
`chebyshev1.SineJacobi.ellipticK_square_bound` (Cauchy--Schwarz and the elementary rational
integral give a uniform bound for K²).
Proof chain: `chebyshev1.SineJacobi.sineEnergy_le_four_div_pi` — chebyshev1, Theorem 5.2;
Exact sine gain, resolvent expression, asymptotics and energy value.
-/
namespace chebyshev1.SineJacobi
noncomputable section
open Real Set MeasureTheory

/--
Defines `ellipticRationalPrimitive` of type `ℝ` by `arccos (cos theta/sqrt (1-k^2*sin
theta^2))/sqrt (1-k^2)`.

Use: `chebyshev1.SineJacobi.ellipticRational_integral` uses this definition to establish
exact identity `(∫ theta in (0:ℝ)..(Real.pi/2), 1/(1-k^2*sin theta^2)) = Real.pi/(2*sqrt
(1-k^2))`.

Article: chebyshev1, Theorem 5.2 via `chebyshev1.SineJacobi.sineEnergy_le_four_div_pi`.
-/
def ellipticRationalPrimitive (k theta : ℝ) : ℝ :=
  arccos (cos theta/sqrt (1-k^2*sin theta^2))/sqrt (1-k^2)

/--
The actual derivative at the stated point: `HasDerivAt (fun u => cos u/sqrt (1-k^2*sin u^2))
(-(1-k^2)*sin theta/sqrt (1-k^2*sin theta^2)^3) theta`.

Use: `chebyshev1.SineJacobi.ellipticRationalPrimitive_deriv` uses this derivative formula
to establish the actual derivative at the stated point: `HasDerivAt (ellipticRationalPrimitive
k) (1/(1-k^2*sin theta^2)) theta`.

Article: chebyshev1, Theorem 5.2 via `chebyshev1.SineJacobi.sineEnergy_le_four_div_pi`.

Proof: Clear the denominators using the available nonzero hypotheses, then verify the remaining
algebraic identity.
-/
private theorem rationalInner_deriv {k theta : ℝ} (hk : |k| < 1) :
    HasDerivAt (fun u => cos u/sqrt (1-k^2*sin u^2))
      (-(1-k^2)*sin theta/sqrt (1-k^2*sin theta^2)^3) theta := by
  -- Clear the denominators using the available nonzero hypotheses, then verify the remaining
  -- algebraic identity.
  have hd := elliptic_den_pos k theta hk
  have hr := (sqrt_pos.mpr hd).ne'
  have hs := (((hasDerivAt_sin theta).pow 2).const_mul (k^2)).const_sub 1
  have h := (hasDerivAt_cos theta).div (hs.sqrt hd.ne') hr
  convert h using 1
  simp only [Pi.pow_apply]
  norm_num
  have hroot := sq_sqrt hd.le
  have htrig := sin_sq_add_cos_sq theta
  generalize sin theta = s at hroot htrig hr ⊢
  generalize cos theta = c at htrig ⊢
  generalize sqrt (1-k^2*s^2) = r at hroot hr ⊢
  field_simp [hr]
  rw [hroot]
  linear_combination -k^2*s*htrig

/--
The actual derivative at the stated point: `HasDerivAt (ellipticRationalPrimitive k)
(1/(1-k^2*sin theta^2)) theta`.

Use: `chebyshev1.SineJacobi.ellipticRational_integral` uses this derivative formula to
establish exact identity `(∫ theta in (0:ℝ)..(Real.pi/2), 1/(1-k^2*sin theta^2)) =
Real.pi/(2*sqrt (1-k^2))`.

Article: chebyshev1, Theorem 5.2 via `chebyshev1.SineJacobi.sineEnergy_le_four_div_pi`.

Proof: Clear the denominators using the available nonzero hypotheses, then verify the remaining
algebraic identity.
-/
theorem ellipticRationalPrimitive_deriv {k theta : ℝ} (hk : |k| < 1)
    (hth : theta ∈ Ioo (0:ℝ) (Real.pi/2)) :
    HasDerivAt (ellipticRationalPrimitive k)
      (1/(1-k^2*sin theta^2)) theta := by
  -- Clear the denominators using the available nonzero hypotheses, then verify the remaining
  -- algebraic identity.
  have hk2 : 0 < 1-k^2 := by have hh := abs_lt.mp hk; nlinarith
  have hq := sqrt_pos.mpr hk2
  have hd := elliptic_den_pos k theta hk
  have hr := sqrt_pos.mpr hd
  have hs := sin_pos_of_mem_Ioo
    (show theta ∈ Ioo (0:ℝ) Real.pi from ⟨hth.1, hth.2.trans (by linarith [pi_pos])⟩)
  have hc := cos_pos_of_mem_Ioo
    (show theta ∈ Ioo (-(Real.pi/2)) (Real.pi/2) by constructor <;> linarith [hth.1, hth.2, pi_pos])
  have hlt : cos theta < sqrt (1-k^2*sin theta^2) := by
    apply (lt_sqrt hc.le).mpr
    nlinarith [sin_sq_add_cos_sq theta, mul_pos hk2 (sq_pos_of_pos hs)]
  have harg : cos theta/sqrt (1-k^2*sin theta^2) ∈ Ioo (-1:ℝ) 1 := by
    constructor
    · have hh := div_pos hc hr; linarith
    · exact (div_lt_one hr).mpr hlt
  have he : sqrt (1-(cos theta/sqrt (1-k^2*sin theta^2))^2) =
      sqrt (1-k^2)*sin theta/sqrt (1-k^2*sin theta^2) := by
    apply (sq_eq_sq₀ (sqrt_nonneg _) (by positivity)).mp
    have hpos : 0 ≤ 1-(cos theta/sqrt (1-k^2*sin theta^2))^2 := by
      have hh := abs_lt.mpr harg
      have hi := abs_lt.mp hh
      nlinarith
    rw [sq_sqrt hpos]
    simp only [div_pow, mul_pow, sq_sqrt hk2.le, sq_sqrt hd.le]
    field_simp [hd.ne']
    nlinarith [sin_sq_add_cos_sq theta]
  have h := ((hasDerivAt_arccos (by linarith [harg.1]) (by linarith [harg.2])).comp theta
    (rationalInner_deriv hk)).div_const (sqrt (1-k^2))
  convert h using 1
  · rfl
  · rw [he]
    have hroot := sq_sqrt hd.le
    have hq2 := sq_sqrt hk2.le
    generalize sin theta = s at hroot hs hd hr ⊢
    generalize sqrt (1-k^2*s^2) = r at hroot hr ⊢
    generalize sqrt (1-k^2) = q at hq hq2 ⊢
    field_simp [hr.ne', hs.ne', hq.ne', hd.ne']
    rw [hroot, hq2]
    ring

/--
The rational companion of K has an elementary exact integral.

Exact identity `(∫ theta in (0:ℝ)..(Real.pi/2), 1/(1-k^2*sin theta^2)) = Real.pi/(2*sqrt
(1-k^2))`.

Use: `chebyshev1.SineJacobi.ellipticK_square_bound` rewrites with this identity to
establish the stated quantitative bound `ellipticK k^2 ≤ Real.pi^2/(4*sqrt (1-k^2))`.

Article: chebyshev1, Theorem 5.2 via `chebyshev1.SineJacobi.sineEnergy_le_four_div_pi`.

Proof: Use the identities/estimates `chebyshev1.SineJacobi.elliptic_den_pos`,
`chebyshev1.SineJacobi.ellipticRationalPrimitive_deriv` with the arguments shown in the
proof.
-/
theorem ellipticRational_integral {k : ℝ} (hk : |k| < 1) :
    (∫ theta in (0:ℝ)..(Real.pi/2), 1/(1-k^2*sin theta^2)) =
      Real.pi/(2*sqrt (1-k^2)) := by
  -- Establish continuity hc before using the function at limits or in calculus arguments.
  have hc : Continuous (ellipticRationalPrimitive k) := by
    unfold ellipticRationalPrimitive
    apply Continuous.div_const
    apply Real.continuous_arccos.comp
    apply Continuous.div (by fun_prop) (by fun_prop)
    exact fun theta => (sqrt_pos.mpr (elliptic_den_pos k theta hk)).ne'
  -- Establish continuity hi before using the function at limits or in calculus arguments.
  have hi : Continuous (fun theta => 1/(1-k^2*sin theta^2)) := by
    apply Continuous.div continuous_const (by fun_prop)
    exact fun theta => (elliptic_den_pos k theta hk).ne'
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le (half_pos pi_pos).le
    hc.continuousOn (fun theta ht => ellipticRationalPrimitive_deriv hk ht)
    (hi.intervalIntegrable (μ := volume) 0 (Real.pi/2))
  simpa [ellipticRationalPrimitive, div_div] using h

end
end chebyshev1.SineJacobi
