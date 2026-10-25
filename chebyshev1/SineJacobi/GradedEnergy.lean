import chebyshev1.SineJacobi.EnergyDerivativeBounds

/-!
Article: chebyshev1, Theorem 5.2.
The cubic grading has a uniform fourth-derivative bound away from zero.
Use: `chebyshev1.SineJacobi.gradedEnergy_fourth_bound` feeds
`chebyshev1.SineJacobi.sineEnergy_quadrature_error` (sine Energy quadrature error).
Proof chain: `chebyshev1.SineJacobi.sineEnergy_decimal` — chebyshev1, Theorem 5.2; Exact sine
gain, resolvent expression, asymptotics and energy value.
-/
namespace chebyshev1.SineJacobi
noncomputable section
open Real Set chebyshev1.Analysis
set_option backward.isDefEq.respectTransparency false

/--
Cubic grading regularizes the endpoint for certified quadrature.

Use: `chebyshev1.SineJacobi.gradedEnergy_contDiffOn` uses this definition to establish
smoothness to the stated order: `ContDiffOn ℝ n gradedEnergy (Ioo (0:ℝ) 1.1)`.

Article: chebyshev1, Theorem 5.2 via `chebyshev1.SineJacobi.sineEnergy_decimal`.
-/
def gradedEnergy (s : ℝ) : ℝ := 3*s^2*energyDensity (s^3/2)

/--
Defines `gradedDerivative` by pattern matching with result type `ℕ → ℝ → ℝ`. The displayed
branches determine the recursive cases and their returned values.

Use:
`_private.chebyshev1.SineJacobi.GradedEnergy.0.chebyshev1.SineJacobi.gradedDerivative_deriv`
rewrites with this definition to establish the actual derivative at the stated point:
`HasDerivAt (gradedDerivative j) (gradedDerivative (j+1) s) s`.

Article: chebyshev1, Theorem 5.2 via `chebyshev1.SineJacobi.sineEnergy_decimal`.
-/
private def gradedDerivative : ℕ → ℝ → ℝ
  | 0 => fun s => gradedEnergy s
  | 1 => fun s => 6*s*energyDensity (s^3/2)+(9/2)*s^4*iteratedDeriv 1 energyDensity (s^3/2)
  | 2 => fun s => 6*energyDensity (s^3/2)+27*s^3*iteratedDeriv 1 energyDensity (s^3/2)+
      (27/4)*s^6*iteratedDeriv 2 energyDensity (s^3/2)
  | 3 => fun s => 90*s^2*iteratedDeriv 1 energyDensity (s^3/2)+
      81*s^5*iteratedDeriv 2 energyDensity (s^3/2)+
      (81/8)*s^8*iteratedDeriv 3 energyDensity (s^3/2)
  | _ => fun s => 180*s*iteratedDeriv 1 energyDensity (s^3/2)+
      540*s^4*iteratedDeriv 2 energyDensity (s^3/2)+
      (405/2)*s^7*iteratedDeriv 3 energyDensity (s^3/2)+
      (243/16)*s^10*iteratedDeriv 4 energyDensity (s^3/2)

/--
The actual derivative at the stated point: `HasDerivAt (gradedDerivative j) (gradedDerivative
(j+1) s) s`.

Use: `chebyshev1.SineJacobi.gradedEnergy_fourth_derivative` uses this derivative formula to
establish the identity stated in that declaration.

Article: chebyshev1, Theorem 5.2 via `chebyshev1.SineJacobi.sineEnergy_decimal`.

Proof: Use the identities/estimates `chebyshev1.Analysis.hasDerivAt_iteratedDeriv`,
`chebyshev1.SineJacobi.energyDensity_contDiffOn` with the arguments shown in the proof.
-/
private theorem gradedDerivative_deriv {j : ℕ} (hj : j < 4) {s : ℝ}
    (hs : s ∈ Ioo (0:ℝ) 1.1) (ht : s^3/2 < 1) :
    HasDerivAt (gradedDerivative j) (gradedDerivative (j+1) s) s := by
  -- Apply
  -- `_private.chebyshev1.SineJacobi.GradedEnergy.0.chebyshev1.SineJacobi.gradedDerivative`,
  -- `chebyshev1.SineJacobi.energyDensity`,
  -- `chebyshev1.Analysis.hasDerivAt_iteratedDeriv` to the displayed hypotheses, then match
  -- the resulting expression to the goal.
  have hs0 := hs.1
  have hp : s^3/2 ∈ Ioo (0:ℝ) 1 := ⟨by positivity, ht⟩
  have hd (i : ℕ) : HasDerivAt (fun x => iteratedDeriv i energyDensity (x^3/2))
      (iteratedDeriv (i+1) energyDensity (s^3/2)*(3*s^2/2)) s := by
    have hu := hasDerivAt_iteratedDeriv
      ((energyDensity_contDiffOn (i+1)).contDiffAt (isOpen_Ioo.mem_nhds hp))
    convert hu.comp s (((hasDerivAt_id s).pow 3).div_const 2) using 1 <;> first | rfl | (dsimp [Function.comp_def]; ring)
  have hi := hasDerivAt_id s
  have h0 : HasDerivAt (fun x => energyDensity (x^3/2))
      (iteratedDeriv 1 energyDensity (s^3/2)*(3*s^2/2)) s := by simpa using hd 0
  interval_cases j
  · convert ((hi.pow 2).const_mul 3).mul h0 using 1 <;> first | rfl | (simp [gradedDerivative]; ring)
  · convert (((hi.const_mul 6).mul h0).add (((hi.pow 4).const_mul (9/2)).mul (hd 1))) using 1 <;>
      first | rfl | (simp [gradedDerivative]; ring)
  · convert ((h0.const_mul 6).add (((hi.pow 3).const_mul 27).mul (hd 1))).add
      (((hi.pow 6).const_mul (27/4)).mul (hd 2)) using 1 <;>
      first | rfl | (simp [gradedDerivative]; ring)
  · convert ((((hi.pow 2).const_mul 90).mul (hd 1)).add
      (((hi.pow 5).const_mul 81).mul (hd 2))).add
      (((hi.pow 8).const_mul (81/8)).mul (hd 3)) using 1 <;>
      first | rfl | (simp [gradedDerivative]; ring)

/--
Smoothness to the stated order: `ContDiffOn ℝ n gradedEnergy (Ioo (0:ℝ) 1.1)`.

Use:
`_private.chebyshev1.SineJacobi.EnergyQuadrature.0.chebyshev1.SineJacobi.gradedEnergy_integrable`
uses this assertion to establish `IntervalIntegrable gradedEnergy
volume 0 1`.

Article: chebyshev1, Theorem 5.2 via `chebyshev1.SineJacobi.sineEnergy_decimal`.

Proof: Use the identities/estimates `chebyshev1.SineJacobi.energyDensity_contDiffOn` with
the arguments shown in the proof.
-/
theorem gradedEnergy_contDiffOn (n : ℕ) : ContDiffOn ℝ n gradedEnergy (Ioo (0:ℝ) 1.1) := by
  -- Use the identities/estimates `chebyshev1.SineJacobi.energyDensity_contDiffOn` with the
  -- arguments shown in the proof.
  unfold gradedEnergy
  apply ContDiffOn.mul (by fun_prop)
  apply (energyDensity_contDiffOn n).comp (by fun_prop)
  intro x hx
  have hx0 := hx.1
  refine ⟨by positivity, ?_⟩
  have hh := pow_lt_pow_left₀ hx.2 hx.1.le (by norm_num : (3:ℕ) ≠ 0)
  norm_num at hh
  linarith

/--
Exact identity `iteratedDeriv 4 gradedEnergy s = 180*s*iteratedDeriv 1 energyDensity (s^3/2)+
540*s^4*iteratedDeriv 2 energyDensity (s^3/2)+ (405/2)*s^7*iteratedDeriv 3 energyDensity
(s^3/2)+ (243/16)*s^10*iteratedDeriv 4 energyDensity (s^3/2)`.

Use: `chebyshev1.SineJacobi.gradedEnergy_fourth_bound` rewrites with this identity to
establish the stated quantitative bound `|iteratedDeriv 4 gradedEnergy s| ≤ 1300000`.

Article: chebyshev1, Theorem 5.2 via `chebyshev1.SineJacobi.sineEnergy_decimal`.

Proof: Use the identities/estimates `chebyshev1.Analysis.iteratedDeriv_eq_of_derivatives`,
`_private.chebyshev1.SineJacobi.GradedEnergy.0.chebyshev1.SineJacobi.gradedDerivative_deriv`
with the arguments shown in the proof.
-/
theorem gradedEnergy_fourth_derivative {s : ℝ} (hs : 0 < s) (hs1 : s ≤ 1) :
    iteratedDeriv 4 gradedEnergy s =
      180*s*iteratedDeriv 1 energyDensity (s^3/2)+
      540*s^4*iteratedDeriv 2 energyDensity (s^3/2)+
      (405/2)*s^7*iteratedDeriv 3 energyDensity (s^3/2)+
      (243/16)*s^10*iteratedDeriv 4 energyDensity (s^3/2) := by
  -- Use the identities/estimates `chebyshev1.Analysis.iteratedDeriv_eq_of_derivatives`,
  -- `_private.chebyshev1.SineJacobi.GradedEnergy.0.chebyshev1.SineJacobi.gradedDerivative_deriv`
  -- with the arguments shown in the proof.
  have ht : s^3/2 < 1 := by nlinarith [pow_le_pow_left₀ hs.le hs1 3]
  exact iteratedDeriv_eq_of_derivatives (F := gradedDerivative) (m := 4) isOpen_Ioo
    (fun j hj x hx => gradedDerivative_deriv hj hx (by
      have hh := pow_lt_pow_left₀ hx.2 hx.1.le (by norm_num : (3:ℕ) ≠ 0)
      norm_num at hh
      linarith)) 4 le_rfl ⟨hs, by linarith⟩

/--
The cubic grading has a uniform fourth-derivative bound away from zero.

The stated quantitative bound `|iteratedDeriv 4 gradedEnergy s| ≤ 1300000`.

Use: `chebyshev1.SineJacobi.sineEnergy_quadrature_error` uses this bound to establish the
stated quantitative bound `|sineEnergy-energyQuadrature N| ≤ 1300000/(3*(N:ℝ)^4)+12/(N:ℝ)^6`.

Article: chebyshev1, Theorem 5.2 via `chebyshev1.SineJacobi.sineEnergy_decimal`.

Proof: Use the identities/estimates
`chebyshev1.SineJacobi.energyDensity_weighted_derivatives`,
`chebyshev1.SineJacobi.sineDensity_square_bound`,
`chebyshev1.SineJacobi.gradedEnergy_fourth_derivative` with the arguments shown in the
proof.
-/
theorem gradedEnergy_fourth_bound {s : ℝ} (hs : 0 < s) (hs1 : s ≤ 1) :
    |iteratedDeriv 4 gradedEnergy s| ≤ 1300000 := by
  -- Use the identities/estimates
  -- `chebyshev1.SineJacobi.energyDensity_weighted_derivatives`,
  -- `chebyshev1.SineJacobi.sineDensity_square_bound`,
  -- `chebyshev1.SineJacobi.gradedEnergy_fourth_derivative` with the arguments shown in the
  -- proof.
  have hs3 := pow_le_pow_left₀ hs.le hs1 3
  have ht : 0 < s^3/2 := by positivity
  have ht1 : s^3/2 ≤ 1/2 := by nlinarith [hs3]
  have hw := energyDensity_weighted_derivatives ht ht1
  have h1 := hw 1 (by norm_num)
  have h2 := hw 2 (by norm_num)
  have h3 := hw 3 (by norm_num)
  have h4 := hw 4 le_rfl
  simp only [energyDerivativeBound] at h1 h2 h3 h4
  have hu : energyDensity (s^3/2) ≤ 4*s^3 := by
    have hb := sineDensity_square_bound (show s^3/2 ∈ Ioo (0:ℝ) 1 by
      exact ⟨ht, by linarith⟩)
    have hsin := sin_le (show 0 ≤ Real.pi*(s^3/2) by positivity)
    have hpi := mul_le_mul_of_nonneg_right pi_lt_four.le ht.le
    change sineDensity (s^3/2)^2 ≤ _
    nlinarith [hb, hsin, hpi]
  have hab : |iteratedDeriv 4 gradedEnergy s| ≤
      180*s*|iteratedDeriv 1 energyDensity (s^3/2)|+
      540*s^4*|iteratedDeriv 2 energyDensity (s^3/2)|+
      (405/2)*s^7*|iteratedDeriv 3 energyDensity (s^3/2)|+
      (243/16)*s^10*|iteratedDeriv 4 energyDensity (s^3/2)| := by
    rw [gradedEnergy_fourth_derivative hs hs1]
    let a := 180*s*iteratedDeriv 1 energyDensity (s^3/2)
    let b := 540*s^4*iteratedDeriv 2 energyDensity (s^3/2)
    let c := (405/2)*s^7*iteratedDeriv 3 energyDensity (s^3/2)
    let d := (243/16)*s^10*iteratedDeriv 4 energyDensity (s^3/2)
    have hh : |a+b+c+d| ≤ |a|+|b|+|c|+|d| :=
      (abs_add_le _ _).trans (add_le_add
        ((abs_add_le _ _).trans (add_le_add (abs_add_le _ _) le_rfl)) le_rfl)
    simpa only [a, b, c, d, abs_mul, abs_pow, abs_of_pos hs,
      show |(180:ℝ)| = 180 by norm_num, show |(540:ℝ)| = 540 by norm_num,
      show |(405/2:ℝ)| = 405/2 by norm_num, show |(243/16:ℝ)| = 243/16 by norm_num] using hh
  have hh : |iteratedDeriv 4 gradedEnergy s| * s^2 ≤ 313344*energyDensity (s^3/2) := by
    have hab' := mul_le_mul_of_nonneg_right hab (sq_nonneg s)
    nlinarith only [hab', h1, h2, h3, h4]
  have hs32 : s^3 ≤ s^2 := by nlinarith [mul_le_mul_of_nonneg_left hs1 (sq_nonneg s)]
  have hbound : |iteratedDeriv 4 gradedEnergy s| * s^2 ≤ 1300000*s^2 := by
    nlinarith [hh, hu, hs32, sq_nonneg s]
  exact (mul_le_mul_iff_left₀ (sq_pos_of_pos hs)).mp hbound

end
end chebyshev1.SineJacobi
