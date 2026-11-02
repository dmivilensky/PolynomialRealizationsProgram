import jacobi.Young.Calibration

/-!
Article: jacobi, Section 3.2 (sharp Young inequality).
All alternative printed forms of the sharp constant and calibration value
are identified exactly, using nonnegative integer powers and rational
arithmetic. The actual infimum theorem is restated with the article's literal
sqrt-three formula, rather than leaving normalization conversion implicit.
Use: the verified inequality can be read in either normalization used in the article.
-/
namespace jacobi.Young
noncomputable section
open Real jacobi.Variational
set_option backward.isDefEq.respectTransparency false

/-- The two printed forms of the sharp Young constant agree exactly.
Use: the verified inequality can be read in either normalization used in the article.
Article: jacobi, Section 3.2 (sharp Young inequality).
Proof: both constants are nonnegative and their exact cubes equal five eighteenths. -/
theorem sharp_constant_identity : (5/18 : ℝ)^(1/3 : ℝ)=(32/45 : ℝ)*(15/16 : ℝ)^(4/3 : ℝ) := by
  -- Natural powers reduce every rational real-power constant to exact arithmetic.
  apply (pow_left_inj₀ (by positivity) (by positivity) (by decide : 3≠0)).mp
  have h1 : ((5/18 : ℝ)^(1/3 : ℝ))^3=5/18 := by
    simpa only [Nat.cast_one,pow_one] using third_power_cube (by norm_num : (0:ℝ)≤5/18) 1
  have h4 : ((15/16 : ℝ)^(4/3 : ℝ))^3=(15/16 : ℝ)^4 := by
    simpa only [Nat.cast_ofNat] using third_power_cube (by norm_num : (0:ℝ)≤15/16) 4
  rw [mul_pow,h1,h4]
  norm_num

/-- The canonical sharp calibration value equals the article's literal sqrt-three expression.
Use: identifies the proved actual variational minimum with precisely the printed formula ell_Y.
Article: jacobi, Section 3.2 (sharp Young inequality).
Proof: compare nonnegative fourth powers, use sqrt(3)^2=3 and the exact
identity youngValue(T)^4=(18/5)T^3. -/
theorem youngValue_printed {T : ℝ} (hT : 0≤T) :
    youngValue T=(2*sqrt 3/5)*(5*T/2)^(3/4 : ℝ) := by
  -- No approximate evaluation of the square root or fractional powers occurs.
  apply (pow_left_inj₀ (youngValue_nonneg hT) (by positivity) (by decide : 4≠0)).mp
  have hp : ((5*T/2)^(3/4 : ℝ))^4=(5*T/2)^3 := by
    rw [← Real.rpow_natCast,← Real.rpow_mul (by positivity : 0≤5*T/2)]
    norm_num
  rw [youngValue_four hT,mul_pow,hp,div_pow,mul_pow,
    show sqrt 3^4=(sqrt 3^2)^2 by ring,Real.sq_sqrt (by norm_num : (0:ℝ)≤3)]
  ring

/-- The complete Young-regime infimum has exactly the article's printed calibration value.
Use: the source-facing formula includes all mass and threshold conditions, with no normalization premise.
Article: jacobi, Section 3.2 (sharp Young inequality).
Proof: combine the proved attained infimum with the exact printed-value identity. -/
theorem second_calibration_young_printed {M T : ℝ} (hM : 0≤M) (hT : 0≤T) (hr : 5*T≤2*M^2) :
    relaxedInfimum {Observation.second} M (fun _ => T)=
      ENNReal.ofReal ((2*sqrt 3/5)*(5*T/2)^(3/4 : ℝ)) := by
  rw [second_calibration_young hM hT hr,youngValue_printed hT]

end
end jacobi.Young
