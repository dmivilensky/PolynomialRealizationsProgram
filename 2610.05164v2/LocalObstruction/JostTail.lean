import «2610.05164v2».LocalObstruction.SineConvolutionTail
import «2610.05164v2».LocalObstruction.GreenIdentities

/-!
Article: 2610.05164v2, Theorem 6.1.
The actual sine Jost solution: exponential leading terms and o(n) remainders, obtained from the
Volterra equation and the certified sine tail.
Use: `«2610.05164v2».LocalObstruction.sineJost_reflected_tail` feeds
`«2610.05164v2».LocalObstruction.sine_green_scale_tail` (sine green scale tail).
Proof chain: `«2610.05164v2».LocalObstruction.sine_green_scale_tail` — 2610.05164v2, Theorem 6.1; No
locally sharp C1 bound from finitely many spectral observations.
-/
namespace «2610.05164v2».LocalObstruction
noncomputable section
open Set Real Filter MeasureTheory Asymptotics «2610.05164v2».SineContinuum «2610.05164v2».Filters
open scoped Topology
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

variable {s : ℝ} (hs : 0≤s)

/--
Defines `sineJostBound` of type `ℝ` by `exp (s/2)`.

Use: `«2610.05164v2».LocalObstruction.sineJost_reflected_bound` uses this definition to
establish the stated quantitative bound `|jost s m (-x)-1|≤(s/2*sineJostBound s)*(∫ y in Ioi x,
m y)`.

Article: 2610.05164v2, Theorem 6.1 via `«2610.05164v2».LocalObstruction.sine_green_scale_tail`.
-/
def sineJostBound (s : ℝ) : ℝ := exp (s/2)
/--
Defines `sineJostCoefficient` of type `ℝ` by `-s/2*∫ y, exp (2*y)*(m y*jost s m y)`.

Use: `«2610.05164v2».LocalObstruction.sineJost_remainder_formula` uses this definition to
establish the precise assertion is `jost s m x-transmission s m-sineJostCoefficient s*exp
(-2*x)= s/2*(exp (-2*x)*(∫ y in Ioi x, exp (2*y)*(m y*jost s m y))- (∫ y in Ioi x, m y*jost s m
y))`.

Article: 2610.05164v2, Theorem 6.1 via `«2610.05164v2».LocalObstruction.theorem_6_1`.
-/
def sineJostCoefficient (s : ℝ) : ℝ := -s/2*∫ y, exp (2*y)*(m y*jost s m y)

include hs in
/--
Membership in the specified domain/enclosure: `jost s m x ∈ Icc (1:ℝ) (sineJostBound s)`.

Use: `«2610.05164v2».LocalObstruction.sineJost_reflected_bound` rewrites with this assertion to
establish the stated quantitative bound `|jost s m (-x)-1|≤(s/2*sineJostBound s)*(∫ y in Ioi x,
m y)`.

Article: 2610.05164v2, Theorem 6.1 via `«2610.05164v2».LocalObstruction.sine_green_scale_tail`.

Proof: Use the identities/estimates `«2610.05164v2».Filters.jost_bounds`,
`«2610.05164v2».SineContinuum.m_integrable`, `«2610.05164v2».SineContinuum.m_positive` with the
arguments shown in the proof.
-/
theorem sineJost_bound (x : ℝ) : jost s m x ∈ Icc (1:ℝ) (sineJostBound s) := by
  have h := jost_bounds m_integrable (fun x => (m_positive x).le) hs x
  refine ⟨h.1,h.2.trans ?_⟩
  apply exp_le_exp.mpr
  have hb := (cumulative_bounds m_integrable (fun x => (m_positive x).le) x).2
  rw [mass] at hb
  nlinarith

include hs in
/--
Integrability of the displayed function: `Integrable (fun y => exp (2*y)*(m y*jost s m y))`.

Use: `«2610.05164v2».LocalObstruction.sineJost_remainder_bound` uses this integrability result
to prove the bound `|jost s m x-transmission s m-sineJostCoefficient
s*exp (-2*x)|≤ (s/2*sineJostBound s)*sineTailJ x`.

Article: 2610.05164v2, Theorem 6.1 via `«2610.05164v2».LocalObstruction.theorem_6_1`.

Proof: Use the identities/estimates
`«2610.05164v2».LocalObstruction.sine_weighted_moment_integrable`,
`«2610.05164v2».SineContinuum.m_continuous`, `«2610.05164v2».Filters.jost_continuous` with the
arguments shown in the proof.
-/
theorem sineJost_weighted_integrable : Integrable (fun y => exp (2*y)*(m y*jost s m y)) := by
  -- Use the identities/estimates
  -- `«2610.05164v2».LocalObstruction.sine_weighted_moment_integrable`,
  -- `«2610.05164v2».SineContinuum.m_continuous`, `«2610.05164v2».Filters.jost_continuous` with
  -- the arguments shown in the proof.
  apply (sine_weighted_moment_integrable.mul_const (sineJostBound s)).mono'
    ((continuous_exp.comp (by fun_prop)).mul (m_continuous.mul
      (jost_continuous m_integrable (fun x => (m_positive x).le) hs))).aestronglyMeasurable
  apply Eventually.of_forall
  intro y
  dsimp only [Pi.mul_apply,Function.comp_apply]
  rw [norm_of_nonneg (mul_nonneg (exp_pos _).le
    (mul_nonneg (m_positive y).le (by linarith [(sineJost_bound hs y).1])))]
  nlinarith [mul_le_mul_of_nonneg_left (sineJost_bound hs y).2
    (mul_nonneg (exp_pos (2*y)).le (m_positive y).le)]

include hs in
/--
The precise assertion is `jost s m x-transmission s m-sineJostCoefficient s*exp (-2*x)=
s/2*(exp (-2*x)*(∫ y in Ioi x, exp (2*y)*(m y*jost s m y))- (∫ y in Ioi x, m y*jost s m y))`.

Use: `«2610.05164v2».LocalObstruction.sineJost_remainder_bound` rewrites with this identity to
establish the stated quantitative bound `|jost s m x-transmission s m-sineJostCoefficient s*exp
(-2*x)|≤ (s/2*sineJostBound s)*sineTailJ x`.

Article: 2610.05164v2, Theorem 6.1 via `«2610.05164v2».LocalObstruction.theorem_6_1`.

Proof: Use the identities/estimates `«2610.05164v2».Filters.jost_forcing_integrable`,
`«2610.05164v2».SineContinuum.m_integrable`, `«2610.05164v2».SineContinuum.m_positive` with the
arguments shown in the proof.
-/
theorem sineJost_remainder_formula (x : ℝ) :
    jost s m x-transmission s m-sineJostCoefficient s*exp (-2*x)=
      s/2*(exp (-2*x)*(∫ y in Ioi x, exp (2*y)*(m y*jost s m y))-
        (∫ y in Ioi x, m y*jost s m y)) := by
  -- Use the identities/estimates `«2610.05164v2».Filters.jost_forcing_integrable`,
  -- `«2610.05164v2».SineContinuum.m_integrable`, `«2610.05164v2».SineContinuum.m_positive`
  -- with the arguments shown in the proof.
  have hF := jost_forcing_integrable m_integrable (fun x => (m_positive x).le) hs
  have hW := sineJost_weighted_integrable hs
  have h₁ := intervalIntegral.integral_Iic_add_Ioi hF.integrableOn hF.integrableOn (b := x)
  have h₂ := intervalIntegral.integral_Iic_add_Ioi hW.integrableOn hW.integrableOn (b := x)
  have he := jost_equation m_integrable (fun x => (m_positive x).le) hs x
  unfold volterra cumulative causal at he
  unfold transmission sineJostCoefficient
  linear_combination he+s/2*h₁-s/2*exp (-2*x)*h₂

include hs in
/--
The stated quantitative bound `|jost s m x-transmission s m-sineJostCoefficient s*exp (-2*x)|≤
(s/2*sineJostBound s)*sineTailJ x`.

Use: `«2610.05164v2».LocalObstruction.sineJost_tail` uses this bound to establish the stated
quantitative bound `(fun x => jost s m x-transmission s m-sineJostCoefficient s*exp (-2*x))
=o[atTop] n`.

Article: 2610.05164v2, Theorem 6.1 via `«2610.05164v2».LocalObstruction.theorem_6_1`.

Proof: Use the identities/estimates `«2610.05164v2».Filters.jost_forcing_integrable`,
`«2610.05164v2».SineContinuum.m_integrable`, `«2610.05164v2».SineContinuum.m_positive` with the
arguments shown in the proof.
-/
theorem sineJost_remainder_bound (x : ℝ) :
    |jost s m x-transmission s m-sineJostCoefficient s*exp (-2*x)|≤
      (s/2*sineJostBound s)*sineTailJ x := by
  -- Use the identities/estimates `«2610.05164v2».Filters.jost_forcing_integrable`,
  -- `«2610.05164v2».SineContinuum.m_integrable`, `«2610.05164v2».SineContinuum.m_positive`
  -- with the arguments shown in the proof.
  have hF := jost_forcing_integrable m_integrable (fun x => (m_positive x).le) hs
  have hW := sineJost_weighted_integrable hs
  have hnn (y : ℝ) : 0≤m y*jost s m y :=
    mul_nonneg (m_positive y).le (by linarith [(sineJost_bound hs y).1])
  have h₁ : (∫ y in Ioi x, m y*jost s m y)≤sineJostBound s*(∫ y in Ioi x, m y) := by
    rw [← integral_const_mul]
    apply integral_mono_ae hF.integrableOn (m_integrable.integrableOn.const_mul _)
    exact Eventually.of_forall (fun y => by
      simpa only [mul_comm] using mul_le_mul_of_nonneg_left (sineJost_bound hs y).2 (m_positive y).le)
  have h₂ : exp (-2*x)*(∫ y in Ioi x, exp (2*y)*(m y*jost s m y))≤
      sineJostBound s*weightedSineTail x := by
    rw [weightedSineTail_original_formula]
    have hi : (∫ y in Ioi x, exp (2*y)*(m y*jost s m y))≤
        sineJostBound s*(∫ y in Ioi x, exp (2*y)*m y) := by
      rw [← integral_const_mul]
      apply integral_mono_ae hW.integrableOn (sine_weighted_moment_integrable.integrableOn.const_mul _)
      exact Eventually.of_forall (fun y => by
        nlinarith [mul_le_mul_of_nonneg_left (sineJost_bound hs y).2
          (mul_nonneg (exp_pos (2*y)).le (m_positive y).le)])
    nlinarith [mul_le_mul_of_nonneg_left hi (exp_pos (-2*x)).le]
  rw [sineJost_remainder_formula hs x,abs_mul,abs_of_nonneg (div_nonneg hs (by norm_num))]
  have hB : |exp (-2*x)*(∫ y in Ioi x, exp (2*y)*(m y*jost s m y))-
      (∫ y in Ioi x, m y*jost s m y)|≤sineJostBound s*sineTailJ x := by
    calc
      _ ≤ |exp (-2*x)*(∫ y in Ioi x, exp (2*y)*(m y*jost s m y))|+
          |∫ y in Ioi x, m y*jost s m y| := abs_sub _ _
      _ = exp (-2*x)*(∫ y in Ioi x, exp (2*y)*(m y*jost s m y))+
          (∫ y in Ioi x, m y*jost s m y) := by
        rw [abs_of_nonneg (mul_nonneg (exp_pos _).le
          (integral_nonneg (fun y => mul_nonneg (exp_pos _).le (hnn y)))),
          abs_of_nonneg (integral_nonneg hnn)]
      _ ≤ _ := by unfold sineTailJ; nlinarith [h₁,h₂]
  have h := mul_le_mul_of_nonneg_left hB (show (0:ℝ)≤s/2 from div_nonneg hs (by norm_num))
  nlinarith [h]

include hs in
/--
The stated quantitative bound `(fun x => jost s m x-transmission s m-sineJostCoefficient s*exp
(-2*x)) =o[atTop] n`.

Use: `«2610.05164v2».LocalObstruction.sine_green_diagonal_tail` uses this identity to establish
the stated quantitative bound `(fun x => greenKernel s m x x-1/2- (sineJostCoefficient
s/(2*transmission s m))*exp (-2*x)) =o[atTop] n`.

Article: 2610.05164v2, Theorem 6.1 via `«2610.05164v2».LocalObstruction.theorem_6_1`.

Proof: Intersect the eventual or almost-everywhere hypotheses, then prove the asserted relation
at an arbitrary point in that intersection. Clear the denominators using the available nonzero
hypotheses, then verify the remaining algebraic identity.
-/
theorem sineJost_tail :
    (fun x => jost s m x-transmission s m-sineJostCoefficient s*exp (-2*x)) =o[atTop] n := by
  -- Intersect the eventual or almost-everywhere hypotheses, then prove the asserted relation
  -- at an arbitrary point in that intersection.
  let K := s/2*sineJostBound s
  have hK : 0≤K := mul_nonneg (div_nonneg hs (by norm_num)) (exp_pos _).le
  apply IsLittleO.of_bound
  intro c hc
  filter_upwards [sineTailJ_littleO.bound (div_pos hc (by linarith : 0<K+1)),
    eventually_ge_atTop (1:ℝ)] with x ht hx
  rw [Real.norm_eq_abs,abs_of_nonneg (sineTailJ_bounds hx).1] at ht
  rw [Real.norm_eq_abs]
  calc
    _ ≤ K*sineTailJ x := sineJost_remainder_bound hs x
    _ ≤ (K+1)*sineTailJ x := mul_le_mul_of_nonneg_right (by linarith) (sineTailJ_bounds hx).1
    _ ≤ (K+1)*(c/(K+1)*‖n x‖) := mul_le_mul_of_nonneg_left ht (by linarith)
    _ = _ := by field_simp

include hs in
/--
The stated quantitative bound `|jost s m (-x)-1|≤(s/2*sineJostBound s)*(∫ y in Ioi x, m y)`.

Use: `«2610.05164v2».LocalObstruction.sineJost_reflected_tail` uses this bound to establish the
stated quantitative bound `(fun x => jost s m (-x)-1) =o[atTop] n`.

Article: 2610.05164v2, Theorem 6.1 via `«2610.05164v2».LocalObstruction.sine_green_scale_tail`.

Proof: Use the identities/estimates `«2610.05164v2».Filters.jost_forcing_integrable`,
`«2610.05164v2».SineContinuum.m_integrable`, `«2610.05164v2».SineContinuum.m_positive` with the
arguments shown in the proof.
-/
theorem sineJost_reflected_bound (x : ℝ) :
    |jost s m (-x)-1|≤(s/2*sineJostBound s)*(∫ y in Ioi x, m y) := by
  -- Use the identities/estimates `«2610.05164v2».Filters.jost_forcing_integrable`,
  -- `«2610.05164v2».SineContinuum.m_integrable`, `«2610.05164v2».SineContinuum.m_positive`
  -- with the arguments shown in the proof.
  have hF := jost_forcing_integrable m_integrable (fun x => (m_positive x).le) hs
  have hV := (volterra_bounds hs hF (fun y =>
    mul_nonneg (m_positive y).le (by linarith [(sineJost_bound hs y).1])) (-x)).2
  have hj := jost_equation m_integrable (fun x => (m_positive x).le) hs (-x)
  have he : cumulative m (-x)=(∫ y in Ioi x, m y) := by
    unfold cumulative
    conv_lhs => arg 2; ext y; rw [← m_even y]
    rw [integral_comp_neg_Iic,neg_neg]
  have hi : cumulative (fun y => m y*jost s m y) (-x)≤
      sineJostBound s*cumulative m (-x) := by
    unfold cumulative
    rw [← integral_const_mul]
    apply integral_mono_ae hF.integrableOn (m_integrable.integrableOn.const_mul _)
    exact Eventually.of_forall (fun y => by
      simpa only [mul_comm] using mul_le_mul_of_nonneg_left (sineJost_bound hs y).2 (m_positive y).le)
  rw [abs_of_nonneg (by linarith [(sineJost_bound hs (-x)).1])]
  rw [he] at hi
  nlinarith [mul_le_mul_of_nonneg_left hi (show (0:ℝ)≤s/2 from div_nonneg hs (by norm_num))]

include hs in
/--
The stated quantitative bound `(fun x => jost s m (-x)-1) =o[atTop] n`.

Use: `«2610.05164v2».LocalObstruction.sine_green_diagonal_tail` uses this identity to establish
the stated quantitative bound `(fun x => greenKernel s m x x-1/2- (sineJostCoefficient
s/(2*transmission s m))*exp (-2*x)) =o[atTop] n`.

Article: 2610.05164v2, Theorem 6.1 via `«2610.05164v2».LocalObstruction.sine_green_scale_tail`.

Proof: Intersect the eventual or almost-everywhere hypotheses, then prove the asserted relation
at an arbitrary point in that intersection. Clear the denominators using the available nonzero
hypotheses, then verify the remaining algebraic identity.
-/
theorem sineJost_reflected_tail : (fun x => jost s m (-x)-1) =o[atTop] n := by
  -- Intersect the eventual or almost-everywhere hypotheses, then prove the asserted relation
  -- at an arbitrary point in that intersection.
  let K := s/2*sineJostBound s
  have hK : 0≤K := mul_nonneg (div_nonneg hs (by norm_num)) (exp_pos _).le
  apply IsLittleO.of_bound
  intro c hc
  filter_upwards [sineTailJ_littleO.bound (div_pos hc (by linarith : 0<K+1)),
    eventually_ge_atTop (1:ℝ)] with x ht hx
  rw [Real.norm_eq_abs,abs_of_nonneg (sineTailJ_bounds hx).1] at ht
  rw [Real.norm_eq_abs]
  have htail : (∫ y in Ioi x, m y)≤sineTailJ x := by
    unfold sineTailJ
    exact le_add_of_nonneg_right (weightedSineTail_bounds hx).1
  calc
    _ ≤ K*(∫ y in Ioi x, m y) := sineJost_reflected_bound hs x
    _ ≤ K*sineTailJ x := mul_le_mul_of_nonneg_left htail hK
    _ ≤ (K+1)*sineTailJ x := mul_le_mul_of_nonneg_right (by linarith) (sineTailJ_bounds hx).1
    _ ≤ (K+1)*(c/(K+1)*‖n x‖) := mul_le_mul_of_nonneg_left ht (by linarith)
    _ = _ := by field_simp

end
end «2610.05164v2».LocalObstruction
