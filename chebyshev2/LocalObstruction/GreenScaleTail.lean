import chebyshev2.LocalObstruction.GreenResolvent
import chebyshev2.LocalObstruction.JostTail

/-!
Article: chebyshev2, Theorem 6.1.
The sine Green scale derivative has an exponential leading term and an o(n) remainder.
Use: `chebyshev2.LocalObstruction.sine_green_scale_tail` feeds
`chebyshev2.LocalObstruction.theorem_6_1` (theorem 6 1).
-/
namespace chebyshev2.LocalObstruction
noncomputable section
open Set Real Filter MeasureTheory Asymptotics chebyshev2.SineContinuum chebyshev2.Filters
open scoped Topology
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

 /--
The precise assertion is `f =o[atTop] n`.

Use: `chebyshev2.LocalObstruction.sine_green_scale_tail` uses this identity to establish
the stated quantitative bound `(fun x => greenScaleGradient s m x-sineGreenScaleCoefficient
s*exp (-2*x)) =o[atTop] n`.

Article: chebyshev2, Theorem 6.1 via `chebyshev2.LocalObstruction.sine_green_scale_tail`.

Proof: Intersect the eventual or almost-everywhere hypotheses, then prove the asserted relation
at an arbitrary point in that intersection.
-/
theorem sineTail_domination {f : ℝ → ℝ} (K : ℝ)
    (hb : ∀ x,1≤x → |f x|≤K*sineTailJ x) : f =o[atTop] n := by
  apply IsBigO.trans_isLittleO (g := sineTailJ) _ sineTailJ_littleO
  apply IsBigO.of_bound K
  filter_upwards [eventually_ge_atTop (1:ℝ)] with x hx
  simpa only [Real.norm_eq_abs,abs_of_nonneg (sineTailJ_bounds hx).1] using hb x hx

 /--
Integrability of the displayed function: `Integrable (fun y => exp (2*y)*m y*(jost s m y)^2)`.

Use: `chebyshev2.LocalObstruction.sineJost_scaled_left_tail_bound` uses this integrability
result to establish membership in the specified domain/enclosure: `exp (-2*x)*(∫ y in Ioi x,exp
(2*y)*m y*(jost s m y)^2)∈ Icc (0:ℝ) ((sineJostBound s)^2*weightedSineTail x)`.

Article: chebyshev2, Theorem 6.1 via `chebyshev2.LocalObstruction.sine_green_scale_tail`.

Proof: Use the identities/estimates
`chebyshev2.LocalObstruction.sine_weighted_moment_integrable`,
`chebyshev2.Filters.jost_continuous`, `chebyshev2.SineContinuum.m_integrable` with the
arguments shown in the proof.
-/
theorem sineJost_square_weighted_integrable {s : ℝ} (hs : 0≤s) :
    Integrable (fun y => exp (2*y)*m y*(jost s m y)^2) := by
  apply sine_weighted_moment_integrable.mul_bdd (c := (sineJostBound s)^2)
  · exact ((jost_continuous m_integrable (fun y => (m_positive y).le) hs).pow 2).aestronglyMeasurable
  · exact Eventually.of_forall (fun y => by
      rw [norm_of_nonneg (sq_nonneg _)]
      exact pow_le_pow_left₀ (by linarith [(sineJost_bound hs y).1]) (sineJost_bound hs y).2 2)

 /--
Integrability of the displayed function: `Integrable (fun y => exp (-2*y)*m y*(jost s m
(-y))^2)`.

Use: `chebyshev2.LocalObstruction.sineJost_scaled_right_tail_bound` uses this integrability
result to establish membership in the specified domain/enclosure: `exp (2*x)*(∫ y in Ioi x,exp
(-2*y)*m y*(jost s m (-y))^2)∈ Icc (0:ℝ) ((sineJostBound s)^2*(∫ y in Ioi x,m y))`.

Article: chebyshev2, Theorem 6.1 via `chebyshev2.LocalObstruction.sine_green_scale_tail`.

Proof: Use the identities/estimates `chebyshev2.SineContinuum.m_even`,
`chebyshev2.LocalObstruction.sineJost_square_weighted_integrable` with the arguments shown
in the proof.
-/
theorem sineJost_square_right_integrable {s : ℝ} (hs : 0≤s) :
    Integrable (fun y => exp (-2*y)*m y*(jost s m (-y))^2) := by
  simpa only [Function.comp_def,mul_neg,neg_mul,m_even] using
    (sineJost_square_weighted_integrable hs).comp_neg

 /--
Defines `sineGreenScaleCoefficient` of type `ℝ` by `-(∫ y,exp (2*y)*m y*(jost s m
y)^2)/(wronskian s m 0)^2`.

Use: `chebyshev2.LocalObstruction.sine_green_scale_tail` uses this definition to establish
the stated quantitative bound `(fun x => greenScaleGradient s m x-sineGreenScaleCoefficient
s*exp (-2*x)) =o[atTop] n`.

Article: chebyshev2, Theorem 6.1 via `chebyshev2.LocalObstruction.sine_green_scale_tail`.
-/
def sineGreenScaleCoefficient (s : ℝ) : ℝ :=
  -(∫ y,exp (2*y)*m y*(jost s m y)^2)/(wronskian s m 0)^2

 /--
The precise assertion is `greenScaleGradient s m x= -((exp (-2*x)*(jost s m (-x))^2)* (∫ y in
Iic x,exp (2*y)*m y*(jost s m y)^2)+ (exp (2*x)*(jost s m x)^2)* (∫ y in Ioi x,exp (-2*y)*m
y*(jost s m (-y))^2))/(wronskian s m 0)^2`.

Use: `chebyshev2.LocalObstruction.sine_green_scale_tail` rewrites with this identity to
establish the stated quantitative bound `(fun x => greenScaleGradient s m
x-sineGreenScaleCoefficient s*exp (-2*x)) =o[atTop] n`.

Article: chebyshev2, Theorem 6.1 via `chebyshev2.LocalObstruction.sine_green_scale_tail`.

Proof: Use the identities/estimates `chebyshev2.SineContinuum.m_integrable`,
`chebyshev2.LocalObstruction.greenKernel_continuous`,
`chebyshev2.SineContinuum.m_positive` with the arguments shown in the proof.
-/
theorem sineGreenScale_formula {s : ℝ} (hs : 0≤s) (x : ℝ) :
    greenScaleGradient s m x= -((exp (-2*x)*(jost s m (-x))^2)*
        (∫ y in Iic x,exp (2*y)*m y*(jost s m y)^2)+
      (exp (2*x)*(jost s m x)^2)*
        (∫ y in Ioi x,exp (-2*y)*m y*(jost s m (-y))^2))/(wronskian s m 0)^2 := by
  -- Establish hi as the integrability justification for the later integral estimates or
  -- changes of order.
  have hi' : Integrable (fun y => m y*(greenKernel s m x y)^2) := by
    apply m_integrable.mul_bdd (c := (1/2:ℝ)^2)
      (((greenKernel_continuous m_integrable (fun y => (m_positive y).le) hs).comp
        (continuous_const.prodMk continuous_id)).pow 2).aestronglyMeasurable
    exact Eventually.of_forall (fun y => by
      change ‖(greenKernel s m x y)^2‖≤(1/2:ℝ)^2
      rw [norm_of_nonneg (sq_nonneg _)]
      have h := resolventGreen_abs_bound m_integrable (fun y => (m_positive y).le) hs x y
      rw [← greenKernel_eq_resolventGreen m_integrable (fun y => (m_positive y).le) m_continuous hs m_even x y] at h
      simpa only [sq_abs] using pow_le_pow_left₀ (abs_nonneg (greenKernel s m x y)) h 2)
  -- Establish hi as the integrability justification for the later integral estimates or
  -- changes of order.
  have hi : Integrable (fun y => (greenKernel s m x y)^2*m y) :=
    hi'.congr (Eventually.of_forall (fun y => mul_comm _ _))
  have hsplit := intervalIntegral.integral_Iic_add_Ioi hi.integrableOn hi.integrableOn (b := x)
  have hleft : (∫ y in Iic x,(greenKernel s m x y)^2*m y)=
      (exp (-2*x)*(jost s m (-x))^2)/(wronskian s m 0)^2*
        (∫ y in Iic x,exp (2*y)*m y*(jost s m y)^2) := by
    rw [← integral_const_mul]
    apply setIntegral_congr_fun measurableSet_Iic
    intro y hy
    dsimp only
    unfold greenKernel jostFunction
    rw [min_eq_right hy,max_eq_left hy]
    have hex (z : ℝ) : exp (2*z)=(exp z)^2 := by rw [pow_two,← exp_add];congr 1;ring
    rw [hex y,show exp (-2*x)=(exp (-x))^2 by convert! hex (-x) using 1; congr 1; ring]
    ring
  have hright : (∫ y in Ioi x,(greenKernel s m x y)^2*m y)=
      (exp (2*x)*(jost s m x)^2)/(wronskian s m 0)^2*
        (∫ y in Ioi x,exp (-2*y)*m y*(jost s m (-y))^2) := by
    rw [← integral_const_mul]
    apply setIntegral_congr_fun measurableSet_Ioi
    intro y hy
    dsimp only
    unfold greenKernel jostFunction
    rw [min_eq_left hy.le,max_eq_right hy.le]
    have hex (z : ℝ) : exp (2*z)=(exp z)^2 := by rw [pow_two,← exp_add];congr 1;ring
    rw [hex x,show exp (-2*y)=(exp (-y))^2 by convert! hex (-y) using 1; congr 1; ring]
    ring
  unfold greenScaleGradient
  rw [← hsplit,hleft,hright]
  ring

 /--
Membership in the specified domain/enclosure: `exp (-2*x)*(∫ y in Ioi x,exp (2*y)*m y*(jost s m
y)^2)∈ Icc (0:ℝ) ((sineJostBound s)^2*weightedSineTail x)`.

Use: `chebyshev2.LocalObstruction.sine_green_scale_tail` rewrites with this assertion to
establish the stated quantitative bound `(fun x => greenScaleGradient s m
x-sineGreenScaleCoefficient s*exp (-2*x)) =o[atTop] n`.

Article: chebyshev2, Theorem 6.1 via `chebyshev2.LocalObstruction.sine_green_scale_tail`.

Proof: Use the identities/estimates `chebyshev2.SineContinuum.m_positive`,
`chebyshev2.LocalObstruction.weightedSineTail_original_formula`,
`chebyshev2.LocalObstruction.sineJost_square_weighted_integrable` with the arguments shown
in the proof.
-/
theorem sineJost_scaled_left_tail_bound {s : ℝ} (hs : 0≤s) (x : ℝ) :
    exp (-2*x)*(∫ y in Ioi x,exp (2*y)*m y*(jost s m y)^2)∈
      Icc (0:ℝ) ((sineJostBound s)^2*weightedSineTail x) := by
  -- Use the identities/estimates `chebyshev2.SineContinuum.m_positive`,
  -- `chebyshev2.LocalObstruction.weightedSineTail_original_formula`,
  -- `chebyshev2.LocalObstruction.sineJost_square_weighted_integrable` with the arguments
  -- shown in the proof.
  constructor
  · exact mul_nonneg (exp_pos _).le (integral_nonneg (fun y => mul_nonneg (mul_nonneg (exp_pos _).le (m_positive y).le) (sq_nonneg _)))
  · rw [weightedSineTail_original_formula]
    have hi : (∫ y in Ioi x,exp (2*y)*m y*(jost s m y)^2)≤
        (sineJostBound s)^2*(∫ y in Ioi x,exp (2*y)*m y) := by
      rw [← integral_const_mul]
      apply integral_mono_ae (sineJost_square_weighted_integrable hs).integrableOn
        (sine_weighted_moment_integrable.integrableOn.const_mul _)
      exact Eventually.of_forall (fun y => by
        have hp := pow_le_pow_left₀ (by linarith [(sineJost_bound hs y).1]) (sineJost_bound hs y).2 2
        nlinarith [mul_le_mul_of_nonneg_left hp (mul_nonneg (exp_pos (2*y)).le (m_positive y).le)])
    nlinarith [mul_le_mul_of_nonneg_left hi (exp_pos (-2*x)).le]

 /--
Membership in the specified domain/enclosure: `exp (2*x)*(∫ y in Ioi x,exp (-2*y)*m y*(jost s m
(-y))^2)∈ Icc (0:ℝ) ((sineJostBound s)^2*(∫ y in Ioi x,m y))`.

Use: `chebyshev2.LocalObstruction.sine_green_scale_tail` rewrites with this assertion to
establish the stated quantitative bound `(fun x => greenScaleGradient s m
x-sineGreenScaleCoefficient s*exp (-2*x)) =o[atTop] n`.

Article: chebyshev2, Theorem 6.1 via `chebyshev2.LocalObstruction.sine_green_scale_tail`.

Proof: Intersect the eventual or almost-everywhere hypotheses, then prove the asserted relation
at an arbitrary point in that intersection.
-/
theorem sineJost_scaled_right_tail_bound {s : ℝ} (hs : 0≤s) (x : ℝ) :
    exp (2*x)*(∫ y in Ioi x,exp (-2*y)*m y*(jost s m (-y))^2)∈
      Icc (0:ℝ) ((sineJostBound s)^2*(∫ y in Ioi x,m y)) := by
  -- Intersect the eventual or almost-everywhere hypotheses, then prove the asserted relation
  -- at an arbitrary point in that intersection.
  constructor
  · exact mul_nonneg (exp_pos _).le (integral_nonneg (fun y => mul_nonneg (mul_nonneg (exp_pos _).le (m_positive y).le) (sq_nonneg _)))
  · rw [← integral_const_mul,← integral_const_mul]
    apply integral_mono_ae
      ((sineJost_square_right_integrable hs).integrableOn.const_mul _)
      (m_integrable.integrableOn.const_mul _)
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with y hy
    have hp := pow_le_pow_left₀ (by linarith [(sineJost_bound hs (-y)).1]) (sineJost_bound hs (-y)).2 2
    have hex : exp (2*x)*exp (-2*y)≤1 := by
      rw [← exp_add]
      apply exp_le_one_iff.mpr
      have hxy : x<y := hy
      linarith
    calc
      _ = (exp (2*x)*exp (-2*y))*((jost s m (-y))^2*m y) := by ring
      _ ≤ (jost s m (-y))^2*m y :=
        mul_le_of_le_one_left (mul_nonneg (sq_nonneg _) (m_positive y).le) hex
      _ ≤ _ := by nlinarith [mul_le_mul_of_nonneg_right hp (m_positive y).le]

 /--
The stated quantitative bound `(fun x => greenScaleGradient s m x-sineGreenScaleCoefficient
s*exp (-2*x)) =o[atTop] n`.

Use: `chebyshev2.LocalObstruction.greenScaleTailGradient` uses this identity in the
displayed construction of `greenScaleTailGradient`. Its inputs and component formulas are fixed
by that definition.

Article: chebyshev2, Theorem 6.1.

Proof: Prove equality of functions by evaluating both sides at an arbitrary argument.
-/
theorem sine_green_scale_tail {s : ℝ} (hs : 0≤s) :
    (fun x => greenScaleGradient s m x-sineGreenScaleCoefficient s*exp (-2*x)) =o[atTop] n := by
  -- Prove equality of functions by evaluating both sides at an arbitrary argument.
  let F := fun y => exp (2*y)*m y*(jost s m y)^2
  let C := ∫ y,F y
  let L := fun x => exp (-2*x)*(∫ y in Ioi x,F y)
  let R := fun x => exp (2*x)*(∫ y in Ioi x,exp (-2*y)*m y*(jost s m (-y))^2)
  have hL : L =o[atTop] n := sineTail_domination ((sineJostBound s)^2) (fun x _ => by
    rw [abs_of_nonneg (sineJost_scaled_left_tail_bound hs x).1]
    exact (sineJost_scaled_left_tail_bound hs x).2.trans
      (mul_le_mul_of_nonneg_left (by unfold sineTailJ;exact le_add_of_nonneg_left (integral_nonneg (fun y => (m_positive y).le))) (sq_nonneg _)))
  have hR : R =o[atTop] n := sineTail_domination ((sineJostBound s)^2) (fun x hx => by
    rw [abs_of_nonneg (sineJost_scaled_right_tail_bound hs x).1]
    exact (sineJost_scaled_right_tail_bound hs x).2.trans
      (mul_le_mul_of_nonneg_left (by unfold sineTailJ;exact le_add_of_nonneg_right (weightedSineTail_bounds hx).1) (sq_nonneg _)))
  -- Record the convergence hneg with its source filter and target limit before taking limits
  -- in the subsequent identities/bounds.
  have hneg : Tendsto (fun x => jost s m (-x)) atTop (𝓝 1) :=
    (jost_left_limit m_integrable (fun x => (m_positive x).le) hs).comp tendsto_neg_atTop_atBot
  have hpos := jost_right_limit m_integrable (fun x => (m_positive x).le) hs
  have hsquare : (fun x => (jost s m (-x))^2-1) =o[atTop] n := by
    have h := (sineJost_reflected_tail hs).mul_isBigO
      ((hneg.add_const 1).isBigO_one ℝ)
    simp only [mul_one] at h
    convert! h using 1
    funext x
    ring
  -- Record the convergence hex with its source filter and target limit before taking limits in
  -- the subsequent identities/bounds.
  have hex : Tendsto (fun x : ℝ => exp (-2*x)) atTop (𝓝 0) :=
    tendsto_exp_atBot.comp (Tendsto.const_mul_atTop_of_neg (by norm_num : (-2:ℝ)<0) tendsto_id)
  have hmain := hsquare.mul_isBigO ((hex.const_mul C).isBigO_one ℝ)
  have hleft := hL.mul_isBigO ((hneg.pow 2).isBigO_one ℝ)
  have hright := hR.mul_isBigO ((hpos.pow 2).isBigO_one ℝ)
  simp only [mul_one] at hmain hleft hright
  have hsum := ((hmain.sub hleft).add hright).const_mul_left (-(1/(wronskian s m 0)^2):ℝ)
  convert! hsum using 1
  funext x
  rw [sineGreenScale_formula hs x]
  have hi := intervalIntegral.integral_Iic_add_Ioi
    (sineJost_square_weighted_integrable hs).integrableOn
    (sineJost_square_weighted_integrable hs).integrableOn (b := x)
  change (∫ y in Iic x,F y)+(∫ y in Ioi x,F y)=C at hi
  unfold sineGreenScaleCoefficient
  change _= -(1/(wronskian s m 0)^2)*
    (((jost s m (-x))^2-1)*(C*exp (-2*x))-L x*(jost s m (-x))^2+R x*(jost s m x)^2)
  dsimp only [L,R]
  rw [show (∫ y in Iic x,F y)=C-(∫ y in Ioi x,F y) by linarith [hi]]
  dsimp only [C,F]
  ring

end
end chebyshev2.LocalObstruction
