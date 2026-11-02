import jacobi.Hankel.JostInverse
import jacobi.Hankel.RayBound
import Mathlib.Analysis.SpecialFunctions.Complex.Analytic

/-!
Article: jacobi, Lemma C.1.
Use: besselAmplitude substitutes this original coefficient into the solved outgoing integral equation.
-/
namespace jacobi.Hankel
noncomputable section
open Set Filter MeasureTheory
open scoped Topology BoundedContinuousFunction
set_option backward.isDefEq.respectTransparency false

/-- The actual complex inverse-square coefficient of the Bessel Liouville equation.
Use: besselAmplitude substitutes this original coefficient into the solved outgoing integral equation.
Article: jacobi, Lemma E.1.
-/
def besselCoefficient (a : ℂ) : ℂ := 1/4-a^2

/-- The genuine outgoing normalized Bessel amplitude on a fixed real ray.
Use: its analytic complex-order dependence and spatial remainder are used to construct the common high-index zero continuation of Lemma E.1.
Article: jacobi, Lemma E.1.
-/
def besselAmplitude {R : ℝ} (hR : 0<R) (a : ℂ) : OutgoingSpace :=
  outgoingAmplitude (inverseSquare_integrable hR) (besselCoefficient a)

/-- The actual Bessel outgoing amplitude is holomorphic in the original complex order wherever its genuine fixed-ray pencil is a contraction.
Use: all high-index complex-order arguments use this actual analytic family on one common neighborhood.
Article: jacobi, Lemma E.1.
Proof: compose the already proved analytic Banach inverse with the original quadratic Bessel coefficient, using the exact inverse-square L1 mass. -/
theorem besselAmplitude_analytic {R : ℝ} (hR : 0<R) {a : ℂ}
    (ha : ‖besselCoefficient a‖/R<1) : AnalyticAt ℂ (besselAmplitude hR) a := by
  have hc : ‖besselCoefficient a‖*(∫ y : ℝ,‖inverseSquare R y‖)<1 := by
    rwa [inverseSquare_norm_integral hR,← div_eq_mul_one_div]
  exact (outgoingAmplitude_analytic (inverseSquare_integrable hR) hc).comp
    (show AnalyticAt ℂ besselCoefficient a by unfold besselCoefficient; fun_prop)

/-- The same actual Bessel outgoing amplitude is bounded by two throughout a genuine common half-contraction domain.
Use: besselAmplitude_close_to_one obtains the spatial O(1/x) estimate uniformly in the actual complex order.
Article: jacobi, Lemma E.1.
Proof: use the actual solved-amplitude absorption estimate and the exact original inverse-square tail mass. -/
theorem besselAmplitude_norm_le_two {R : ℝ} (hR : 0<R) {a : ℂ}
    (ha : ‖besselCoefficient a‖/R≤1/2) : ‖besselAmplitude hR a‖≤2 := by
  apply outgoingAmplitude_norm_le_two
  rwa [inverseSquare_norm_integral hR,← div_eq_mul_one_div]

/-- The genuine outgoing Bessel amplitude differs from one by at most 2|c|/x on every original later ray.
Use: the actual Jost normalization at infinity and its ensuing Wronskian and Bessel comparison use a proved spatial remainder uniform on the original complex-order disk.
Article: jacobi, Lemma E.1.
Proof: evaluate the genuine inverse equation, bound its original Volterra integral by the future-ray mass 1/x and the proved norm bound two, and multiply by the actual complex coefficient. -/
theorem besselAmplitude_close_to_one {R : ℝ} (hR : 0<R) {a : ℂ}
    (ha : ‖besselCoefficient a‖/R≤1/2) {x : ℝ} (hx : R≤x) :
    ‖besselAmplitude hR a x-1‖≤2*‖besselCoefficient a‖/x := by
  -- The original inverse equation is evaluated before any spatial estimate is made.
  have hc : ‖besselCoefficient a‖*(∫ y : ℝ,‖inverseSquare R y‖)<1 := by
    rw [inverseSquare_norm_integral hR,← div_eq_mul_one_div]
    exact ha.trans_lt (by norm_num)
  have he := congrArg (fun f : OutgoingSpace => f x)
    (outgoingAmplitude_equation (inverseSquare_integrable hR) hc)
  change besselAmplitude hR a x=1-besselCoefficient a*
    outgoingIntegral (inverseSquare R) (besselAmplitude hR a) x at he
  have ht := outgoingIntegral_ray_bound hR hx (by norm_num : (0:ℝ)≤2)
    (besselAmplitude hR a) (fun y _ =>
      ((besselAmplitude hR a).norm_coe_le_norm y).trans (besselAmplitude_norm_le_two hR ha))
  rw [he,sub_sub_cancel_left,norm_neg,norm_mul]
  exact (mul_le_mul_of_nonneg_left ht (norm_nonneg _)).trans_eq (by ring)

/-- An explicit single cutoff controls the actual Bessel coefficient on the entire closed complex-order unit disk.
Use: common_order_ray supplies one fixed Banach space and one genuine contraction domain for all original complex orders in a neighborhood; there is no index-dependent choice of rays.
Article: jacobi, Lemma E.1.
Proof: |1/4-a^2| is at most 1/4+(|a0|+1)^2 on the genuine unit disk. A cutoff exceeding twice that bound makes every original outgoing pencil a half-contraction. -/
theorem common_order_ray (a0 : ℂ) :
    ∃ R : ℝ,0<R ∧ ∀ a : ℂ,‖a-a0‖≤1 → ‖besselCoefficient a‖/R≤1/2 := by
  -- This radius is chosen from the actual polynomial coefficient, independently of the spectral index.
  let B : ℝ := (‖a0‖+1)^2+1
  have hB : 0<B := by dsimp [B]; positivity
  refine ⟨2*B,by positivity,fun a ha => ?_⟩
  have hn : ‖a‖≤‖a0‖+1 := by
    calc
      ‖a‖ = ‖a-a0+a0‖ := by congr 1; ring
      _ ≤ ‖a-a0‖+‖a0‖ := norm_add_le _ _
      _ ≤ _ := by linarith
  have hc : ‖besselCoefficient a‖≤B := calc
    _ ≤ ‖(1/4:ℂ)‖+‖a^2‖ := norm_sub_le _ _
    _ ≤ B := by rw [norm_pow]; norm_num; dsimp [B]; nlinarith [norm_nonneg a,norm_nonneg a0]
  apply (div_le_iff₀ (by positivity : 0<2*B)).mpr
  nlinarith

end
end jacobi.Hankel
