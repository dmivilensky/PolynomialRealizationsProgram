import jacobi.Hankel.CubicRemainder
import jacobi.Hankel.IncomingAmplitude

/-!
Article: jacobi, Lemma E.1.
Use: the Bessel connection and bounded complex-frequency propagation start from a proved common-domain asymptotic estimate, rather than index-dependent real-order bounds or an assumed complex Hankel expansion.
-/
namespace jacobi.Hankel
noncomputable section
open Set
set_option backward.isDefEq.respectTransparency false

/-- One genuine common far ray, holomorphic incoming/outgoing Jost family and cubic outgoing remainder work uniformly on a whole original complex-order disk.
Use: the Bessel connection and bounded complex-frequency propagation start from a proved common-domain asymptotic estimate, rather than index-dependent real-order bounds or an assumed complex Hankel expansion.
Article: jacobi, Lemma E.1.
Proof: choose the genuine common half-contraction cutoff from the original quadratic coefficient. Its norm is then at most R/2; the actual cubic residual coefficient is bounded by (R/2)*(R/2+2)*(R/2+6). The already proved true Jost remainder gives one uniform positive constant for every original order in the closed disk. -/
theorem uniform_besselAmplitude_cubic (a0 : ℂ) :
    ∃ R C : ℝ,∃ hR : 0<R,0<C ∧ ∀ a : ℂ,‖a-a0‖≤1 →
      AnalyticAt ℂ (besselAmplitude hR) a ∧ AnalyticAt ℂ (incomingAmplitude hR) a ∧
      ∀ x : ℝ,R≤x → ‖besselAmplitude hR a x-amplitudePolynomial (besselCoefficient a) x‖≤C/x^3 := by
  -- A single actual cutoff supplies both the common analytic domain and a genuine coefficient bound for all spatial indices.
  obtain ⟨R,hR,hhalf⟩ := common_order_ray a0
  let B : ℝ := R/2
  have hB : 0<B := half_pos hR
  refine ⟨R,B*(B+2)*(B+6)/12,hR,by positivity,fun a ha => ?_⟩
  have hh := hhalf a ha
  refine ⟨besselAmplitude_analytic hR (hh.trans_lt (by norm_num)),
    incomingAmplitude_analytic hR (hh.trans_lt (by norm_num)),fun x hx => ?_⟩
  have hxp : 0<x := hR.trans_le hx
  have hc : ‖besselCoefficient a‖≤B := by
    have h := (div_le_iff₀ hR).mp hh
    dsimp [B]
    linarith
  have h2 : ‖besselCoefficient a+2‖≤B+2 := calc
    _ ≤ ‖besselCoefficient a‖+‖(2:ℂ)‖ := norm_add_le _ _
    _ ≤ _ := by norm_num; exact hc
  have h6 : ‖besselCoefficient a+6‖≤B+6 := calc
    _ ≤ ‖besselCoefficient a‖+‖(6:ℂ)‖ := norm_add_le _ _
    _ ≤ _ := by norm_num; exact hc
  have hp : ‖besselCoefficient a*(besselCoefficient a+2)*(besselCoefficient a+6)‖≤B*(B+2)*(B+6) := by
    rw [norm_mul,norm_mul]
    gcongr
  apply (besselAmplitude_cubic hR hh hx).trans
  exact (div_le_div_of_nonneg_right hp (by positivity : 0≤12*x^3)).trans_eq (by ring)

end
end jacobi.Hankel
