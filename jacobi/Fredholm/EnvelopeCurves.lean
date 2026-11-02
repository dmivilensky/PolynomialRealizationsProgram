import jacobi.Fredholm.FreeEnvelope
import jacobi.Fredholm.Continuity
import Mathlib.Analysis.Calculus.FDeriv.Partial

/-!
Article: jacobi, Appendix D.4 (envelope identities and global parameter uniqueness).
Continuous actual partial derivatives imply strict differentiability.
The genuine chain rule therefore restricts the verified one-form to
arbitrary differentiable parameter curves, including constant-mass curves.
Source: mathlib's theorem on continuous partial derivatives and its chain rule.
Use: differentiates the mass constraint along arbitrary physical parameter curves.
-/
namespace jacobi.Fredholm
noncomputable section
open Real Set MeasureTheory Filter jacobi.Elliptic
open scoped Topology
set_option backward.isDefEq.respectTransparency false

/-- The true two-component gradient of the printed normalized mass.
Use: differentiates the mass constraint along arbitrary physical parameter curves.
Article: jacobi, Appendix D.4 (envelope identities and global parameter uniqueness).
-/
def massGradient (t c : ℝ) : ℝ×ℝ :=
  ((3/2:ℝ)*c*shape2 t c,(3/2:ℝ)*(i2 t c-c*t/2*response2 t c))

/-- The true two-component gradient of the original energy quadrature.
Use: supplies the genuine energy derivative on the constant-mass curve.
Article: jacobi, Appendix D.4 (envelope identities and global parameter uniqueness).
-/
def energyGradient (t c : ℝ) : ℝ×ℝ :=
  ((3*c)^(3/2:ℝ)/sqrt t*(shape3 t c-i3 t c/(2*t)),
    (3*c)^(3/2:ℝ)/sqrt t*((3/(2*c))*i3 t c-(t/2)*response3 t c))

/-- The actual determinant gradient expressed by the proved integrated envelope cancellation.
Use: a continuous original derivative, not a hypothesized optimizer-family derivative.
Article: jacobi, Appendix D.4 (envelope identities and global parameter uniqueness).
-/
def determinantGradient (t c : ℝ) : ℝ×ℝ :=
  (envelopeCoefficient t c*(shape3 t c-i3 t c/(2*t))+(2*edge t c-1)*(massGradient t c).1,
    envelopeCoefficient t c*((3/(2*c))*i3 t c-(t/2)*response3 t c)+
      (2*edge t c-1)*(massGradient t c).2)

/-- All six literal state and response moments are jointly continuous at every interior physical point.
Use: proves continuity of the actual mass, energy and determinant gradients before invoking the chain rule.
Article: jacobi, Appendix D.4 (envelope identities and global parameter uniqueness).
Proof: restrict the proved joint dominated continuity on the closed
physical box to an actual neighborhood of the interior point. Specialize
the bounded numerator to one or to the spatial coordinate. -/
theorem moments_continuousAt {t c : ℝ} (ht : t∈Ioo (0:ℝ) 1) (hc : c∈Ioo (0:ℝ) 1) :
    ContinuousAt (fun p : ℝ×ℝ => i2 p.1 p.2) (t,c) ∧
    ContinuousAt (fun p : ℝ×ℝ => i3 p.1 p.2) (t,c) ∧
    ContinuousAt (fun p : ℝ×ℝ => shape2 p.1 p.2) (t,c) ∧
    ContinuousAt (fun p : ℝ×ℝ => shape3 p.1 p.2) (t,c) ∧
    ContinuousAt (fun p : ℝ×ℝ => response2 p.1 p.2) (t,c) ∧
    ContinuousAt (fun p : ℝ×ℝ => response3 p.1 p.2) (t,c) := by
  -- Interior physical points have a genuine neighborhood contained in the closed dominated box.
  have hp : (t,c)∈parameterBox := ⟨⟨ht.1.le,ht.2.le⟩,⟨hc.1.le,hc.2.le⟩⟩
  have hn : parameterBox∈𝓝 (t,c) := prod_mem_nhds (Icc_mem_nhds ht.1 ht.2) (Icc_mem_nhds hc.1 hc.2)
  have h1 (v : ℝ) (_ : v∈Ioo (0:ℝ) 1) : |(1:ℝ)|≤1 := by norm_num
  have hv (v : ℝ) (hv : v∈Ioo (0:ℝ) 1) : |v|≤1 := by rw [abs_of_pos hv.1]; exact hv.2.le
  refine ⟨?_,?_,?_,?_,?_,?_⟩
  · simpa only [i2,one_mul] using ((state_integral_continuous (fun _ => 1) measurable_const h1) (t,c) hp).continuousAt hn
  · exact ((state_integral_continuous (fun v => v) measurable_id hv) (t,c) hp).continuousAt hn
  · simpa only [shape2,one_mul] using ((shape_integral_continuous (fun _ => 1) measurable_const h1) (t,c) hp).continuousAt hn
  · exact ((shape_integral_continuous (fun v => v) measurable_id hv) (t,c) hp).continuousAt hn
  · simpa only [response2,one_mul] using ((response_integral_continuous (fun _ => 1) measurable_const h1) (t,c) hp).continuousAt hn
  · exact ((response_integral_continuous (fun v => v) measurable_id hv) (t,c) hp).continuousAt hn

/-- The three actual Fredholm gradients are jointly continuous throughout the interior physical domain.
Use: continuous partial derivatives justify the full curve envelope, beyond its two coordinate identities.
Article: jacobi, Appendix D.4 (envelope identities and global parameter uniqueness).
Proof: all six actual moments are jointly continuous. The remaining
factors are elementary continuous functions with positive tau, chi,
1-chi and sqrt(tau), so product and quotient rules preserve continuity. -/
theorem gradients_continuousAt {t c : ℝ} (ht : t∈Ioo (0:ℝ) 1) (hc : c∈Ioo (0:ℝ) 1) :
    ContinuousAt (fun p : ℝ×ℝ => massGradient p.1 p.2) (t,c) ∧
    ContinuousAt (fun p : ℝ×ℝ => energyGradient p.1 p.2) (t,c) ∧
    ContinuousAt (fun p : ℝ×ℝ => determinantGradient p.1 p.2) (t,c) := by
  -- None of these continuity statements assumes differentiability of a density family.
  obtain ⟨hI2,hI3,hS2,hS3,hR2,hR3⟩ := moments_continuousAt ht hc
  have ht0 := ht.1
  have hc0 := hc.1
  have hc1 := sub_pos.mpr hc.2
  constructor
  · unfold massGradient
    fun_prop
  constructor
  · unfold energyGradient
    fun_prop (disch := positivity)
  · unfold determinantGradient massGradient envelopeCoefficient edge
    fun_prop (disch := positivity)

/-- Continuous actual partial derivatives give the ordinary derivative along every differentiable physical curve.
Use: applies the complete chain rule to the actual Fredholm quadratures.
Article: jacobi, Appendix D.4 (envelope identities and global parameter uniqueness).
Proof: continuous scalar partials give strict Frechet differentiability
on the product domain. Compose its genuine derivative with the two
given curve derivatives and evaluate the resulting linear map. -/
theorem curve_hasDerivAt_of_partials (F : ℝ → ℝ → ℝ) (G : ℝ → ℝ → ℝ×ℝ)
    (hT : ∀ t∈Ioo (0:ℝ) 1,∀ c∈Ioo (0:ℝ) 1,
      HasDerivAt (fun u => F u c) (G t c).1 t)
    (hC : ∀ t∈Ioo (0:ℝ) 1,∀ c∈Ioo (0:ℝ) 1,
      HasDerivAt (F t) (G t c).2 c)
    {t c : ℝ → ℝ} {x a b : ℝ} (ht : HasDerivAt t a x) (hc : HasDerivAt c b x)
    (htp : t x∈Ioo (0:ℝ) 1) (hcp : c x∈Ioo (0:ℝ) 1)
    (hG : ContinuousAt (fun p : ℝ×ℝ => G p.1 p.2) (t x,c x)) :
    HasDerivAt (fun y => F (t y) (c y)) ((G (t x) (c x)).1*a+(G (t x) (c x)).2*b) x := by
  -- The partial derivatives hold on a full neighborhood, not just along the proposed curve.
  let S := ContinuousLinearMap.smulRightL ℝ ℝ ℝ (1 : ℝ →L[ℝ] ℝ)
  have hn : Ioo (0:ℝ) 1×ˢIoo (0:ℝ) 1∈𝓝 (t x,c x) :=
    prod_mem_nhds (isOpen_Ioo.mem_nhds htp) (isOpen_Ioo.mem_nhds hcp)
  have h := hasStrictFDerivAt_uncurry_coprod (f := F)
    (f₁ := fun u v => S (G u v).1) (f₂ := fun u v => S (G u v).2)
    (by filter_upwards [hn] with p hp; exact (hT p.1 hp.1 p.2 hp.2).hasFDerivAt)
    (by filter_upwards [hn] with p hp; exact (hC p.1 hp.1 p.2 hp.2).hasFDerivAt)
    (S.continuous.continuousAt.comp hG.fst) (S.continuous.continuousAt.comp hG.snd)
  have hh := h.hasFDerivAt.comp_hasDerivAt x (ht.prodMk hc)
  convert hh using 1
  · rfl
  · change (G (t x) (c x)).1*a+(G (t x) (c x)).2*b=
      a*(G (t x) (c x)).1+b*(G (t x) (c x)).2
    ring

/-- The complete Fredholm envelope holds along every differentiable interior parameter curve.
Use: applies the actual one-form to the constant-mass constraint, with no optimizer-family regularity assumption.
Article: jacobi, Appendix D.4 (envelope identities and global parameter uniqueness).
Proof: the three genuine gradients are continuous and their components
are the proved ordinary quadrature derivatives. Apply the full product
chain rule to each function; their exact two-component identity then
gives the stated derivative along the arbitrary curve. -/
theorem curve_envelope {t c : ℝ → ℝ} {x a b : ℝ}
    (ht : HasDerivAt t a x) (hc : HasDerivAt c b x)
    (htp : t x∈Ioo (0:ℝ) 1) (hcp : c x∈Ioo (0:ℝ) 1) :
    deriv (fun y => energy (t y) (c y)) x=(3/2:ℝ)*amplitude (t x) (c x)*
      (deriv (fun y => determinant (t y) (c y)) x-
        (2*edge (t x) (c x)-1)*deriv (fun y => mass (t y) (c y)) x) := by
  -- These are derivatives of the original functions restricted to the given curve.
  have hM := curve_hasDerivAt_of_partials mass massGradient
    (fun u hu v hv => (mass_shape_hasDerivAt_pos hu ⟨hv.1,hv.2.le⟩).1)
    (fun u hu v hv => mass_parameter_hasDerivAt ⟨hu.1.le,hu.2.le⟩ hv)
    ht hc htp hcp (gradients_continuousAt htp hcp).1
  have hE := curve_hasDerivAt_of_partials energy energyGradient
    (fun u hu v hv => energy_shape_hasDerivAt hu ⟨hv.1.le,hv.2.le⟩)
    (fun u hu v hv => energy_parameter_hasDerivAt ⟨hu.1,hu.2.le⟩ hv)
    ht hc htp hcp (gradients_continuousAt htp hcp).2.1
  have hD := curve_hasDerivAt_of_partials determinant determinantGradient
    (fun u hu v hv => determinant_shape_envelope hu hv)
    (fun u hu v hv => determinant_parameter_envelope hu hv)
    ht hc htp hcp (gradients_continuousAt htp hcp).2.2
  rw [hM.deriv,hE.deriv,hD.deriv]
  have hA := amplitude_envelope_coefficient htp.1 hcp
  dsimp only [massGradient,energyGradient,determinantGradient,Prod.fst,Prod.snd]
  linear_combination
    -(shape3 (t x) (c x)-i3 (t x) (c x)/(2*t x))*a*hA-
    ((3/(2*c x))*i3 (t x) (c x)-(t x/2)*response3 (t x) (c x))*b*hA

/-- The printed interior envelope identity holds on every differentiable constant-mass parameter curve.
Use: the literal identity in the source uniqueness proof, now with its analytic premises discharged.
Article: jacobi, Appendix D.4 (envelope identities and global parameter uniqueness).
Proof: the complete curve identity loses its mass term because the
actual restricted mass has derivative zero. -/
theorem constant_mass_envelope {t c : ℝ → ℝ} {x a b : ℝ}
    (ht : HasDerivAt t a x) (hc : HasDerivAt c b x)
    (htp : t x∈Ioo (0:ℝ) 1) (hcp : c x∈Ioo (0:ℝ) 1)
    (hm : HasDerivAt (fun y => mass (t y) (c y)) 0 x) :
    deriv (fun y => energy (t y) (c y)) x=(3/2:ℝ)*amplitude (t x) (c x)*
      deriv (fun y => determinant (t y) (c y)) x := by
  simpa only [hm.deriv,mul_zero,sub_zero] using curve_envelope ht hc htp hcp

end
end jacobi.Fredholm
