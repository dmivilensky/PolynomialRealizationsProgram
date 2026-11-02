import jacobi.GelfandLevitan.StripGauge

/-!
Article: jacobi, Appendix C.2 (transformed ODE and Green identity).
The actual first-order quasi-derivative system has an exact integrating
factor identity on every positive strip. It is derived from genuine
derivatives and the physical FTC. It will recover the unknown initial
quasi-derivative from the actual solution values at two physical points.
Use: the real positive integrating factors enter the original complex-energy quasi-derivative identities with their physical values unchanged.
-/
namespace jacobi.GelfandLevitan
noncomputable section
open Real Set Filter
open scoped Topology
set_option backward.isDefEq.respectTransparency false

/-- Complex inclusion of real physical-strip functions as a genuine bounded real-linear map.
Use: the real positive integrating factors enter the original complex-energy quasi-derivative identities with their physical values unchanged.
Article: jacobi, Appendix C.2 (transformed ODE and Green identity).
-/
def stripComplex {p q : ℝ} : C(ClosedStrip p q,ℝ) →L[ℝ] C(ClosedStrip p q,ℂ) :=
  ContinuousLinearMap.compLeftContinuous ℝ (ClosedStrip p q) Complex.ofRealCLM

/-- The original gauged inhomogeneous primitive for a physical-strip quasi-derivative system.
Use: quasiGauge_identity integrates the genuine quasi-derivative, and the solution endpoint difference then fixes its genuine integration constant.
Article: jacobi, Appendix C.2 (transformed ODE and Green identity).
-/
def quasiGaugePrimitive {p q : ℝ} (hpq : p≤q) (w : C(ClosedStrip p q,ℝ))
    (b f : C(ClosedStrip p q,ℂ)) : C(ClosedStrip p q,ℂ) :=
  stripPrimitive hpq (stripComplex (stripGauge hpq 2 w)*b*f)

/-- The actual positive-strip quasi-derivative satisfies its exact normalized integrating-factor primitive identity.
Use: quasiGauge_reconstruction obtains the true initial quasi-derivative from the original solution's endpoint values and hence proves its finite-to-infinite limit without assumptions on convergence of diagonal derivatives.
Article: jacobi, Appendix C.2 (transformed ODE and Green identity).
Source: the classical integrating-factor method.
Proof: multiply the actual quasi-derivative by the genuine positive integrating factor. Its independently proved derivative cancels the original drift term. The actual physical-strip FTC integrates this exact derivative, with integrating factor one at the true left endpoint. -/
theorem quasiGauge_identity {p q : ℝ} (hpq : p<q) (w : C(ClosedStrip p q,ℝ))
    (b f v : C(ClosedStrip p q,ℂ))
    (hv : ∀ t : ClosedStrip p q,HasDerivWithinAt (stripExtension hpq.le v)
      (b t*f t-2*(w t:ℂ)*v t) (Icc p q) (t:ℝ)) :
    stripComplex (stripGauge hpq.le 2 w)*v=
      ContinuousMap.const _ (v ⟨p,⟨le_rfl,hpq.le⟩⟩)+quasiGaugePrimitive hpq.le w b f := by
  -- The actual gauge derivative cancels the drift before integration; no derivative-limit premise is introduced.
  have hD (t : ClosedStrip p q) :
      HasDerivWithinAt (stripExtension hpq.le (stripComplex (stripGauge hpq.le 2 w)*v))
        ((stripComplex (stripGauge hpq.le 2 w)*b*f) t) (Icc p q) (t:ℝ) := by
    have hg := (stripGauge_hasDerivWithinAt hpq.le 2 w t).ofReal_comp
    have h := hg.mul (hv t)
    rw [stripExtension_value,stripExtension_value] at h
    change HasDerivWithinAt (stripExtension hpq.le (stripComplex (stripGauge hpq.le 2 w)*v)) _ _ _ at h
    convert h using 1
    change (stripGauge hpq.le 2 w t:ℂ)*b t*f t=_
    push_cast
    ring
  have he := stripPrimitive_eq_sub hpq (stripComplex (stripGauge hpq.le 2 w)*v)
    (stripComplex (stripGauge hpq.le 2 w)*b*f) hD
  have hleft : (stripComplex (stripGauge hpq.le 2 w)*v) ⟨p,⟨le_rfl,hpq.le⟩⟩=
      v ⟨p,⟨le_rfl,hpq.le⟩⟩ := by
    change (stripGauge hpq.le 2 w ⟨p,⟨le_rfl,hpq.le⟩⟩:ℂ)*_= _
    rw [stripGauge_left,Complex.ofReal_one,one_mul]
  rw [hleft] at he
  change quasiGaugePrimitive hpq.le w b f=_ at he
  rw [he]
  abel_nf

/-- The actual quasi-derivative is the negative integrating factor times its genuine initial value plus the proved original gauged primitive.
Use: quasiGauge_reconstruction expresses the same original quasi-derivative entirely in terms of original solution and diagonal values.
Article: jacobi, Appendix C.2 (transformed ODE and Green identity).
Proof: multiply the independently proved actual integrating-factor identity by the true reciprocal factor, whose product is exactly one at every original physical point. -/
theorem quasiGauge_value {p q : ℝ} (hpq : p<q) (w : C(ClosedStrip p q,ℝ))
    (b f v : C(ClosedStrip p q,ℂ))
    (hv : ∀ t : ClosedStrip p q,HasDerivWithinAt (stripExtension hpq.le v)
      (b t*f t-2*(w t:ℂ)*v t) (Icc p q) (t:ℝ)) (t : ClosedStrip p q) :
    v t=(stripGauge hpq.le (-2) w t:ℂ)*
      (v ⟨p,⟨le_rfl,hpq.le⟩⟩+quasiGaugePrimitive hpq.le w b f t) := by
  have he := congrArg (fun g : C(ClosedStrip p q,ℂ) => g t) (quasiGauge_identity hpq w b f v hv)
  change (stripGauge hpq.le 2 w t:ℂ)*v t=v ⟨p,⟨le_rfl,hpq.le⟩⟩+quasiGaugePrimitive hpq.le w b f t at he
  have hi : (stripGauge hpq.le (-2) w t:ℂ)*(stripGauge hpq.le 2 w t:ℂ)=1 := by
    rw [← Complex.ofReal_mul,mul_comm,stripGauge_reciprocal,Complex.ofReal_one]
  calc
    _ = ((stripGauge hpq.le (-2) w t:ℂ)*(stripGauge hpq.le 2 w t:ℂ))*v t := by rw [hi,one_mul]
    _ = _ := by rw [mul_assoc,he]

end
end jacobi.GelfandLevitan
