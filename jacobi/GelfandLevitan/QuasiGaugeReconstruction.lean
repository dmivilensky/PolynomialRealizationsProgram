import jacobi.GelfandLevitan.QuasiGaugeIdentity

/-!
Article: jacobi, Appendix C.2 (transformed ODE and Green identity).
The actual quasi-derivative is determined by the original diagonal,
inhomogeneous coefficient and solution values on a fixed positive
strip. The denominator is an integral of a strictly positive real
factor. This exact reconstruction removes any need to assume finite
initial-slope convergence in the infinite GL limit.
Use: the genuine initial quasi-derivative is separated from the endpoint integral in quasiGauge_initial.
-/
namespace jacobi.GelfandLevitan
noncomputable section
open Real Set Filter MeasureTheory
open scoped Topology
set_option backward.isDefEq.respectTransparency false

/-- Complex constants factor out of the actual physical-strip primitive.
Use: the genuine initial quasi-derivative is separated from the endpoint integral in quasiGauge_initial.
Article: jacobi, Appendix C.2 (transformed ODE and Green identity).
Source: complex linearity of the Bochner integral.
Proof: evaluate the actual primitives and apply the community interval-integral constant multiplication identity. -/
theorem stripPrimitive_const_mul {p q : ℝ} (hpq : p≤q) (c : ℂ) (f : C(ClosedStrip p q,ℂ)) :
    stripPrimitive hpq (ContinuousMap.const _ c*f)=ContinuousMap.const _ c*stripPrimitive hpq f := by
  ext t
  exact intervalIntegral.integral_const_mul c _

/-- The strictly positive real denominator determining the physical-strip initial quasi-derivative.
Use: quasiGauge_initial solves the actual original endpoint identity with a genuinely nonzero denominator.
Article: jacobi, Appendix C.2 (transformed ODE and Green identity).
-/
def quasiGaugeDenominator {p q : ℝ} (hpq : p≤q) (w : C(ClosedStrip p q,ℝ)) : ℝ :=
  stripPrimitive hpq (stripGauge hpq (-2) w*stripGauge hpq (-2) w) ⟨q,⟨hpq,le_rfl⟩⟩

/-- The initial quasi-derivative denominator is genuinely strictly positive on every nondegenerate physical strip.
Use: the exact reconstructed initial value and its continuous dependence require no extra nondegeneracy premise.
Article: jacobi, Appendix C.2 (transformed ODE and Green identity).
Source: positivity of the integral of a strictly positive continuous function.
Proof: the actual integrand is the square of a real exponential and hence positive everywhere. Its original physical interval has strictly positive length. -/
theorem quasiGaugeDenominator_pos {p q : ℝ} (hpq : p<q) (w : C(ClosedStrip p q,ℝ)) :
    0<quasiGaugeDenominator hpq.le w := by
  change 0<∫ r in p..q,stripExtension hpq.le (stripGauge hpq.le (-2) w*stripGauge hpq.le (-2) w) r
  apply intervalIntegral.intervalIntegral_pos_of_pos
    ((stripExtension hpq.le (stripGauge hpq.le (-2) w*stripGauge hpq.le (-2) w)).continuous.intervalIntegrable p q)
    _ hpq
  intro r
  change 0<Real.exp _*Real.exp _
  positivity

/-- The genuine twice integrated inhomogeneous term in the physical endpoint identity.
Use: quasiGaugeInitial subtracts this actual term before solving for the original initial quasi-derivative.
Article: jacobi, Appendix C.2 (transformed ODE and Green identity).
-/
def quasiGaugeRemainder {p q : ℝ} (hpq : p≤q) (w : C(ClosedStrip p q,ℝ))
    (b f : C(ClosedStrip p q,ℂ)) : C(ClosedStrip p q,ℂ) :=
  stripPrimitive hpq ((stripComplex (stripGauge hpq (-2) w)*stripComplex (stripGauge hpq (-2) w))*
    quasiGaugePrimitive hpq w b f)

/-- The initial quasi-derivative recovered from the actual physical-strip solution endpoints and diagonal.
Use: quasiGauge_initial proves that this expression equals the genuine initial quasi-derivative, and its norm-continuous ingredients permit the finite-to-infinite limit.
Article: jacobi, Appendix C.2 (transformed ODE and Green identity).
-/
def quasiGaugeInitial {p q : ℝ} (hpq : p≤q) (w : C(ClosedStrip p q,ℝ))
    (b f : C(ClosedStrip p q,ℂ)) : ℂ :=
  (f ⟨q,⟨hpq,le_rfl⟩⟩*(stripGauge hpq (-2) w ⟨q,⟨hpq,le_rfl⟩⟩:ℂ)-
    f ⟨p,⟨le_rfl,hpq⟩⟩-quasiGaugeRemainder hpq w b f ⟨q,⟨hpq,le_rfl⟩⟩)/
      (quasiGaugeDenominator hpq w:ℂ)

/-- The actual quasi-derivative's left endpoint value is exactly its reconstruction from the original solution and diagonal data.
Use: quasiGauge_reconstruction and its true uniform-norm limit eliminate every unproved initial-slope convergence premise.
Article: jacobi, Appendix C.2 (transformed ODE and Green identity).
Source: the integrating-factor solution of a first-order linear system with two prescribed first-component values.
Proof: the negative integrating factor cancels the solution drift. Substitute the independently integrated actual quasi-derivative, then apply the genuine physical FTC once more. The endpoint difference is the original initial quasi-derivative times the proved positive denominator plus the actual inhomogeneous remainder. -/
theorem quasiGauge_initial {p q : ℝ} (hpq : p<q) (w : C(ClosedStrip p q,ℝ))
    (b f v : C(ClosedStrip p q,ℂ))
    (hf : ∀ t : ClosedStrip p q,HasDerivWithinAt (stripExtension hpq.le f)
      (2*(w t:ℂ)*f t+v t) (Icc p q) (t:ℝ))
    (hv : ∀ t : ClosedStrip p q,HasDerivWithinAt (stripExtension hpq.le v)
      (b t*f t-2*(w t:ℂ)*v t) (Icc p q) (t:ℝ)) :
    v ⟨p,⟨le_rfl,hpq.le⟩⟩=quasiGaugeInitial hpq.le w b f := by
  -- Both integrations are performed on the unchanged physical strip with genuine actual derivatives.
  let h := stripComplex (stripGauge hpq.le (-2) w)
  let H := quasiGaugePrimitive hpq.le w b f
  let c := v ⟨p,⟨le_rfl,hpq.le⟩⟩
  have hD (t : ClosedStrip p q) :
      HasDerivWithinAt (stripExtension hpq.le (f*h))
        ((ContinuousMap.const (ClosedStrip p q) c*(h*h)+(h*h)*H) t) (Icc p q) (t:ℝ) := by
    have hg := (stripGauge_hasDerivWithinAt hpq.le (-2) w t).ofReal_comp
    have hDer := (hf t).mul hg
    rw [stripExtension_value,stripExtension_value] at hDer
    change HasDerivWithinAt (stripExtension hpq.le (f*h)) _ _ _ at hDer
    convert hDer using 1
    change c*((stripGauge hpq.le (-2) w t:ℂ)*(stripGauge hpq.le (-2) w t:ℂ))+
      ((stripGauge hpq.le (-2) w t:ℂ)*(stripGauge hpq.le (-2) w t:ℂ))*H t=_
    rw [quasiGauge_value hpq w b f v hv t]
    dsimp only [c,H]
    push_cast
    ring
  have he := stripPrimitive_eq_sub hpq (f*h) (ContinuousMap.const _ c*(h*h)+(h*h)*H) hD
  have hl : (f*h) ⟨p,⟨le_rfl,hpq.le⟩⟩=f ⟨p,⟨le_rfl,hpq.le⟩⟩ := by
    change _*(stripGauge hpq.le (-2) w ⟨p,⟨le_rfl,hpq.le⟩⟩:ℂ)=_
    rw [stripGauge_left,Complex.ofReal_one,mul_one]
  rw [hl,map_add,stripPrimitive_const_mul] at he
  have heq := congrArg (fun g : C(ClosedStrip p q,ℂ) => g ⟨q,⟨hpq.le,le_rfl⟩⟩) he
  have hsq : stripPrimitive hpq.le (h*h) ⟨q,⟨hpq.le,le_rfl⟩⟩=(quasiGaugeDenominator hpq.le w:ℂ) := by
    change (∫ r in p..q,(stripGauge hpq.le (-2) w (Set.projIcc p q hpq.le r):ℂ)*
      (stripGauge hpq.le (-2) w (Set.projIcc p q hpq.le r):ℂ))=
      ((∫ r in p..q,stripGauge hpq.le (-2) w (Set.projIcc p q hpq.le r)*
        stripGauge hpq.le (-2) w (Set.projIcc p q hpq.le r):ℝ):ℂ)
    rw [← intervalIntegral.integral_ofReal]
    apply intervalIntegral.integral_congr
    intro r _
    exact (Complex.ofReal_mul _ _).symm
  change c*stripPrimitive hpq.le (h*h) ⟨q,⟨hpq.le,le_rfl⟩⟩+
    quasiGaugeRemainder hpq.le w b f ⟨q,⟨hpq.le,le_rfl⟩⟩=
    f ⟨q,⟨hpq.le,le_rfl⟩⟩*(stripGauge hpq.le (-2) w ⟨q,⟨hpq.le,le_rfl⟩⟩:ℂ)-
      f ⟨p,⟨le_rfl,hpq.le⟩⟩ at heq
  rw [hsq] at heq
  apply (eq_div_iff (Complex.ofReal_ne_zero.mpr (quasiGaugeDenominator_pos hpq w).ne')).mpr
  change c*(quasiGaugeDenominator hpq.le w:ℂ)=_
  linear_combination heq

/-- The complete quasi-derivative reconstructed from only the actual original solution, diagonal and inhomogeneous coefficient.
Use: quasiGauge_reconstruction identifies this norm-continuous expression with the genuine quasi-derivative in the actual finite approximation sequence.
Article: jacobi, Appendix C.2 (transformed ODE and Green identity).
-/
def quasiGaugeReconstruction {p q : ℝ} (hpq : p≤q) (w : C(ClosedStrip p q,ℝ))
    (b f : C(ClosedStrip p q,ℂ)) : C(ClosedStrip p q,ℂ) :=
  stripComplex (stripGauge hpq (-2) w)*
    (ContinuousMap.const _ (quasiGaugeInitial hpq w b f)+quasiGaugePrimitive hpq w b f)

/-- Every genuine physical-strip quasi-derivative equals the explicit reconstruction from the actual original solution data.
Use: its uniform convergence follows from convergence of the actual original diagonals and solutions; no finite first-derivative convergence is supplied as a hypothesis.
Article: jacobi, Appendix C.2 (transformed ODE and Green identity).
Proof: substitute the independently proved true initial value into the exact original integrating-factor identity at each physical point. -/
theorem quasiGauge_reconstruction {p q : ℝ} (hpq : p<q) (w : C(ClosedStrip p q,ℝ))
    (b f v : C(ClosedStrip p q,ℂ))
    (hf : ∀ t : ClosedStrip p q,HasDerivWithinAt (stripExtension hpq.le f)
      (2*(w t:ℂ)*f t+v t) (Icc p q) (t:ℝ))
    (hv : ∀ t : ClosedStrip p q,HasDerivWithinAt (stripExtension hpq.le v)
      (b t*f t-2*(w t:ℂ)*v t) (Icc p q) (t:ℝ)) :
    v=quasiGaugeReconstruction hpq.le w b f := by
  ext t
  change v t=(stripGauge hpq.le (-2) w t:ℂ)*
    (quasiGaugeInitial hpq.le w b f+quasiGaugePrimitive hpq.le w b f t)
  rw [← quasiGauge_initial hpq w b f v hf hv]
  exact quasiGauge_value hpq w b f v hv t

end
end jacobi.GelfandLevitan
