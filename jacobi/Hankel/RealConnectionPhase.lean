import jacobi.Hankel.BesselDecomposition
import jacobi.Bessel.WeylPhase
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

/-!
Article: jacobi, Lemma E.1.
Use: real_bessel_connection_phase identifies this precise phase in the original Bessel-Jost coefficients from the canonical numbered zeros.
-/
namespace jacobi.Hankel
noncomputable section
open Set Filter jacobi.Bessel
open scoped Topology BoundedContinuousFunction
set_option backward.isDefEq.respectTransparency false

/-- The original squared-zero phase factor, as an entire function of complex order.
Use: real_bessel_connection_phase identifies this precise phase in the original Bessel-Jost coefficients from the canonical numbered zeros.
Article: jacobi, Lemma E.1.
-/
def besselZeroPhase (a : ℂ) : ℂ := Complex.exp (2*Complex.I*(Real.pi:ℂ)*(a/2+3/4))

/-- The original doubled Fourier phase at the canonical real phase grid is exactly its index-independent Bessel factor.
Use: positiveZero_fourier_limit removes the genuine integer zero index from the exponential without an unspecified phase shift.
Article: jacobi, Lemma E.1.
Proof: separate the actual integer multiple of 2*pi*i and use the community exact exponential periodicity theorem. -/
theorem realPhase_grid (a : ℝ) (k : ℕ) :
    realPhase (2*Complex.I) (phaseGrid a k)=besselZeroPhase (a:ℂ) := by
  unfold realPhase phaseGrid besselZeroPhase
  rw [show 2*Complex.I*((Real.pi*((k:ℝ)+a/2+3/4):ℝ):ℂ)=
    (k:ℂ)*(2*(Real.pi:ℂ)*Complex.I)+2*Complex.I*(Real.pi:ℂ)*((a:ℂ)/2+3/4) by push_cast; ring]
  rw [Complex.exp_add,Complex.exp_nat_mul_two_pi_mul_I,one_mul]

/-- The actual doubled Fourier phases of the original numbered Bessel zeros converge to their exact source phase factor.
Use: real_bessel_connection_phase evaluates the genuine Bessel-Jost decomposition at the original zero tail and fixes the original relative phase.
Article: jacobi, Lemma E.1.
Proof: the already verified actual zero minus its canonical phase grid tends to zero. The true integer-grid exponential is exactly constant, so continuity of the original complex exponential proves the limit. -/
theorem positiveZero_fourier_limit {a : ℝ} (ha : -1<a) :
    Tendsto (fun k : ℕ => realPhase (2*Complex.I) (positiveZero a ha k)) atTop
      (𝓝 (besselZeroPhase (a:ℂ))) := by
  -- The known real McMahon phase has the genuine zero enumeration fixed before this complex Fourier limit is taken.
  have hc : Continuous (realPhase (2*Complex.I)) := by unfold realPhase; fun_prop
  have h : Tendsto (fun k : ℕ => realPhase (2*Complex.I) (positiveZero a ha k-phaseGrid a k))
      atTop (𝓝 1) := by
    convert! hc.tendsto 0 |>.comp (positiveZero_phase_tendsto ha) using 1
    simp [realPhase]
  have he (k : ℕ) : realPhase (2*Complex.I) (positiveZero a ha k)=
      realPhase (2*Complex.I) (positiveZero a ha k-phaseGrid a k)*besselZeroPhase (a:ℂ) := by
    rw [← realPhase_grid a k]
    unfold realPhase
    rw [← Complex.exp_add]
    congr 1
    push_cast
    ring
  rw [show (fun k : ℕ => realPhase (2*Complex.I) (positiveZero a ha k))=
    (fun k => realPhase (2*Complex.I) (positiveZero a ha k-phaseGrid a k)*besselZeroPhase (a:ℂ)) from funext he]
  simpa only [one_mul] using h.mul_const (besselZeroPhase (a:ℂ))

/-- The genuine positive Fourier phase squared is precisely the original doubled Fourier phase.
Use: bessel_connection_at_zero multiplies the original Bessel decomposition by its actual positive Fourier phase.
Article: jacobi, Lemma E.1.
Proof: combine the two actual complex exponentials and collect their doubled original exponent. -/
theorem realPhase_square (x : ℝ) :
    realPhase Complex.I x*realPhase Complex.I x=realPhase (2*Complex.I) x := by
  unfold realPhase
  rw [← Complex.exp_add]
  congr 1
  ring

/-- At every original Bessel zero on the common Jost ray, the two true constant connection coefficients satisfy their exact oscillatory relation.
Use: real_bessel_connection_phase takes the genuine original zero-tail limit of this equation to determine the exact incoming/outgoing phase.
Article: jacobi, Lemma E.1.
Proof: the original squared-zero enumeration makes the true Liouville Bessel wave vanish. Multiply its exact Jost decomposition by the genuine positive Fourier factor, then use its actual square and opposite-phase cancellation identities. -/
theorem bessel_connection_at_zero {R : ℝ} (hR : 0<R) {a : ℝ} (ha : -1<a)
    (hc : ‖besselCoefficient (a:ℂ)‖/R≤1/2) (k : ℕ) (hk : R<positiveZero a ha k) :
    outgoingBesselCoefficient hR (a:ℂ)*realPhase (2*Complex.I) (positiveZero a ha k)*
      besselAmplitude hR (a:ℂ) (positiveZero a ha k)+
      incomingBesselCoefficient hR (a:ℂ)*incomingAmplitude hR (a:ℂ) (positiveZero a ha k)=0 := by
  -- This equation is evaluated at genuine original zeros, not at an assumed nearby phase-grid root.
  let x := positiveZero a ha k
  have hz : complexBesselWave (a:ℂ) x=0 := by
    rw [complexBesselWave_zero_iff,← Complex.ofReal_pow,(positiveZero_properties ha k).2]
    exact sigma_mem ha k
  have hd := congrArg (fun z : ℂ => realPhase Complex.I x*z)
    (bessel_decomposition hR (by simpa only [Complex.ofReal_re] using ha) hc hk)
  rw [hz,mul_zero] at hd
  linear_combination -hd-
    (outgoingBesselCoefficient hR (a:ℂ)*besselAmplitude hR (a:ℂ) x)*(realPhase_square x)-
    (incomingBesselCoefficient hR (a:ℂ)*incomingAmplitude hR (a:ℂ) x)*(realPhase_cancel x)

/-- The actual original real-order Bessel-Jost connection coefficients have the exact canonically numbered relative phase.
Use: the complex-order identity argument extends this true phase, allowing the genuine cubic outgoing/incoming expansion to locate the original numbered Bessel zeros uniformly on a common complex-order disk.
Article: jacobi, Lemma E.1.
Proof: evaluate the actual Bessel-Jost decomposition at its genuine numbered zeros, which tend to infinity. Both actual Jost amplitudes tend to one, and the proved canonical doubled Fourier zero phase has its exact limit. The genuine zero equation therefore gives B=-exp(2*i*pi*(alpha/2+3/4))*A. -/
theorem real_bessel_connection_phase {R : ℝ} (hR : 0<R) {a : ℝ} (ha : -1<a)
    (hc : ‖besselCoefficient (a:ℂ)‖/R≤1/2) :
    incomingBesselCoefficient hR (a:ℂ)=
      -besselZeroPhase (a:ℂ)*outgoingBesselCoefficient hR (a:ℂ) := by
  -- Only already proved original numbered-zero and true Jost endpoint limits enter this phase determination.
  have hp := (besselAmplitude_limit hR hc).comp (positiveZero_tendsto ha)
  have hm := (incomingAmplitude_limit hR hc).comp (positiveZero_tendsto ha)
  have he := (((positiveZero_fourier_limit ha).mul hp).const_mul (outgoingBesselCoefficient hR (a:ℂ))).add
    (hm.const_mul (incomingBesselCoefficient hR (a:ℂ)))
  have hz : Tendsto (fun k : ℕ =>
      outgoingBesselCoefficient hR (a:ℂ)*realPhase (2*Complex.I) (positiveZero a ha k)*
        besselAmplitude hR (a:ℂ) (positiveZero a ha k)+
        incomingBesselCoefficient hR (a:ℂ)*incomingAmplitude hR (a:ℂ) (positiveZero a ha k))
      atTop (𝓝 0) := tendsto_const_nhds.congr' (by
    filter_upwards [(positiveZero_tendsto ha).eventually_gt_atTop R] with k hk
    exact (bessel_connection_at_zero hR ha hc k hk).symm)
  have hlim : outgoingBesselCoefficient hR (a:ℂ)*besselZeroPhase (a:ℂ)+
      incomingBesselCoefficient hR (a:ℂ)=0 := by
    have he' : Tendsto (fun k : ℕ =>
        outgoingBesselCoefficient hR (a:ℂ)*realPhase (2*Complex.I) (positiveZero a ha k)*
          besselAmplitude hR (a:ℂ) (positiveZero a ha k)+
          incomingBesselCoefficient hR (a:ℂ)*incomingAmplitude hR (a:ℂ) (positiveZero a ha k))
        atTop (𝓝 (outgoingBesselCoefficient hR (a:ℂ)*besselZeroPhase (a:ℂ)+incomingBesselCoefficient hR (a:ℂ))) := by
      convert! he using 1
      · funext k
        dsimp only [Function.comp_def]
        ring
      · simp only [mul_one]
    exact tendsto_nhds_unique he' hz
  linear_combination hlim

end
end jacobi.Hankel
