import jacobi.Hankel.BesselConnection

/-!
Article: jacobi, Lemma E.1.
Use: outgoingBesselCoefficient fixes one actual Cauchy-data evaluation independent of the spectral zero index.
-/
namespace jacobi.Hankel
noncomputable section
open Set
set_option backward.isDefEq.respectTransparency false

/-- The true original outgoing Bessel connection coefficient is spatially constant on the entire common positive ray.
Use: outgoingBesselCoefficient fixes one actual Cauchy-data evaluation independent of the spectral zero index.
Article: jacobi, Lemma E.1.
Proof: its actual derivative vanishes at every point of the original connected open ray, so the community real mean-value theorem identifies any two original evaluations. -/
theorem outgoingConnection_constant {R : ℝ} (hR : 0<R) {a : ℂ}
    (ha : -1<a.re) (hc : ‖besselCoefficient a‖/R<1) {x y : ℝ} (hx : R<x) (hy : R<y) :
    outgoingConnection hR a x=outgoingConnection hR a y :=
  isOpen_Ioi.is_const_of_deriv_eq_zero (convex_Ioi R).isPreconnected
    (fun _t ht => (outgoingConnection_hasDerivAt hR ha hc ht).differentiableAt.differentiableWithinAt)
    (fun _t ht => (outgoingConnection_hasDerivAt hR ha hc ht).deriv) hx hy

/-- The true original incoming Bessel connection coefficient is spatially constant on the same common ray.
Use: incomingBesselCoefficient uses the same genuine evaluation point as the outgoing coefficient.
Article: jacobi, Lemma E.1.
Proof: apply constancy from the already proved actual zero derivative on the connected original positive ray. -/
theorem incomingConnection_constant {R : ℝ} (hR : 0<R) {a : ℂ}
    (ha : -1<a.re) (hc : ‖besselCoefficient a‖/R<1) {x y : ℝ} (hx : R<x) (hy : R<y) :
    incomingConnection hR a x=incomingConnection hR a y :=
  isOpen_Ioi.is_const_of_deriv_eq_zero (convex_Ioi R).isPreconnected
    (fun _t ht => (incomingConnection_hasDerivAt hR ha hc ht).differentiableAt.differentiableWithinAt)
    (fun _t ht => (incomingConnection_hasDerivAt hR ha hc ht).deriv) hx hy

/-- The genuine outgoing coefficient of the original normalized Bessel function, fixed at the common point R+1.
Use: bessel_decomposition is an exact expansion of the original Bessel function with coefficients independent of its spatial coordinate or zero index.
Article: jacobi, Lemma E.1.
-/
def outgoingBesselCoefficient {R : ℝ} (hR : 0<R) (a : ℂ) : ℂ :=
  outgoingConnection hR a (R+1)

/-- The genuine incoming coefficient of the original normalized Bessel function at the same common point R+1.
Use: the relative phase in the original numbered-zero Hankel expansion is determined from this true coefficient and its outgoing counterpart.
Article: jacobi, Lemma E.1.
-/
def incomingBesselCoefficient {R : ℝ} (hR : 0<R) (a : ℂ) : ℂ :=
  incomingConnection hR a (R+1)

/-- The genuine two opposite original real-ray Fourier phases multiply exactly to one.
Use: bessel_decomposition_at cancels the true spatial phase factors in the original Cauchy-data reconstruction.
Article: jacobi, Lemma E.1.
Proof: combine the two actual complex exponentials and cancel their opposite exponents. -/
theorem realPhase_cancel (x : ℝ) : realPhase Complex.I x*realPhase (-Complex.I) x=1 := by
  unfold realPhase
  rw [← Complex.exp_add]
  ring_nf
  exact Complex.exp_zero

/-- The actual original Bessel solution is reconstructed exactly from its true mixed Jost coefficients at any point of the original far ray.
Use: bessel_decomposition replaces these pointwise coefficients by their same actual fixed-base values, establishing the original Bessel-Jost identity.
Article: jacobi, Lemma E.1.
Proof: the two opposite Fourier phases cancel exactly, and the two original mixed numerators sum to Y times the actual Jost Wronskian. Divide by its independently proved genuine value -2i. -/
theorem bessel_decomposition_at {R : ℝ} (hR : 0<R) {a : ℂ}
    (hc : ‖besselCoefficient a‖/R≤1/2) {x : ℝ} (hx : R<x) :
    complexBesselWave a x=
      outgoingConnection hR a x*realPhase Complex.I x*besselAmplitude hR a x+
      incomingConnection hR a x*realPhase (-Complex.I) x*incomingAmplitude hR a x := by
  -- This is actual Cauchy reconstruction, with its true basis determinant proved nonzero before division.
  have hd : (-2*Complex.I:ℂ)≠0 := mul_ne_zero (by norm_num) Complex.I_ne_zero
  have hN : complexBesselWave a x*jostWronskian hR a x=
      outgoingConnectionNumerator hR a x*besselAmplitude hR a x+
      incomingConnectionNumerator hR a x*incomingAmplitude hR a x := by
    dsimp only [jostWronskian,outgoingConnectionNumerator,incomingConnectionNumerator]
    ring
  have hp : outgoingConnection hR a x*realPhase Complex.I x*besselAmplitude hR a x=
      (outgoingConnectionNumerator hR a x*besselAmplitude hR a x)/(-2*Complex.I) := calc
    _ = (realPhase Complex.I x*realPhase (-Complex.I) x)*
        ((outgoingConnectionNumerator hR a x*besselAmplitude hR a x)/(-2*Complex.I)) := by
      unfold outgoingConnection
      ring
    _ = _ := by rw [realPhase_cancel,one_mul]
  have hm : incomingConnection hR a x*realPhase (-Complex.I) x*incomingAmplitude hR a x=
      (incomingConnectionNumerator hR a x*incomingAmplitude hR a x)/(-2*Complex.I) := calc
    _ = (realPhase Complex.I x*realPhase (-Complex.I) x)*
        ((incomingConnectionNumerator hR a x*incomingAmplitude hR a x)/(-2*Complex.I)) := by
      unfold incomingConnection
      ring
    _ = _ := by rw [realPhase_cancel,one_mul]
  rw [hp,hm,← add_div,← hN,jostWronskian_formula hR hc hx,mul_div_cancel_right₀ _ hd]

/-- The genuine original complex-order normalized Bessel wave has an exact decomposition in the two actual Jost solutions, with coefficients fixed at one common spatial point.
Use: its uniform cubic expansion is now a comparison of the original Bessel function with the genuine constructed Jost remainder; the remaining relative-phase and complex-frequency arguments identify the original numbered zero tail.
Article: jacobi, Lemma E.1.
Proof: reconstruct the original Bessel solution pointwise by the independently proved nonzero Jost determinant, and use the actual zero derivatives of its two original connection coefficients to replace them by their genuine Cauchy values at R+1. -/
theorem bessel_decomposition {R : ℝ} (hR : 0<R) {a : ℂ}
    (ha : -1<a.re) (hc : ‖besselCoefficient a‖/R≤1/2) {x : ℝ} (hx : R<x) :
    complexBesselWave a x=
      outgoingBesselCoefficient hR a*realPhase Complex.I x*besselAmplitude hR a x+
      incomingBesselCoefficient hR a*realPhase (-Complex.I) x*incomingAmplitude hR a x := by
  have hs : ‖besselCoefficient a‖/R<1 := hc.trans_lt (by norm_num)
  rw [bessel_decomposition_at hR hc hx,
    outgoingConnection_constant hR ha hs hx (show R<R+1 by linarith),
    incomingConnection_constant hR ha hs hx (show R<R+1 by linarith)]
  rfl

/-- A zero of the actual original Liouville Bessel wave is precisely a zero of the same original normalized entire Bessel function at the squared spatial coordinate.
Use: the genuine Jost decomposition transfers its actual zero estimates to the original Bessel spectrum sigma_k, without changing the spectral function or its zero set.
Article: jacobi, Lemma E.1.
Proof: the true logarithmic prefactor is a complex exponential and never vanishes. -/
theorem complexBesselWave_zero_iff (a : ℂ) (x : ℝ) :
    complexBesselWave a x=0 ↔ jacobi.Bessel.normalized a ((x:ℂ)^2)=0 := by
  rw [complexBesselWave,complexWaveFactor,mul_eq_zero,or_iff_right (Complex.exp_ne_zero _)]

end
end jacobi.Hankel
