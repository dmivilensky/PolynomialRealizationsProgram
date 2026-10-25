import chebyshev2.SineContinuum.RealLineUnitary
import chebyshev2.SineContinuum.GreenOperator
import chebyshev2.Continuum.KernelOperator

/-!
Article: chebyshev2, Proposition 2.
The eigenbasis on the real line is complete, with the article's exact reference eigenvalues, rather
than an assumed spectral model.
Use: `chebyshev2.SineContinuum.sineKernel_basis` feeds
`chebyshev2.SineContinuum.mercerVector_orthonormal` (mercer Vector orthonormal).
Proof chain: `chebyshev2.SineContinuum.sine_kernel_eigenvalue` — chebyshev2, Proposition 2;
Sine coordinate bijection, symmetry, masses, spectrum, theta formula and tails.
-/
namespace chebyshev2.SineContinuum
noncomputable section
open Set Real MeasureTheory
attribute [local instance] Measure.Subtype.measureSpace
set_option backward.isDefEq.respectTransparency false

/--
Defines `sineKernel` of type `Continuum.FeatureSpace →L[ℝ] Continuum.FeatureSpace` by
`Continuum.kernelOperator m_integrable (fun x => (m_positive x).le)`.

Use: `chebyshev2.SineContinuum.sineKernel_conjugacy` uses this definition to establish the
precise assertion is `realLineUnitary.toContinuousLinearEquiv.toContinuousLinearMap ∘L
sineKernel ∘L realLineUnitary.symm.toContinuousLinearEquiv.toContinuousLinearMap= (2:ℝ) •
greenOperator`.

Article: chebyshev2, Proposition 2 via `chebyshev2.SineContinuum.sine_kernel_eigenvalue`.
-/
def sineKernel : Continuum.FeatureSpace →L[ℝ] Continuum.FeatureSpace :=
  Continuum.kernelOperator m_integrable (fun x => (m_positive x).le)

/--
The precise assertion is `(n (X t)/√(SineJacobi.phi t)) * (∫ y, exp (-|X t-y|)*n y*f y)=
2*inner ℝ (greenRow ⟨t,⟨ht.1.le,ht.2.le⟩⟩) (realLineUnitary f)`.

Use: `chebyshev2.SineContinuum.sineKernel_conjugacy_apply` rewrites with this identity to
establish the precise assertion is `realLineUnitary (sineKernel f)= (2:ℝ) • greenOperator
(realLineUnitary f)`.

Article: chebyshev2, Proposition 2 via `chebyshev2.SineContinuum.sine_kernel_eigenvalue`.

Proof: Intersect the eventual or almost-everywhere hypotheses, then prove the asserted relation
at an arbitrary point in that intersection. Identify the summands/integrands on their required
domain before replacing the sum or integral. Clear the denominators using the available nonzero
hypotheses, then verify the remaining algebraic identity.
-/
theorem transformed_kernel_integral (f : Continuum.FeatureSpace) {t : ℝ}
    (ht : t ∈ Ioo (0:ℝ) 1) :
    (n (X t)/√(SineJacobi.phi t)) *
      (∫ y, exp (-|X t-y|)*n y*f y)=
    2*inner ℝ (greenRow ⟨t,⟨ht.1.le,ht.2.le⟩⟩) (realLineUnitary f) := by
  -- Intersect the eventual or almost-everywhere hypotheses, then prove the asserted relation
  -- at an arbitrary point in that intersection.
  have hp := SineJacobi.phi_pos ht
  have hq : n (X t)/√(SineJacobi.phi t)=√(SineJacobi.phi t) := by
    rw [n_X ht]
    apply (div_eq_iff (sqrt_pos.mpr hp).ne').mpr
    simpa only [pow_two] using (sq_sqrt hp.le).symm
  rw [hq,coordinate_integral]
  rw [← integral_Icc_eq_integral_Ioo]
  rw [← integral_subtype (s := Icc (0:ℝ) 1) measurableSet_Icc
    (fun s : ℝ => (SineJacobi.phi s)⁻¹*(exp (-|X t-X s|)*n (X s)*f (X s)))]
  rw [← integral_const_mul,L2.inner_def,← integral_const_mul]
  apply integral_congr_ae
  filter_upwards [realLineUnitary_ae f,greenRow_ae ⟨t,⟨ht.1.le,ht.2.le⟩⟩,
    interval_interior_ae] with s hu hg hs
  rw [hg]
  change √(SineJacobi.phi t)*((SineJacobi.phi s)⁻¹*
    (exp (-|X t-X s|)*n (X s)*f (X s)))=
    2*((realLineUnitary f s)*green t s)
  rw [hu,n_X hs]
  have he := exponential_kernel ht hs
  have hps := SineJacobi.phi_pos hs
  field_simp [(sqrt_pos.mpr hps).ne',hps.ne']
  calc
    _ = (√(SineJacobi.phi t)*√(SineJacobi.phi s)*exp (-|X t-X s|))*f (X s) := by ring
    _ = _ := by rw [he]; ring

/--
Literal Proposition 2 conjugacy, on all L² vectors.

The precise assertion is `realLineUnitary (sineKernel f)= (2:ℝ) • greenOperator
(realLineUnitary f)`.

Use: `chebyshev2.SineContinuum.sineKernel_basis` rewrites with this identity to establish
the precise assertion is `sineKernel (sineRealHilbertBasis j)= Continuum.referenceEigenvalue j
• sineRealHilbertBasis j`.

Article: chebyshev2, Proposition 2 via `chebyshev2.SineContinuum.sine_kernel_eigenvalue`.

Proof: Intersect the eventual or almost-everywhere hypotheses, then prove the asserted relation
at an arbitrary point in that intersection.
-/
theorem sineKernel_conjugacy_apply (f : Continuum.FeatureSpace) :
    realLineUnitary (sineKernel f)= (2:ℝ) • greenOperator (realLineUnitary f) := by
  -- Intersect the eventual or almost-everywhere hypotheses, then prove the asserted relation
  -- at an arbitrary point in that intersection.
  apply Lp.ext
  have hk := realLineWeight.base_ac.ae_eq
    (X_interval_measurePreserving.quasiMeasurePreserving.ae_eq_comp
      (Continuum.kernelOperator_coe m_integrable (fun x => (m_positive x).le) f))
  filter_upwards [realLineUnitary_ae (sineKernel f),hk,
    Lp.coeFn_smul (2:ℝ) (greenOperator (realLineUnitary f)),
    greenOperator_ae (realLineUnitary f),interval_interior_ae] with t hu hk hs hg ht
  change sineKernel f (X t)=_ at hk
  rw [hu,hk,hs]
  simp only [Function.comp_def,Pi.smul_apply,smul_eq_mul,sqrt_m]
  rw [hg]
  rw [← transformed_kernel_integral f ht]
  ring

/--
The precise assertion is `realLineUnitary.toContinuousLinearEquiv.toContinuousLinearMap ∘L
sineKernel ∘L realLineUnitary.symm.toContinuousLinearEquiv.toContinuousLinearMap= (2:ℝ) •
greenOperator`.

Use: a standalone supporting identity for the article chain below; no retained declaration
currently has an explicit proof dependency on it.

Article: chebyshev2, Proposition 2.

Proof: Use the identities/estimates `chebyshev2.SineContinuum.sineKernel_conjugacy_apply`
with the arguments shown in the proof.
-/
theorem sineKernel_conjugacy :
    realLineUnitary.toContinuousLinearEquiv.toContinuousLinearMap ∘L sineKernel ∘L
      realLineUnitary.symm.toContinuousLinearEquiv.toContinuousLinearMap= (2:ℝ) • greenOperator := by
  apply ContinuousLinearMap.ext
  intro f
  change realLineUnitary (sineKernel (realLineUnitary.symm f))= (2:ℝ) • greenOperator f
  simpa only [LinearIsometryEquiv.apply_symm_apply] using
    sineKernel_conjugacy_apply (realLineUnitary.symm f)

/--
The eigenbasis on the real line is complete, with the article's exact reference eigenvalues,
rather than an assumed spectral model.

Use: `chebyshev2.SineContinuum.sineKernel_basis` uses this definition to establish the
precise assertion is `sineKernel (sineRealHilbertBasis j)= Continuum.referenceEigenvalue j •
sineRealHilbertBasis j`.

Article: chebyshev2, Proposition 2 via `chebyshev2.SineContinuum.sine_kernel_eigenvalue`.
-/
def sineRealHilbertBasis : HilbertBasis ℕ ℝ Continuum.FeatureSpace :=
  HilbertBasis.ofRepr (realLineUnitary.trans sineHilbertBasis.repr)

/--
Exact identity `sineRealHilbertBasis j=realLineUnitary.symm (sineHilbertBasis j)`.

Use: `chebyshev2.SineContinuum.sineKernel_basis` rewrites with this identity to establish
the precise assertion is `sineKernel (sineRealHilbertBasis j)= Continuum.referenceEigenvalue j
• sineRealHilbertBasis j`.

Article: chebyshev2, Proposition 2 via `chebyshev2.SineContinuum.sine_kernel_eigenvalue`.

Proof: The identity follows by unfolding the definitions; no estimate or limiting argument is
involved.
-/
theorem sineRealHilbertBasis_apply (j : ℕ) :
    sineRealHilbertBasis j=realLineUnitary.symm (sineHilbertBasis j) := rfl

/--
The precise assertion is `sineKernel (sineRealHilbertBasis j)= Continuum.referenceEigenvalue j
• sineRealHilbertBasis j`.

Use: `chebyshev2.SineContinuum.mercerVector_orthonormal` rewrites with this identity to
establish the precise assertion is `Orthonormal ℝ mercerVector`.

Article: chebyshev2, Proposition 2 via `chebyshev2.SineContinuum.sine_kernel_eigenvalue`.

Proof: Use the identities/estimates `chebyshev2.SineContinuum.sineKernel_conjugacy_apply`,
`chebyshev2.SineContinuum.sineRealHilbertBasis_apply`,
`chebyshev2.SineContinuum.greenOperator_basis` with the arguments shown in the proof.
-/
theorem sineKernel_basis (j : ℕ) :
    sineKernel (sineRealHilbertBasis j)=
      Continuum.referenceEigenvalue j • sineRealHilbertBasis j := by
  -- Use the identities/estimates `chebyshev2.SineContinuum.sineKernel_conjugacy_apply`,
  -- `chebyshev2.SineContinuum.sineRealHilbertBasis_apply`,
  -- `chebyshev2.SineContinuum.greenOperator_basis` with the arguments shown in the proof.
  apply realLineUnitary.injective
  rw [sineKernel_conjugacy_apply,sineRealHilbertBasis_apply,
    realLineUnitary.apply_symm_apply,greenOperator_basis,map_smul,
    realLineUnitary.apply_symm_apply]
  rw [smul_smul,mu_reference]
  congr 1
  ring

end
end chebyshev2.SineContinuum
