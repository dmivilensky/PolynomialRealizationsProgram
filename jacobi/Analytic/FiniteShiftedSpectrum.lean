import jacobi.Analytic.DenominatorNeighborhood
import jacobi.Analytic.ShiftedSpectrum
import jacobi.Jacobi.SpectralLimit

/-!
Article: jacobi, Appendix C.6 (uniform shifted spectral convergence).
The actual padded finite Jacobi edge spectrum has uniformly nonzero
shifted resolvent denominators on every compact subset of the original
slit plane. All finite poles are excluded by the proved original L1
spectral limit and a genuine common denominator neighbourhood.
Use: finiteShiftedEdge and shiftedEdge use the same exact transform; its difference identity transfers the full actual L1 spectral limit.
-/
namespace jacobi.EdgeResolvent
noncomputable section
open Real Set Filter
open scoped Topology

/-- The resolvent transform of a real scaled spectral value, including
its zero padding, in the original edge shift coordinate.
Use: finiteShiftedEdge and shiftedEdge use the same exact transform;
its difference identity transfers the full actual L1 spectral limit.
Article: jacobi, Appendix C.6 (uniform shifted spectral convergence).
-/
def resolventTransform (r:ℝ) (w:ℂ) : ℂ := (r:ℂ)*(1+((r/2:ℝ):ℂ)*w)⁻¹

/-- The actual shifted finite Jacobi resolvent spectrum with the true
N=n+1 matrix dimension and its original spectral zero padding.
Use: Theorem C.5 sums this same genuine spectrum against the actual
finite target eigenvectors; no surrogate finite eigenvalues are used.
Article: jacobi, Appendix C.6 (uniform shifted spectral convergence).
-/
def finiteShiftedEdge (a b:ℝ) (ha:-1<a) (hb:-1<b) (n k:ℕ) (w:ℂ) : ℂ :=
  resolventTransform (jacobi.Jacobi.finiteLambdaAt a b ha hb (n+1) k) w

/-- The genuine shifted Bessel spectrum is exactly the same resolvent
transform of its original unshifted edge spectrum.
Use: finite shifted L1 convergence compares the actual original finite
and infinite coefficients by a single exact scalar difference identity.
Article: jacobi, Appendix C.6 (uniform shifted spectral convergence).
Proof: the original edge value is 2/sigma, so its half is 1/sigma;
the independently proved genuine shifted factorization then applies. -/
theorem shiftedEdge_transform (a:ℝ) (ha:-1<a) (k:ℕ) {w:ℂ} (hw:w∈edgeDomain a ha) :
    shiftedEdge a ha k w=resolventTransform (jacobi.Bessel.edgeValue a ha k) w := by
  have he : jacobi.Bessel.edgeValue a ha k/2=1/ jacobi.Bessel.sigma a ha k := by
    rw [jacobi.Bessel.edgeValue]
    ring
  rw [shiftedEdge_factor a ha k hw,resolventTransform,he]

/-- All genuine shifted finite Jacobi denominators are uniformly
nonzero with a common inverse bound on every original compact shift set.
Use: the complete Lemma specw and Theorem C.5 require no independently
assumed pole-exclusion or finite spectral-majorant certificate.
Article: jacobi, Appendix C.6 (uniform shifted spectral convergence).
Proof: the actual finite/limiting L1 spectral distance bounds each
coordinate error. The limiting half-coordinates lie in the proved
positive reciprocal-sigma interval. The common compact denominator
neighbourhood therefore applies to every actual finite mode at once. -/
theorem finite_denominator_compact {a b:ℝ} (ha:-1<a) (hb:-1<b)
    {W:Set ℂ} (hW:IsCompact W) (hsub:W⊆edgeDomain a ha) :
    ∃C:ℝ,0<C ∧ ∀ᶠn:ℕ in atTop,∀k:ℕ,∀w∈W,
      (1+((jacobi.Jacobi.finiteLambdaAt a b ha hb (n+1) k/2:ℝ):ℂ)*w≠0) ∧
      ‖(1+((jacobi.Jacobi.finiteLambdaAt a b ha hb (n+1) k/2:ℝ):ℂ)*w)⁻¹‖≤C ∧
      ‖(1+((jacobi.Bessel.edgeValue a ha k/2:ℝ):ℂ)*w)⁻¹‖≤C := by
  -- The true zero-padded spectra are compared before introducing any shifted finite inverse.
  obtain ⟨δ,C,hδ,hC,hclose⟩ := denominator_neighborhood
    (jacobi.Bessel.spectralZero_pos ha (jacobi.Bessel.sigma_mem ha 0)) hW hsub
  have hd := (jacobi.Jacobi.finiteLambdaAt_l1_tendsto ha hb).comp (tendsto_add_atTop_nat 1)
  refine ⟨C,hC,?_⟩
  filter_upwards [hd.eventually (Iio_mem_nhds (by positivity : (0:ℝ)<2*δ))] with n hn k w hw
  dsimp only [Function.comp_def] at hn
  have hS := ((jacobi.Jacobi.finiteLambdaAt_summable ha hb (n+1)).sub (jacobi.Bessel.edgeValue_summable ha)).abs
  have hpoint := hS.le_tsum k (fun j _ => abs_nonneg _)
  have hy : jacobi.Bessel.edgeValue a ha k/2∈Icc (0:ℝ) (1/ jacobi.Bessel.sigma a ha 0) := by
    have he : jacobi.Bessel.edgeValue a ha k/2=1/ jacobi.Bessel.sigma a ha k := by
      rw [jacobi.Bessel.edgeValue]
      ring
    rw [he]
    exact inverse_sigma_mem a ha k
  have hxy : |jacobi.Jacobi.finiteLambdaAt a b ha hb (n+1) k/2- jacobi.Bessel.edgeValue a ha k/2|≤δ := by
    rw [← sub_div,abs_div,abs_of_pos (by norm_num : (0:ℝ)<2)]
    linarith
  have hfin := hclose w hw _ _ hy hxy
  have hlim := hclose w hw (jacobi.Bessel.edgeValue a ha k/2) _ hy
    (by simpa only [sub_self,abs_zero] using hδ.le)
  exact ⟨hfin.1,hfin.2,hlim.2⟩

/-- The same scalar resolvent transform has its exact original
spectral difference formula wherever both actual denominators are nonzero.
Use: finiteShiftedEdge_l1_uniform obtains a common compact Lipschitz
bound times the genuine unshifted spectral L1 distance.
Article: jacobi, Appendix C.6 (uniform shifted spectral convergence).
Proof: cancel the two genuine nonzero scalar denominators; the mixed
w*r*s terms cancel exactly. -/
theorem resolventTransform_sub (r s:ℝ) (w:ℂ)
    (hr:1+((r/2:ℝ):ℂ)*w≠0) (hs:1+((s/2:ℝ):ℂ)*w≠0) :
    resolventTransform r w-resolventTransform s w=
      ((r-s:ℝ):ℂ)*(1+((r/2:ℝ):ℂ)*w)⁻¹*(1+((s/2:ℝ):ℂ)*w)⁻¹ := by
  -- The two genuine denominator cross-terms cancel before any inverse is simplified.
  have hn : (r:ℂ)*(1+((s/2:ℝ):ℂ)*w)-(1+((r/2:ℝ):ℂ)*w)*(s:ℂ)=((r-s:ℝ):ℂ) := by
    push_cast
    ring
  unfold resolventTransform
  calc
    _=((r:ℂ)*(1+((s/2:ℝ):ℂ)*w)-(1+((r/2:ℝ):ℂ)*w)*(s:ℂ))/
        ((1+((r/2:ℝ):ℂ)*w)*(1+((s/2:ℝ):ℂ)*w)) := by
      simpa only [div_eq_mul_inv] using div_sub_div (r:ℂ) (s:ℂ) hr hs
    _=_ := by rw [hn,div_eq_mul_inv,mul_inv_rev]; ring

end
end jacobi.EdgeResolvent
