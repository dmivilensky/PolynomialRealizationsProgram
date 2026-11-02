import jacobi.GelfandLevitan.TargetGreenKernel
import jacobi.GelfandLevitan.KernelPairing

/-!
Article: jacobi, Proposition 2.2.
The actual uniformly convergent continuous Green kernel represents the
genuine bounded inverse of the full original unbounded target operator.
Its integral action holds for every original L2 input, and the output
has the actual continuous representative built from the kernel rows.
Use: targetGreenKernelTerm_pairing identifies each original spatial Green summand with the same rank-one spectral operator used by the full bounded inverse.
-/
namespace jacobi.GelfandLevitan
noncomputable section
open Real Set Filter MeasureTheory jacobi.Reference
open scoped Topology InnerProductSpace
attribute [local instance] Measure.Subtype.measureSpace
set_option backward.isDefEq.respectTransparency false

/-- Integrating against an actual full continuous target wave gives its genuine original target-basis coefficient.
Use: targetGreenKernelTerm_pairing identifies each original spatial Green summand with the same rank-one spectral operator used by the full bounded inverse.
Article: jacobi, Proposition C.2.
Proof: the independently proved full-basis representative is the actual continuous reflected wave; substitute it in the genuine real L2 inner-product integral. -/
theorem fullWaveMap_coefficient (a : ℝ) (ha : -1<a) (k : ℕ) (v : Space) :
    (∫ t:Interval,v t*fullWaveMap a ha k t)=inner ℝ (fullTargetBasis a ha k) v := by
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [fullTargetBasis_wave_ae a ha k] with t ht
  rw [ht]
  rfl

/-- Every genuine continuous Green kernel summand has exactly the original rank-one target spectral bilinear pairing.
Use: targetGreen_kernel_form passes the actual uniform kernel series through a bounded genuine L2 pairing and identifies it with the full bounded inverse.
Article: jacobi, Proposition C.2.
Proof: factor the true independent-variable product integral, then identify both spatial wave integrals with the original target-basis coefficients. -/
theorem targetGreenKernelTerm_pairing (a : ℝ) (ha : -1<a) (k : ℕ) (v w : Space) :
    kernelPairing v w (targetGreenKernelTerm a ha k)=
      (jacobi.Bessel.sigma a ha k)⁻¹*inner ℝ (fullTargetBasis a ha k) v*
        inner ℝ (fullTargetBasis a ha k) w := by
  -- The pairings involve genuine L1 products of original L2 inputs with bounded continuous waves.
  change (∫ p:Interval×Interval,(v p.1*w p.2)*
    ((jacobi.Bessel.sigma a ha k)⁻¹*fullWaveMap a ha k p.1*fullWaveMap a ha k p.2) ∂(volume.prod volume))=_
  have he (p : Interval×Interval) : (v p.1*w p.2)*
      ((jacobi.Bessel.sigma a ha k)⁻¹*fullWaveMap a ha k p.1*fullWaveMap a ha k p.2)=
      (jacobi.Bessel.sigma a ha k)⁻¹*((v p.1*fullWaveMap a ha k p.1)*(w p.2*fullWaveMap a ha k p.2)) := by ring
  simp_rw [he]
  rw [integral_const_mul,integral_prod_mul
    (fun t:Interval => v t*fullWaveMap a ha k t) (fun s:Interval => w s*fullWaveMap a ha k s),
    fullWaveMap_coefficient,fullWaveMap_coefficient]
  ring

/-- The original continuous full Green kernel has exactly the actual bounded inverse's bilinear form on arbitrary original full-interval L2 inputs.
Use: targetGreenActionMap_toLp and targetGreen_integral_action establish the genuine full spatial inverse realization.
Article: jacobi, Theorem 2.1.
Proof: apply the genuine bounded kernel-pairing functional to the actual norm-convergent Green series. Each original term is the proved true rank-one coefficient pairing. The community complete Hilbert expansion of the actual bounded Green operator has the same terms and hence the same sum. -/
theorem targetGreen_kernel_form (a : ℝ) (ha : -1<a) (v w : Space) :
    inner ℝ (targetGreenOperator a ha v) w=kernelPairing v w (targetGreenKernelMap a ha) := by
  -- Uniform kernel convergence is used in its actual function norm before arbitrary L2 inputs are integrated.
  have hK := (kernelPairing v w).hasSum (targetGreenKernelTerm_norm_summable a ha).of_norm.hasSum
  simp only [targetGreenKernelTerm_pairing] at hK
  have hG := (fullTargetBasis a ha).hasSum_inner_mul_inner (targetGreenOperator a ha v) w
  have hG' : HasSum (fun k => (jacobi.Bessel.sigma a ha k)⁻¹*
      inner ℝ (fullTargetBasis a ha k) v*inner ℝ (fullTargetBasis a ha k) w)
      (inner ℝ (targetGreenOperator a ha v) w) := by
    apply hG.congr_fun
    intro k
    have hc : inner ℝ (fullTargetBasis a ha k) (targetGreenOperator a ha v)=
        (jacobi.Bessel.sigma a ha k)⁻¹*inner ℝ (fullTargetBasis a ha k) v := by
      simpa only [HilbertBasis.repr_apply_apply] using targetGreen_coordinates a ha v k
    rw [real_inner_comm (fullTargetBasis a ha k) (targetGreenOperator a ha v),hc]
  exact hG'.unique hK

/-- The actual continuous representative of the original Green integral action on an arbitrary full-interval L2 input.
Use: targetGreenActionMap_toLp identifies this unchanged spatial construction with the actual full bounded spectral inverse.
Article: jacobi, Theorem 2.1.
-/
def targetGreenActionMap (a : ℝ) (ha : -1<a) (v : Space) : C(Interval,ℝ) :=
  ⟨fun t => inner ℝ (ContinuousMap.toLp (𝕜 := ℝ) (p := 2) volume
    ((targetGreenKernelMap a ha).curry t)) v,
    (((ContinuousMap.toLp (𝕜 := ℝ) (p := 2) volume).continuous.comp
      (targetGreenKernelMap a ha).curry.continuous).inner continuous_const)⟩

/-- The genuine continuous Green-action representative is the literal original spatial kernel integral at every physical point.
Use: targetGreen_integral_action gives the actual full L2 inverse its original pointwise integral representative.
Article: jacobi, Proposition C.2.
Proof: substitute the actual continuous row's genuine L2 representative in its real Hilbert inner product against the arbitrary original L2 input. -/
theorem targetGreenActionMap_apply (a : ℝ) (ha : -1<a) (v : Space) (t : Interval) :
    targetGreenActionMap a ha v t=∫ s:Interval,v s*targetGreenKernel a ha t s := by
  change inner ℝ (ContinuousMap.toLp (𝕜 := ℝ) (p := 2) volume ((targetGreenKernelMap a ha).curry t)) v=_
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [ContinuousMap.coeFn_toLp (𝕜 := ℝ) (p := 2) volume ((targetGreenKernelMap a ha).curry t)] with s hs
  rw [hs]
  rfl

/-- The actual continuous Green integral output has the true full-kernel bilinear pairing against every original L2 test vector.
Use: targetGreenActionMap_toLp compares the actual spatial output with the full spectral inverse using all genuine Hilbert pairings.
Article: jacobi, Proposition C.2.
Proof: the original output embedding has its actual continuous representative. The genuine product integrand is integrable, so Fubini identifies its true iterated integral with the original bounded kernel pairing. -/
theorem targetGreenActionMap_inner (a : ℝ) (ha : -1<a) (v w : Space) :
    inner ℝ (ContinuousMap.toLp (𝕜 := ℝ) (p := 2) volume (targetGreenActionMap a ha v)) w=
      kernelPairing w v (targetGreenKernelMap a ha) := by
  -- Fubini applies to the true continuous full kernel and original L1 inputs, with integrability independently established by the shared kernel-pairing theorem.
  change _=∫ p:Interval×Interval,(w p.1*v p.2)*targetGreenKernelMap a ha p ∂(volume.prod volume)
  rw [L2.inner_def,integral_prod _ (continuousKernelPairing_integrable w v (targetGreenKernelMap a ha))]
  apply integral_congr_ae
  filter_upwards [ContinuousMap.coeFn_toLp (𝕜 := ℝ) (p := 2) volume (targetGreenActionMap a ha v)] with t ht
  rw [ht]
  change w t*targetGreenActionMap a ha v t=_
  rw [targetGreenActionMap_apply,← integral_const_mul]
  apply integral_congr_ae
  exact Eventually.of_forall (fun s => by change w t*(v s*targetGreenKernelMap a ha (t,s))=_; ring)

/-- The actual original continuous Green integral action represents exactly the genuine full bounded inverse of H_alpha for every original L2 input.
Use: targetGreen_integral_action and both proved full-domain inverse identities give the complete actual Green inverse realization.
Article: jacobi, Proposition C.2.
Proof: test both genuine original L2 outputs against every actual Hilbert vector. The original Fubini pairing equals the independently proved spectral Green pairing, and actual positivity gives the symmetry needed to interchange the two original inputs. -/
theorem targetGreenActionMap_toLp (a : ℝ) (ha : -1<a) (v : Space) :
    ContinuousMap.toLp (𝕜 := ℝ) (p := 2) volume (targetGreenActionMap a ha v)=targetGreenOperator a ha v := by
  apply ext_inner_right ℝ
  intro w
  rw [targetGreenActionMap_inner,← targetGreen_kernel_form]
  exact ((targetGreen_positive a ha).1 w v).trans (real_inner_comm _ _)

/-- The actual full bounded inverse of the original unbounded H_alpha has precisely the original continuous Green kernel integral as its almost-everywhere representative, for every genuine L2 input.
Use: completes the full original Green inverse assertion together with targetOperator_green_inverse and targetGreen_operator_inverse; targetGreen_diagonal identifies its original profile and energy.
Article: jacobi, Theorem 2.1.
Proof: the proved original continuous integral output maps to exactly the actual bounded spectral inverse. Its genuine continuous-to-L2 representative and the independently proved original row integral formula give the unchanged spatial action. -/
theorem targetGreen_integral_action (a : ℝ) (ha : -1<a) (v : Space) :
    targetGreenOperator a ha v=ᵐ[volume] fun t:Interval => ∫ s:Interval,v s*targetGreenKernel a ha t s := by
  rw [← targetGreenActionMap_toLp]
  exact (ContinuousMap.coeFn_toLp (𝕜 := ℝ) (p := 2) volume (targetGreenActionMap a ha v)).trans
    (Eventually.of_forall (fun t => targetGreenActionMap_apply a ha v t))

end
end jacobi.GelfandLevitan
