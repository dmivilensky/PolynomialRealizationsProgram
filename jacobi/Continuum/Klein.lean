import chebyshev2.Continuum.TraceClassTrace
import chebyshev2.Continuum.SpectralQuadratic
import Mathlib.Analysis.Convex.Deriv

/-!
Article: jacobi, Appendix D.1 (infinite-dimensional Klein inequality and Fredholm variation).
The general double-eigenbasis argument is independent of the logarithm.
Functional-calculus operators are specified by their actual eigenvector
actions; the source's three trace-class hypotheses give all convergence.
The linear trace is written in the eigenbasis of X, exactly as in the
source proof. Its absolute convergence follows from the compact interval
bound on f' and the genuine trace-class diagonal of Z-X.
Source: Klein's trace inequality; Carlen, Trace Inequalities and Quantum Entropy.
Use: the scalar inequality inside the general double-eigenbasis Klein proof.
-/
namespace jacobi.Continuum
noncomputable section
open Real Set chebyshev2.Continuum
open scoped InnerProductSpace
set_option backward.isDefEq.respectTransparency false
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- A convex function lies above its derivative supporting line, including interval endpoints.
Use: the scalar inequality inside the general double-eigenbasis Klein proof.
Article: jacobi, Appendix D.1 (infinite-dimensional Klein inequality and Fredholm variation).
Source: the supporting-line inequality for differentiable convex functions.
Proof: compare the appropriate secant slope with the one-sided interval
 derivative; clear its positive denominator in either order of x and z. -/
theorem convex_supporting {I : Set ℝ} {f : ℝ → ℝ} (hf : ConvexOn ℝ I f)
    {x z d : ℝ} (hx : x∈I) (hz : z∈I) (hd : HasDerivWithinAt f d I x) :
    f x+d*(z-x)≤f z := by
  -- The two ordered cases also allow the endpoints of the compact spectral interval.
  rcases lt_trichotomy x z with h | h | h
  · have hh := hf.le_slope_of_hasDerivWithinAt hx hz h hd
    rw [slope_def_field] at hh
    have hh' := (le_div_iff₀ (sub_pos.mpr h)).mp hh
    linarith
  · rw [h]
    ring_nf
    exact le_rfl
  · have hh := hf.slope_le_of_hasDerivWithinAt hz hx h hd
    rw [slope_def_field] at hh
    have hh' := (div_le_iff₀ (sub_pos.mpr h)).mp hh
    nlinarith

/-- Any scalar supporting line remains valid in every genuine unit-vector spectral quadratic form.
Use: shares the double-eigenbasis averaging argument between the general Klein lemma and its Fredholm logarithm application.
Article: jacobi, Appendix D.1 (infinite-dimensional Klein inequality and Fredholm variation).
Proof: expand the actual operators Z and f(Z) in the same complete
Hilbert eigenbasis. Parseval makes the nonnegative squared coefficients
sum to one; sum the scalar supporting inequality with those coefficients. -/
theorem spectral_supporting {ι : Type*} (b : HilbertBasis ι ℝ E)
    (Z F : E →L[ℝ] E) (z : ι → ℝ) {f : ℝ → ℝ} {x d : ℝ}
    (hZ : ∀ i,Z (b i)=z i • b i) (hF : ∀ i,F (b i)=f (z i) • b i)
    (hsupport : ∀ i,f x+d*(z i-x)≤f (z i)) (v : E) (hv : ‖v‖=1) :
    f x+d*(inner ℝ v (Z v)-x)≤ inner ℝ v (F v) := by
  -- Every term is an actual quadratic form, including contributions from the kernel eigenspace.
  have hw : HasSum (fun i => (inner ℝ (b i) v)^2) 1 := by
    simpa only [hv,one_pow] using basis_hasSum_sq b v
  have hlin := (hw.mul_left (f x)).add
    (((eigenbasis_quadratic_hasSum b Z hZ v).sub (hw.mul_left x)).mul_left d)
  simp only [mul_one] at hlin
  apply hasSum_le _ hlin (eigenbasis_quadratic_hasSum b F hF v)
  intro i
  have hh := mul_le_mul_of_nonneg_right (hsupport i) (sq_nonneg (inner ℝ (b i) v))
  nlinarith

/-- A convex derivative supporting line holds in every genuine unit-vector spectral quadratic form.
Use: supplies each nonnegative diagonal remainder in the full general Klein trace theorem.
Article: jacobi, Appendix D.1 (infinite-dimensional Klein inequality and Fredholm variation).
Proof: apply the shared actual eigenbasis averaging to the proved scalar convex supporting inequality. -/
theorem convex_spectral_supporting {ι : Type*} (b : HilbertBasis ι ℝ E)
    (Z F : E →L[ℝ] E) (z : ι → ℝ) {I : Set ℝ} {f : ℝ → ℝ}
    (hZ : ∀ i,Z (b i)=z i • b i) (hF : ∀ i,F (b i)=f (z i) • b i)
    (hf : ConvexOn ℝ I f) (hz : ∀ i,z i∈I) {x d : ℝ}
    (hx : x∈I) (hd : HasDerivWithinAt f d I x) (v : E) (hv : ‖v‖=1) :
    f x+d*(inner ℝ v (Z v)-x)≤ inner ℝ v (F v) :=
  spectral_supporting b Z F z hZ hF (fun i => convex_supporting hf hx (hz i) hd) v hv

/-- General Klein trace comparison with the actual, absolutely convergent linear trace in X's eigenbasis.
Use: verifies the article's standalone convex-C1 lemma in addition to its logarithmic Fredholm specialization.
Article: jacobi, Appendix D.1 (infinite-dimensional Klein inequality and Fredholm variation).
Functional-calculus notation is spelled out by hFX and hFZ on complete
actual eigenbases. FX, FZ and delta are the three trace-class operators
in the source hypothesis; hdelta identifies delta with the original Z-X.
Proof: compactness bounds f'. The trace-class diagonal of the actual
difference makes the linear trace absolutely summable. Both functional
traces converge in X's eigenbasis. Their supporting-line remainder is
termwise nonnegative by the actual double-eigenbasis expansion, so its sum is nonnegative. -/
theorem klein_trace {ι κ : Type*} (b : HilbertBasis ι ℝ E) (c : HilbertBasis κ ℝ E)
    (X Z : E →L[ℝ] E) (x : ι → ℝ) (z : κ → ℝ)
    (hX : ∀ i,X (b i)=x i • b i) (hZ : ∀ i,Z (c i)=z i • c i)
    (FX FZ delta : TraceClassOperator E) (hdelta : delta.val=Z-X)
    {I : Set ℝ} {f fp : ℝ → ℝ} (hI : IsCompact I) (hf : ConvexOn ℝ I f)
    (hfp : ContinuousOn fp I) (hd : ∀ t∈I,HasDerivWithinAt f (fp t) I t)
    (hx : ∀ i,x i∈I) (hz : ∀ i,z i∈I)
    (hFX : ∀ i,FX.val (b i)=f (x i) • b i)
    (hFZ : ∀ i,FZ.val (c i)=f (z i) • c i) :
    Summable (fun i => |fp (x i)*inner ℝ (b i) (delta.val (b i))|) ∧
      0≤TraceClassOperator.trace b FZ-TraceClassOperator.trace b FX-
        ∑' i,fp (x i)*inner ℝ (b i) (delta.val (b i)) := by
  -- Trace-class hypotheses supply actual convergence, not a conditional identity of formal series.
  obtain ⟨C,hC⟩ := hI.exists_bound_of_continuousOn hfp
  have hD := (traceClass_diagonal_summable b delta).1
  have hlin : Summable (fun i => fp (x i)*inner ℝ (b i) (delta.val (b i))) := by
    apply Summable.of_norm_bounded (hD.mul_left C)
    intro i
    rw [norm_mul,Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_right (hC _ (hx i)) (norm_nonneg _)
  have htr (T : TraceClassOperator E) :
      HasSum (fun i => inner ℝ (b i) (T.val (b i))) (TraceClassOperator.trace b T) :=
    (traceClass_diagonal_summable b T).1.of_abs.hasSum
  have htotal := ((htr FZ).sub (htr FX)).sub hlin.hasSum
  refine ⟨hlin.abs,?_⟩
  have hn (i : ι) : 0≤(inner ℝ (b i) (FZ.val (b i))-inner ℝ (b i) (FX.val (b i)))-
      fp (x i)*inner ℝ (b i) (delta.val (b i)) := by
    have hh := convex_spectral_supporting c Z FZ.val z hZ hFZ hf hz (hx i) (hd _ (hx i))
      (b i) (b.orthonormal.norm_eq_one i)
    rw [hdelta,sub_apply,inner_sub_right,hX,hFX,
      real_inner_smul_right,real_inner_smul_right,real_inner_self_eq_norm_sq,
      b.orthonormal.norm_eq_one,one_pow,mul_one,mul_one]
    linarith
  have hnon : 0≤∑' i,((inner ℝ (b i) (FZ.val (b i))-inner ℝ (b i) (FX.val (b i)))-
      fp (x i)*inner ℝ (b i) (delta.val (b i))) := tsum_nonneg hn
  rwa [htotal.tsum_eq] at hnon

end
end jacobi.Continuum
