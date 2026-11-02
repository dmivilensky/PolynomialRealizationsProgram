import jacobi.Variational.FredholmCalculus
import jacobi.Continuum.Klein

/-!
Article: jacobi, Appendix D.1 (infinite-dimensional Klein inequality and Fredholm variation).
The scalar logarithmic supporting inequality is transferred to genuine
spectral quadratic forms and traces in the complete actual eigenbases.
This supplies the convex trace comparison used on both sides of a signed
density perturbation. No operator convexity or trace derivative is assumed.
Source: the article's double-eigenbasis proof of Klein's inequality.
Use: the diagonal comparison in the actual eigenbasis proof of Klein's inequality.
-/
namespace jacobi.Variational
noncomputable section
open MeasureTheory Real chebyshev2.Continuum
open scoped InnerProductSpace
set_option backward.isDefEq.respectTransparency false

/-- The scalar Fredholm supporting line is valid for every actual unit-vector spectral quadratic form.
Use: the diagonal comparison in the actual eigenbasis proof of Klein's inequality.
Article: jacobi, Appendix D.1 (infinite-dimensional Klein inequality and Fredholm variation).
Proof: expand the logarithmic operator and the density operator in the
same actual complete eigenbasis. Parseval makes the squared coefficients
sum to one; sum the proved scalar supporting inequality with these nonnegative weights. -/
theorem fredholmFunction_supporting (q : L1Source) {s x : ℝ} (hs : 0≤s)
    (hp : s*observe q .top<1) (hx : s*x<1) (v : FeatureSpace) (hv : ‖v‖=1) :
    fredholmLog s x+(s/(1-s*x)-s)*(inner ℝ v (densityOperator q.value v)-x)≤
      inner ℝ v (q.fredholmFunction s v) := by
  -- The shared general Klein averaging theorem applies to the actual logarithmic operators.
  let D := densitySpectralData q.integrable q.nonneg
  apply jacobi.Continuum.spectral_supporting D.basis (densityOperator q.value)
    (q.fredholmFunction s) D.eig D.equation (q.fredholmFunction_basis hs hp) ?_ v hv
  intro i
  have hmargin : s*observe q .top≤1-(1-s*observe q .top) := by linarith
  have hzi : s*D.eig i<1 := by have h := q.eigenbasis_margin hs hmargin i; linarith
  exact fredholmLog_supporting hx hzi

/-- The actual subcritical resolvent acts by the reciprocal pencil eigenvalue on every basis vector.
Use: identifies f_s'(K_m) on the same actual basis used in Klein's trace comparison.
Article: jacobi, Appendix D.1 (infinite-dimensional Klein inequality and Fredholm variation).
Proof: apply the original pencil to the candidate reciprocal multiple and
then cancel it with the already proved actual two-sided inverse. -/
theorem L1Source.fredholmResolvent_basis (m : L1Source) {s : ℝ} (hs : 0≤s)
    (hp : s*observe m .top<1) (i : (densitySpectralData m.integrable m.nonneg).Index) :
    m.fredholmResolvent s hs hp ((densitySpectralData m.integrable m.nonneg).basis i)=
      (1-s*(densitySpectralData m.integrable m.nonneg).eig i)⁻¹ •
        (densitySpectralData m.integrable m.nonneg).basis i := by
  -- The reciprocal denominator is positive by the actual top spectral margin.
  let D := densitySpectralData m.integrable m.nonneg
  let c := (1-s*D.eig i)⁻¹
  have hmargin : s*observe m .top≤1-(1-s*observe m .top) := by linarith
  have hden : 0<1-s*D.eig i := by have h := m.eigenbasis_margin hs hmargin i; linarith
  have hA : m.fredholmPencil s (c • D.basis i)=D.basis i := by
    change c • D.basis i-s • densityOperator m.value (c • D.basis i)=D.basis i
    rw [map_smul,D.equation,smul_smul,smul_smul,← sub_smul]
    have hc : c-s*c*D.eig i=1 := by dsimp only [c]; field_simp
    rw [hc,one_smul]
  have h := congrArg (m.fredholmResolvent s hs hp) hA
  rw [m.resolvent_pencil hs hp] at h
  exact h.symm

/-- The actual Fredholm derivative operator has exactly the scalar logarithmic derivative eigenvalues.
Use: identifies each linear trace term in the operator Klein inequality.
Article: jacobi, Appendix D.1 (infinite-dimensional Klein inequality and Fredholm variation).
Proof: apply the actual resolvent basis formula and collect the two scalar multiples. -/
theorem L1Source.fredholmDerivativeOperator_basis (m : L1Source) {s : ℝ} (hs : 0≤s)
    (hp : s*observe m .top<1) (i : (densitySpectralData m.integrable m.nonneg).Index) :
    m.fredholmDerivativeOperator s hs hp ((densitySpectralData m.integrable m.nonneg).basis i)=
      (s/(1-s*(densitySpectralData m.integrable m.nonneg).eig i)-s) •
        (densitySpectralData m.integrable m.nonneg).basis i := by
  let D := densitySpectralData m.integrable m.nonneg
  change s • m.fredholmResolvent s hs hp (D.basis i)-s • D.basis i=_
  rw [m.fredholmResolvent_basis hs hp,smul_smul,← sub_smul]
  congr 1

/-- The bounded Fredholm derivative operator is symmetric.
Use: moves it to the eigenbasis vector before evaluating a signed perturbation's diagonal.
Article: jacobi, Appendix D.1 (infinite-dimensional Klein inequality and Fredholm variation).
Proof: the actual resolvent and identity are symmetric, and real scalar combinations preserve symmetry. -/
theorem L1Source.fredholmDerivativeOperator_symmetric (m : L1Source) {s : ℝ} (hs : 0≤s)
    (hp : s*observe m .top<1) : (m.fredholmDerivativeOperator s hs hp).IsSymmetric :=
  ((m.fredholmResolvent_symmetric hs hp).smul (c := s) (by simp)).sub
    (LinearMap.IsSymmetric.id.smul (c := s) (by simp))

/-- The genuine nuclear derivative composition has the expected diagonal in the original actual eigenbasis.
Use: identifies Klein's linear eigenbasis term with the operator trace and its Green gradient integral.
Article: jacobi, Appendix D.1 (infinite-dimensional Klein inequality and Fredholm variation).
Proof: identify the nuclear composition's underlying operator, move the
symmetric derivative operator to the basis vector, and evaluate its actual
eigenvalue before expanding the signed density difference. -/
theorem fredholmDerivative_diagonal (m q : L1Source) {s : ℝ} (hs : 0≤s)
    (hp : s*observe m .top<1) (i : (densitySpectralData m.integrable m.nonneg).Index) :
    inner ℝ ((densitySpectralData m.integrable m.nonneg).basis i)
      ((jacobi.Continuum.composedDensity (m.fredholmDerivativeOperator s hs hp) (q.value-m.value)).val
        ((densitySpectralData m.integrable m.nonneg).basis i))=
      (s/(1-s*(densitySpectralData m.integrable m.nonneg).eig i)-s)*
        (inner ℝ ((densitySpectralData m.integrable m.nonneg).basis i)
          (densityOperator q.value ((densitySpectralData m.integrable m.nonneg).basis i))-
            (densitySpectralData m.integrable m.nonneg).eig i) := by
  -- The signed perturbation is the actual operator K_q-K_m, with no independent trace certificate.
  let D := densitySpectralData m.integrable m.nonneg
  let A := m.fredholmDerivativeOperator s hs hp
  rw [jacobi.Continuum.composedDensity_val A (q.integrable.sub m.integrable)]
  change inner ℝ (D.basis i) (A (densityOperator (q.value-m.value) (D.basis i)))=_
  have hsym : inner ℝ (A (D.basis i)) (densityOperator (q.value-m.value) (D.basis i))=
      inner ℝ (D.basis i) (A (densityOperator (q.value-m.value) (D.basis i))) :=
    (m.fredholmDerivativeOperator_symmetric hs hp) _ _
  rw [← hsym,m.fredholmDerivativeOperator_basis hs hp,real_inner_smul_left,
    densityOperator_sub q.integrable m.integrable,sub_apply,inner_sub_right,D.equation,
      real_inner_smul_right,real_inner_self_eq_norm_sq,D.basis.orthonormal.norm_eq_one,one_pow,mul_one]

/-- Klein's supporting trace inequality for the actual regularized Fredholm functional.
Use: its two orientations sandwich the actual determinant variation by the two gradient pairings.
Article: jacobi, Appendix D.1 (infinite-dimensional Klein inequality and Fredholm variation).
Proof: compare actual logarithmic quadratic forms in the complete eigenbasis
of K_m. The scalar supporting line gives a nonnegative diagonal remainder.
The genuine trace-class derivative composition and both proved functional
traces make every diagonal series summable; sum the nonnegative remainder. -/
theorem fredholm_klein (m q : L1Source) {s : ℝ} (hs : 0≤s)
    (hm : s*observe m .top<1) (hq : s*observe q .top<1) :
    0≤q.fredholmReal s-m.fredholmReal s-
      (∫ x,m.fredholmGradient s hs hm x*(q.value x-m.value x)) := by
  -- All three trace series refer to actual bounded or nuclear operators on the same Hilbert space.
  let D := densitySpectralData m.integrable m.nonneg
  let U := jacobi.Continuum.composedDensity (m.fredholmDerivativeOperator s hs hm) (q.value-m.value)
  have hqtrace := q.fredholmFunction_trace hs hq D.basis
  have hmtrace := m.fredholmFunction_trace hs hm D.basis
  have hU : HasSum (fun i => inner ℝ (D.basis i) (U.val (D.basis i)))
      (∫ x,m.fredholmGradient s hs hm x*(q.value x-m.value x)) := by
    have htrace := (m.fredholm_trace_gradient hs hm (q.integrable.sub m.integrable) D.basis).2
    change TraceClassOperator.trace D.basis U=
      (∫ x,m.fredholmGradient s hs hm x*(q.value x-m.value x)) at htrace
    rw [← htrace]
    exact (traceClass_diagonal_summable D.basis U).1.of_abs.hasSum
  have htotal := (hqtrace.sub hmtrace).sub hU
  have hn (i : D.Index) :
      0≤(inner ℝ (D.basis i) (q.fredholmFunction s (D.basis i))-
        inner ℝ (D.basis i) (m.fredholmFunction s (D.basis i)))-
          inner ℝ (D.basis i) (U.val (D.basis i)) := by
    have hmargin : s*observe m .top≤1-(1-s*observe m .top) := by linarith
    have hip : s*D.eig i<1 := by have h := m.eigenbasis_margin hs hmargin i; linarith
    have h := fredholmFunction_supporting q hs hq hip (D.basis i) (D.basis.orthonormal.norm_eq_one i)
    have hdiag : inner ℝ (D.basis i) (m.fredholmFunction s (D.basis i))=fredholmLog s (D.eig i) := by
      rw [m.fredholmFunction_basis hs hm,real_inner_smul_right,real_inner_self_eq_norm_sq,
        D.basis.orthonormal.norm_eq_one,one_pow,mul_one]
    rw [hdiag]
    change 0≤_-(inner ℝ (D.basis i)
      ((jacobi.Continuum.composedDensity (m.fredholmDerivativeOperator s hs hm) (q.value-m.value)).val
        (D.basis i)))
    rw [fredholmDerivative_diagonal m q hs hm]
    linarith
  have hsum : 0≤∑' i : D.Index,((inner ℝ (D.basis i) (q.fredholmFunction s (D.basis i))-
      inner ℝ (D.basis i) (m.fredholmFunction s (D.basis i)))-
        inner ℝ (D.basis i) (U.val (D.basis i))) := tsum_nonneg hn
  rwa [htotal.tsum_eq] at hsum

end
end jacobi.Variational
