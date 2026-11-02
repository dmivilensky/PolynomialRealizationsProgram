import jacobi.GelfandLevitan.Positivity
import jacobi.Reference.HalfSpace
import chebyshev2.Continuum.CompactOperator

/-!
Article: jacobi, Proposition C.2.
The actual coefficient integrals are represented by genuine vectors
in the original closed half-interval Hilbert domain. Each original
GL summand is a symmetric compact rank-two correction there.
The earlier article's rank-one compactness theorem and the community
orthogonal projection are reused for the actual source functions.
Use: projection to the genuine half-supported subspace represents exactly the original coefficient integral on that domain.
-/
namespace jacobi.GelfandLevitan
noncomputable section
open Real Set MeasureTheory jacobi.Reference
open scoped Topology InnerProductSpace
attribute [local instance] Measure.Subtype.measureSpace
set_option backward.isDefEq.respectTransparency false

/-- The actual original real reference solution as a genuine vector of the shared full Lebesgue L2 space.
Use: projection to the genuine half-supported subspace represents exactly the original coefficient integral on that domain.
Article: jacobi, Proposition C.2.
-/
def fullCoefficientVector (a : ℝ) (ha : -1<a) (E : ℝ) : Space :=
  ContinuousMap.toLp (𝕜 := ℝ) (p := 2) volume (realHalfWave a ha E)

/-- The original continuous physical real solution is the genuine almost-everywhere representative of its actual full L2 vector.
Use: identifies the Hilbert inner product with the literal original spatial coefficient integral.
Article: jacobi, Proposition C.2.
Proof: use the community continuous-function-to-Lp representative theorem on the genuine original measure. -/
theorem fullCoefficientVector_ae (a : ℝ) (ha : -1<a) (E : ℝ) :
    fullCoefficientVector a ha E=ᵐ[volume] (fun t:Interval => realSolution a E (halfTime t)) :=
  ContinuousMap.coeFn_toLp volume (realHalfWave a ha E)

/-- The true full-space coefficient vector pairs with every original L2 input to give its literal original coefficient integral.
Use: the orthogonally projected actual half-space vector represents the source functional without any sampling or completeness premise.
Article: jacobi, Proposition C.2.
Proof: the actual L2 inner product is its original integral. Replace
the genuine coefficient vector by its proved continuous representative
almost everywhere; the resulting integrand is exactly the source one. -/
theorem fullCoefficientVector_inner (a : ℝ) (ha : -1<a) (E : ℝ) (v : Space) :
    inner ℝ (fullCoefficientVector a ha E) v=realCoefficient a v E := by
  rw [L2.inner_def]
  unfold realCoefficient
  apply integral_congr_ae
  filter_upwards [fullCoefficientVector_ae a ha E] with t ht
  rw [ht]
  rfl

/-- The genuine half-interval Hilbert vector representing the actual source coefficient integral at energy E.
Use: the original GL operator summands are compact rank-one combinations of these actual projected physical waves.
Article: jacobi, Proposition C.2.
-/
def coefficientVector (a : ℝ) (ha : -1<a) (E : ℝ) : halfSubspace :=
  halfSubspace.orthogonalProjectionOnto (fullCoefficientVector a ha E)

/-- The actual half-interval coefficient vector represents exactly the original source integral on every genuine half-domain vector.
Use: evaluates the genuine compact GL rank-one summands by the already proved original spectral coefficients.
Article: jacobi, Appendix C.2 (uniform GL coercivity).
Proof: the community orthogonal projection preserves pairing with
every vector of the actual closed half-supported domain. Its full
pairing was proved to equal the literal source integral. -/
theorem coefficientVector_inner (a : ℝ) (ha : -1<a) (E : ℝ) (v : halfSubspace) :
    inner ℝ (coefficientVector a ha E) v=realCoefficient a (v:Space) E := by
  rw [coefficientVector,halfSubspace.inner_orthogonalProjectionOnto_eq_of_mem_right]
  exact fullCoefficientVector_inner a ha E (v:Space)

/-- The genuine compact Hilbert operator corresponding to the original k-th source GL kernel correction.
Use: its norm-convergent original series realizes the actual continuous GL kernel operator needed in uniform coercivity.
Article: jacobi, Appendix C.2 (uniform GL coercivity).
-/
def rankCorrection (a : ℝ) (ha : -1<a) (k : ℕ) : halfSubspace →L[ℝ] halfSubspace :=
  (normingRatio a ha k/norming a k) • InnerProductSpace.rankOne ℝ
    (coefficientVector a ha (jacobi.Bessel.sigma a ha k)) (coefficientVector a ha (jacobi.Bessel.sigma a ha k))-
  (1/norming a k) • InnerProductSpace.rankOne ℝ
    (coefficientVector a ha (eigenvalue a k)) (coefficientVector a ha (eigenvalue a k))

/-- Every genuine original Hilbert GL correction has exactly its actual source coefficient bilinear form.
Use: identifies the genuine operator series with the original kernel integrals and proves actual symmetry before compactness and coercivity.
Article: jacobi, Appendix C.2 (uniform GL coercivity).
Proof: evaluate the two actual rank-one maps, take the true real
Hilbert inner product, and identify every genuine coefficient-vector
pairing with the previously proved literal source coefficient integral. -/
theorem rankCorrection_inner (a : ℝ) (ha : -1<a) (k : ℕ) (v w : halfSubspace) :
    inner ℝ (rankCorrection a ha k v) w=
      (normingRatio a ha k*realCoefficient a (v:Space) (jacobi.Bessel.sigma a ha k)*
        realCoefficient a (w:Space) (jacobi.Bessel.sigma a ha k)-
        realCoefficient a (v:Space) (eigenvalue a k)*realCoefficient a (w:Space) (eigenvalue a k))/norming a k := by
  -- Combine the genuine nested scalar actions before applying the actual half-space inner-product scaling law.
  simp only [rankCorrection,sub_apply,smul_apply,InnerProductSpace.rankOne_apply,
    inner_sub_left,coefficientVector_inner,smul_smul]
  rw [real_inner_smul_left (coefficientVector a ha (jacobi.Bessel.sigma a ha k)) w
      ((normingRatio a ha k/norming a k)*realCoefficient a (v:Space) (jacobi.Bessel.sigma a ha k)),
    real_inner_smul_left (coefficientVector a ha (eigenvalue a k)) w
      ((1/norming a k)*realCoefficient a (v:Space) (eigenvalue a k))]
  rw [coefficientVector_inner,coefficientVector_inner]
  ring

/-- Every original actual GL Hilbert correction is symmetric on the genuine half-interval domain.
Use: the actual norm-convergent operator series is self-adjoint before the source compact Fredholm argument.
Article: jacobi, Appendix C.2 (uniform GL coercivity).
Proof: the exact original coefficient bilinear form is symmetric, since its source scalar factors commute. -/
theorem rankCorrection_symmetric (a : ℝ) (ha : -1<a) (k : ℕ) :
    (rankCorrection a ha k).IsSymmetric := by
  intro v w
  change inner ℝ (rankCorrection a ha k v) w=inner ℝ v (rankCorrection a ha k w)
  have hc : inner ℝ v (rankCorrection a ha k w)=inner ℝ (rankCorrection a ha k w) v :=
    real_inner_comm _ _
  rw [hc,rankCorrection_inner,rankCorrection_inner]
  ring

/-- Each actual original GL Hilbert correction is compact, including every genuine finite-prefix index.
Use: the norm-convergent source correction series defines an actual compact symmetric kernel operator for the GL coercivity theorem.
Article: jacobi, Appendix C.2 (uniform GL coercivity).
Proof: reuse the earlier article's genuine rank-one compactness theorem; compact operators are closed under scalar multiplication and subtraction. -/
theorem rankCorrection_compact (a : ℝ) (ha : -1<a) (k : ℕ) : IsCompactOperator (rankCorrection a ha k) :=
  ((chebyshev2.Continuum.rankOne_isCompact _ _).smul _).sub
    ((chebyshev2.Continuum.rankOne_isCompact _ _).smul _)

end
end jacobi.GelfandLevitan
