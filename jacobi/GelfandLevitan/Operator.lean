import jacobi.GelfandLevitan.OperatorBounds

/-!
Article: jacobi, Appendix C.2 (uniform GL coercivity).
The original continuous source kernel is realized by the norm-convergent
series of its actual compact symmetric Hilbert corrections. Its genuine
quadratic integral is exactly the operator's quadratic form. The actual
identity-plus-kernel operator is positive and injective; uniform
coercivity is the subsequent compact Fredholm argument.
Use: compactness, actual quadratic identity and injectivity lead to the source uniform coercivity and the true GL inverse.
-/
namespace jacobi.GelfandLevitan
noncomputable section
open Real Set MeasureTheory Filter jacobi.Reference
open scoped Topology InnerProductSpace
set_option backward.isDefEq.respectTransparency false

/-- The genuine original GL kernel operator on the actual closed half-interval Hilbert domain.
Use: compactness, actual quadratic identity and injectivity lead to the source uniform coercivity and the true GL inverse.
Article: jacobi, Appendix C.2 (uniform GL coercivity).
-/
def kernelOperator (a : ℝ) (ha : -1<a) : halfSubspace →L[ℝ] halfSubspace :=
  ∑' k,rankCorrection a ha k

/-- The original kernel operator is the actual norm limit of its genuine natural finite-rank partial sums.
Use: supplies real compactness of the original source operator and the exact continuous pairing limits used in its quadratic identity.
Article: jacobi, Appendix C.2 (uniform GL coercivity).
Proof: the proved summability of the true original corrections in operator norm gives convergence of their natural partial sums to their actual sum. -/
theorem kernelOperator_limit (a : ℝ) (ha : -1<a) :
    Tendsto (fun N:ℕ => ∑ k∈Finset.range N,rankCorrection a ha k) atTop (𝓝 (kernelOperator a ha)) :=
  (rankCorrection_summable a ha).hasSum.tendsto_sum_nat

/-- The actual original GL kernel operator is compact on the genuine half-interval Hilbert space.
Use: the source Fredholm alternative upgrades the proved genuine strict positivity to uniform coercivity and a true bounded inverse.
Article: jacobi, Appendix C.2 (uniform GL coercivity).
Proof: every actual natural partial sum belongs to the community
submodule of compact operators. That submodule is closed in operator
norm on the actual complete Hilbert space. Its genuine norm limit,
the original kernel operator, is therefore compact as well. -/
theorem kernelOperator_compact (a : ℝ) (ha : -1<a) : IsCompactOperator (kernelOperator a ha) := by
  -- Compactness is obtained from actual norm convergence of the original source corrections.
  let S : Submodule ℝ (halfSubspace →L[ℝ] halfSubspace) :=
    compactOperator (RingHom.id ℝ) halfSubspace halfSubspace
  have hS : IsClosed (S : Set (halfSubspace →L[ℝ] halfSubspace)) := isClosed_setOfPred_isCompactOperator
  have hmem (N : ℕ) : (∑ k∈Finset.range N,rankCorrection a ha k)∈S :=
    S.sum_mem (fun k _ => rankCorrection_compact a ha k)
  exact hS.mem_of_tendsto (kernelOperator_limit a ha) (Eventually.of_forall hmem)

/-- Every true Hilbert pairing of the original kernel operator is the actual convergent sum of its genuine original correction pairings.
Use: proves actual operator symmetry and identifies its original integral quadratic form without assuming an operator representation.
Article: jacobi, Appendix C.2 (uniform GL coercivity).
Proof: evaluation at the actual input is a community continuous linear
map on operators, and inner pairing with a fixed genuine Hilbert vector
is continuous linear over the reals. Apply their composition to the
proved actual operator-norm series, then use real inner symmetry. -/
theorem kernelOperator_inner_hasSum (a : ℝ) (ha : -1<a) (v w : halfSubspace) :
    HasSum (fun k => inner ℝ (rankCorrection a ha k v) w) (inner ℝ (kernelOperator a ha v) w) := by
  -- Both evaluation and pairing are continuous on the actual operator and original Hilbert spaces.
  let L : (halfSubspace →L[ℝ] halfSubspace) →L[ℝ] ℝ :=
    (innerSL ℝ w).comp (ContinuousLinearMap.apply ℝ halfSubspace v)
  have hh := L.hasSum (rankCorrection_summable a ha).hasSum
  have hs : HasSum (fun k => inner ℝ w (rankCorrection a ha k v)) (inner ℝ w (kernelOperator a ha v)) := hh
  have he : inner ℝ w (kernelOperator a ha v)=inner ℝ (kernelOperator a ha v) w := real_inner_comm _ _
  rw [he] at hs
  exact hs.congr_fun (fun k => real_inner_comm _ _)

/-- The actual original GL kernel operator is symmetric on the true half-interval Hilbert domain.
Use: the actual compact spectral theorem and Fredholm argument apply to the genuine source operator in uniform coercivity.
Article: jacobi, Appendix C.2 (uniform GL coercivity).
Proof: the genuine correction pairings have the proved true operator
sum. Every original correction is symmetric. The two actual convergent
scalar sums therefore agree, and real inner symmetry gives the exact
operator symmetry identity. -/
theorem kernelOperator_symmetric (a : ℝ) (ha : -1<a) : (kernelOperator a ha).IsSymmetric := by
  intro v w
  change inner ℝ (kernelOperator a ha v) w=inner ℝ v (kernelOperator a ha w)
  have hs := kernelOperator_inner_hasSum a ha w v
  have he (k : ℕ) : inner ℝ (rankCorrection a ha k v) w=inner ℝ (rankCorrection a ha k w) v :=
    (rankCorrection_symmetric a ha k v w).trans (real_inner_comm _ _)
  have hh := (kernelOperator_inner_hasSum a ha v w).unique (hs.congr_fun he)
  exact hh.trans (real_inner_comm _ _)

/-- The genuine original GL kernel operator has exactly the actual original double-integral quadratic form.
Use: transfers the original positive coefficient identity and true injectivity to the actual compact Hilbert operator required by Fredholm theory.
Article: jacobi, Appendix C.2 (uniform GL coercivity).
Proof: the genuine operator pairing series converges to the true
operator form. Its actual original coefficient series was independently
proved to converge to the literal original kernel double integral.
The exact actual rank-one identities identify their terms; uniqueness
of genuine sums gives the asserted equality. -/
theorem kernelOperator_quadratic (a : ℝ) (ha : -1<a) (v : halfSubspace) :
    inner ℝ (kernelOperator a ha v) v=kernelQuadratic a ha (v:Space) := by
  have hs := kernel_quadratic_hasSum a ha (v:Space)
  have he (k : ℕ) : inner ℝ (rankCorrection a ha k v) v=
      (normingRatio a ha k*(realCoefficient a (v:Space) (jacobi.Bessel.sigma a ha k))^2-
        (realCoefficient a (v:Space) (eigenvalue a k))^2)/norming a k := by
    rw [rankCorrection_inner]
    ring
  exact (kernelOperator_inner_hasSum a ha v v).unique (hs.congr_fun he)

/-- The actual identity-plus-original-kernel Hilbert operator.
Use: its true positivity, injectivity and compact perturbation structure supply the original GL inverse and uniform coercivity.
Article: jacobi, Appendix C.2 (uniform GL coercivity).
-/
def positiveOperator (a : ℝ) (ha : -1<a) : halfSubspace →L[ℝ] halfSubspace :=
  ContinuousLinearMap.id ℝ halfSubspace+kernelOperator a ha

/-- The actual identity-plus-F operator has exactly the genuine original source quadratic form.
Use: applies all already proved actual positive spectral and coefficient-injectivity statements to the genuine original Hilbert operator.
Article: jacobi, Appendix C.2 (uniform GL coercivity).
Proof: expand the actual identity and genuine kernel operator pairing. The identity contributes the original norm square; the original kernel pairing is its already proved true double integral. -/
theorem positiveOperator_quadratic (a : ℝ) (ha : -1<a) (v : halfSubspace) :
    inner ℝ (positiveOperator a ha v) v=quadratic a ha (v:Space) := by
  rw [positiveOperator,add_apply,ContinuousLinearMap.id_apply,inner_add_left,
    real_inner_self_eq_norm_sq,kernelOperator_quadratic]
  rfl

/-- The genuine original identity-plus-F Hilbert operator is injective on the actual full half-interval domain.
Use: excludes the original eigenvalue minus one of the actual compact F operator in the source Fredholm coercivity proof.
Article: jacobi, Appendix C.2 (uniform GL coercivity).
Proof: an actual null vector has zero true source quadratic form.
The fully proved actual Bessel coefficient uniqueness argument makes
that original input zero. Triviality of the true linear kernel then
gives injectivity of the actual Hilbert operator. -/
theorem positiveOperator_injective (a : ℝ) (ha : -1<a) : Function.Injective (positiveOperator a ha) := by
  -- Compare two genuine inputs by their actual difference; the proved source null-form uniqueness applies to that same original L2 vector.
  intro v w hvw
  have hz : positiveOperator a ha (v-w)=0 := by rw [map_sub,hvw,sub_self]
  have hq : quadratic a ha ((v-w:halfSubspace):Space)=0 := by
    rw [← positiveOperator_quadratic,hz,inner_zero_left]
  have he : v-w=0 := Subtype.ext
    (quadratic_eq_zero_imp a ha ((v-w:halfSubspace):Space) (halfSubspace_supported (v-w)) hq)
  exact sub_eq_zero.mp he

end
end jacobi.GelfandLevitan
