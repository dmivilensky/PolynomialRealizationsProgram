import jacobi.Variational.FredholmGradient

/-!
Article: jacobi, Appendix D.1 (infinite-dimensional Klein inequality and Fredholm variation).
Exact resolvent perturbation for the actual density operators, with the
sharp spectral-margin norm bound. The derivative operator and the continuous
Green-diagonal gradient are Lipschitz in the actual L1 density distance.
Source: the two-sided inverse identities and signed feature-operator linearity.
Use: the resolvent identity uses K_(q-m), whose operator norm is bounded by the actual L1 distance.
-/
namespace jacobi.Variational
noncomputable section
open MeasureTheory Real chebyshev2.Continuum
open scoped InnerProductSpace
set_option backward.isDefEq.respectTransparency false

/-- Differences of the two actual Fredholm pencils equal the signed density perturbation.
Use: the resolvent identity uses K_(q-m), whose operator norm is bounded by the actual L1 distance.
Article: jacobi, Appendix D.1 (infinite-dimensional Klein inequality and Fredholm variation).
Proof: distribute the scalar and reuse the already proved signed density-operator linearity. -/
theorem fredholmPencil_sub (m q : L1Source) (s : ℝ) :
    m.fredholmPencil s-q.fredholmPencil s=s • densityOperator (q.value-m.value) := by
  rw [densityOperator_sub q.integrable m.integrable,smul_sub]
  unfold L1Source.fredholmPencil
  abel

/-- The actual two subcritical Fredholm resolvents obey the exact resolvent identity.
Use: bounds derivative-operator differences and the operator second-order remainder.
Article: jacobi, Appendix D.1 (infinite-dimensional Klein inequality and Fredholm variation).
Proof: insert both pencil inverses, factor their difference, and identify the signed density operator. -/
theorem fredholmResolvent_sub (m q : L1Source) {s : ℝ} (hs : 0≤s)
    (hm : s*observe m .top<1) (hq : s*observe q .top<1) :
    q.fredholmResolvent s hs hq-m.fredholmResolvent s hs hm=
      s • (q.fredholmResolvent s hs hq ∘L densityOperator (q.value-m.value) ∘L
        m.fredholmResolvent s hs hm) := by
  -- Algebra is performed with the actual bounded inverses, without a commutativity assumption.
  let R := m.fredholmResolvent s hs hm
  let Q := q.fredholmResolvent s hs hq
  have hAR : m.fredholmPencil s*R=1 := by
    apply ContinuousLinearMap.ext
    intro u
    exact m.pencil_resolvent hs hm u
  have hQA : Q*q.fredholmPencil s=1 := by
    apply ContinuousLinearMap.ext
    intro u
    exact q.resolvent_pencil hs hq u
  change Q-R=s • (Q ∘L densityOperator (q.value-m.value) ∘L R)
  calc
    Q-R = Q*(m.fredholmPencil s*R)-(Q*q.fredholmPencil s)*R := by rw [hAR,hQA,mul_one,one_mul]
    _ = Q*(m.fredholmPencil s-q.fredholmPencil s)*R := by
      rw [mul_sub,sub_mul]
      simp only [mul_assoc]
    _ = _ := by
      rw [fredholmPencil_sub]
      simp only [mul_smul_comm]
      rfl

/-- Resolvent differences have the sharp product-of-margins L1 bound.
Use: supplies the quantitative operator estimate behind the quadratic Fredholm variation.
Article: jacobi, Appendix D.1 (infinite-dimensional Klein inequality and Fredholm variation).
Proof: apply the exact resolvent identity, submultiplicativity, both proved
inverse norm bounds and the actual signed feature-operator L1 norm bound. -/
theorem fredholmResolvent_distance (m q : L1Source) {s : ℝ} (hs : 0≤s)
    (hm : s*observe m .top<1) (hq : s*observe q .top<1) :
    ‖q.fredholmResolvent s hs hq-m.fredholmResolvent s hs hm‖≤
      s*(∫ x,|q.value x-m.value x|)/((1-s*observe q .top)*(1-s*observe m .top)) := by
  -- Each inverse is controlled by its own actual spectral gap to the pole.
  rw [fredholmResolvent_sub m q hs hm hq,norm_smul,Real.norm_eq_abs,abs_of_nonneg hs]
  have hB : ‖densityOperator (q.value-m.value)‖≤∫ x,|q.value x-m.value x| := by
    simpa only [Pi.sub_apply] using densityOperator_norm (q.value-m.value)
  have hcq : 0≤(1-s*observe q .top)⁻¹ := inv_nonneg.mpr (sub_pos.mpr hq).le
  have hL : 0≤∫ x,|q.value x-m.value x| := integral_nonneg fun _ => abs_nonneg _
  have hb : ‖q.fredholmResolvent s hs hq‖*‖densityOperator (q.value-m.value)‖≤
      (1-s*observe q .top)⁻¹*(∫ x,|q.value x-m.value x|) :=
    mul_le_mul (q.fredholmResolvent_norm hs hq) hB (norm_nonneg _) hcq
  have ht : (‖q.fredholmResolvent s hs hq‖*‖densityOperator (q.value-m.value)‖)*
      ‖m.fredholmResolvent s hs hm‖≤
      ((1-s*observe q .top)⁻¹*(∫ x,|q.value x-m.value x|))*(1-s*observe m .top)⁻¹ :=
    mul_le_mul hb (m.fredholmResolvent_norm hs hm) (norm_nonneg _) (mul_nonneg hcq hL)
  have hnorm : ‖q.fredholmResolvent s hs hq ∘L densityOperator (q.value-m.value) ∘L
      m.fredholmResolvent s hs hm‖≤
      (‖q.fredholmResolvent s hs hq‖*‖densityOperator (q.value-m.value)‖)*
        ‖m.fredholmResolvent s hs hm‖ := by
    have h1 := ContinuousLinearMap.opNorm_comp_le (q.fredholmResolvent s hs hq)
      (densityOperator (q.value-m.value) ∘L m.fredholmResolvent s hs hm)
    have h2 := mul_le_mul_of_nonneg_left
      (ContinuousLinearMap.opNorm_comp_le (densityOperator (q.value-m.value))
        (m.fredholmResolvent s hs hm)) (norm_nonneg (q.fredholmResolvent s hs hq))
    exact (h1.trans h2).trans_eq (by ring)
  exact (mul_le_mul_of_nonneg_left (hnorm.trans ht) hs).trans_eq (by
    rw [div_eq_mul_inv,mul_inv]
    ring)

/-- The actual bounded Fredholm derivative operator has its printed resolvent modulus.
Use: its nuclear pairing with K_delta yields the quadratic determinant remainder after the trace inequalities.
Article: jacobi, Appendix D.1 (infinite-dimensional Klein inequality and Fredholm variation).
Proof: the identity terms cancel, leaving s times the actual resolvent difference. -/
theorem fredholmDerivativeOperator_distance (m q : L1Source) {s : ℝ} (hs : 0≤s)
    (hm : s*observe m .top<1) (hq : s*observe q .top<1) :
    ‖q.fredholmDerivativeOperator s hs hq-m.fredholmDerivativeOperator s hs hm‖≤
      s^2*(∫ x,|q.value x-m.value x|)/((1-s*observe q .top)*(1-s*observe m .top)) := by
  have he : q.fredholmDerivativeOperator s hs hq-m.fredholmDerivativeOperator s hs hm=
      s • (q.fredholmResolvent s hs hq-m.fredholmResolvent s hs hm) := by
    unfold L1Source.fredholmDerivativeOperator
    rw [smul_sub]
    abel
  rw [he,norm_smul,Real.norm_eq_abs,abs_of_nonneg hs]
  exact (mul_le_mul_of_nonneg_left (fredholmResolvent_distance m q hs hm hq) hs).trans_eq (by ring)

/-- The genuine Green-diagonal gradient has the same uniform L1 perturbation bound.
Use: provides the operator-to-pointwise step for Fredholm differential and multiplier estimates.
Article: jacobi, Appendix D.1 (infinite-dimensional Klein inequality and Fredholm variation).
Proof: evaluate the derivative-operator difference on a unit feature and use its proved norm bound. -/
theorem fredholmGradient_distance (m q : L1Source) {s : ℝ} (hs : 0≤s)
    (hm : s*observe m .top<1) (hq : s*observe q .top<1) (x : ℝ) :
    |q.fredholmGradient s hs hq x-m.fredholmGradient s hs hm x|≤
      s^2*(∫ y,|q.value y-m.value y|)/((1-s*observe q .top)*(1-s*observe m .top)) := by
  -- Feature evaluation has norm one, so no additional spatial factor is introduced.
  rw [← q.fredholmDerivativeOperator_feature hs hq,← m.fredholmDerivativeOperator_feature hs hm,
    ← inner_sub_left]
  let A := q.fredholmDerivativeOperator s hs hq-m.fredholmDerivativeOperator s hs hm
  change |inner ℝ (A (feature x)) (feature x)|≤_
  calc
    _ ≤ ‖A (feature x)‖*‖feature x‖ := abs_real_inner_le_norm _ _
    _ ≤ ‖A‖ := by simpa only [feature_norm,mul_one] using A.le_opNorm (feature x)
    _ ≤ _ := fredholmDerivativeOperator_distance m q hs hm hq

end
end jacobi.Variational
