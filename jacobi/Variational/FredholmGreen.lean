import jacobi.Variational.FredholmResolvent

/-!
Article: jacobi, Theorem D.7.
The genuine subcritical inverse defines a continuous symmetric Green kernel.
Its Neumann series proves the pointwise exponential lower bound, including
off the diagonal. The actual H1 Green representative satisfies the form
identity uniquely, and the diagonal has the printed spectral-margin bounds.
Source: the reproducing kernel of H1 and the norm-convergent Neumann series.
Use: proves positivity of the Green kernel at distinct points, not just positivity as an operator.
-/
namespace jacobi.Variational
noncomputable section
open MeasureTheory Real Filter chebyshev2.Continuum chebyshev2.Sobolev
open scoped InnerProductSpace Topology BigOperators
set_option backward.isDefEq.respectTransparency false

/-- The actual inverse is the norm-convergent positive-parameter Neumann series.
Use: proves positivity of the Green kernel at distinct points, not just positivity as an operator.
Article: jacobi, Theorem D.7.
Proof: the actual top norm bound gives norm(s*K_m)<1. Multiply the geometric
sum by the pencil and use the constructed inverse to identify its limit. -/
theorem L1Source.fredholmResolvent_hasSum (m : L1Source) {s : ℝ} (hs : 0≤s)
    (hp : s*observe m .top<1) :
    HasSum (fun n : ℕ => (s • densityOperator m.value)^n) (m.fredholmResolvent s hs hp) := by
  -- The same spectral margin controls convergence and the actual inverse.
  let T := s • densityOperator m.value
  let R := m.fredholmResolvent s hs hp
  have hT : ‖T‖<1 := by
    rw [norm_smul,Real.norm_eq_abs,abs_of_nonneg hs]
    exact (mul_le_mul_of_nonneg_left (densityOperator_norm_top m) hs).trans_lt hp
  have hsum := summable_geometric_of_norm_lt_one hT
  have hAS : m.fredholmPencil s*(∑' n : ℕ,T^n)=1 := mul_neg_geom_series T hT
  have hRA : R*m.fredholmPencil s=1 := by
    apply ContinuousLinearMap.ext
    intro u
    change m.fredholmResolvent s hs hp (m.fredholmPencil s u)=u
    exact m.resolvent_pencil hs hp u
  have he : (∑' n : ℕ,T^n)=R := by
    calc
      _ = (R*m.fredholmPencil s)*(∑' n : ℕ,T^n) := by rw [hRA,one_mul]
      _ = R*(m.fredholmPencil s*(∑' n : ℕ,T^n)) := mul_assoc _ _ _
      _ = R := by rw [hAS,mul_one]
  simpa only [he] using hsum.hasSum

/-- Nonnegative feature evaluations are preserved by every positive density-operator power.
Use: every individual term of the Green Neumann kernel is nonnegative.
Article: jacobi, Appendix D.4 (green diagonal and determinant identities).
Proof: evaluate one density operator through its actual Bochner integral,
then use the positive exponential feature inner product and induction. -/
theorem L1Source.feature_power_nonneg (m : L1Source) {s : ℝ} (hs : 0≤s)
    (n : ℕ) (x y : ℝ) :
    0 ≤ inner ℝ (feature y) (((s • densityOperator m.value)^n) (feature x)) := by
  -- Pointwise feature positivity is stronger than positivity of a quadratic form.
  induction n generalizing y with
  | zero => simp only [pow_zero,one_apply_eq_self,feature_inner]; positivity
  | succ n ih =>
    rw [pow_succ',mul_apply_eq_comp,smul_apply,
      real_inner_smul_right,densityOperator_inner m.integrable]
    apply mul_nonneg hs
    apply integral_nonneg
    intro z
    change 0 ≤ m.value z*(inner ℝ (feature z) (feature y)*
      inner ℝ (feature z) (((s • densityOperator m.value)^n) (feature x)))
    rw [feature_inner]
    exact mul_nonneg (m.nonneg z) (mul_nonneg (exp_pos _).le (ih z))

/-- The actual subcritical Green kernel in physical coordinates.
Use: its diagonal is the Fredholm first-variation gradient after removing the identity term.
Article: jacobi, Appendix D.4 (green diagonal and determinant identities).
-/
def L1Source.fredholmGreen (m : L1Source) (s : ℝ) (hs : 0≤s) (hp : s*observe m .top<1)
    (x y : ℝ) : ℝ := (1/2:ℝ)*inner ℝ (m.fredholmResolvent s hs hp (feature x)) (feature y)

/-- The genuine Green kernel is jointly continuous in both physical coordinates.
Use: its diagonal is a continuous bounded gradient in the multiplier theorem.
Article: jacobi, Appendix D.4 (green diagonal and determinant identities).
Proof: the feature map is continuous into H1 and the constructed resolvent is a bounded operator. -/
theorem L1Source.fredholmGreen_continuous (m : L1Source) {s : ℝ} (hs : 0≤s)
    (hp : s*observe m .top<1) : Continuous (fun z : ℝ × ℝ => m.fredholmGreen s hs hp z.1 z.2) := by
  unfold L1Source.fredholmGreen
  exact continuous_const.mul (((m.fredholmResolvent s hs hp).continuous.comp
    (feature_continuous.comp continuous_fst)).inner (feature_continuous.comp continuous_snd))

/-- The genuine Green kernel is symmetric in its two physical arguments.
Use: identifies its inverse-form representative with either Green variable.
Article: jacobi, Appendix D.4 (green first integral and optimizer geometry).
Proof: use the actual inverse's symmetry and the real inner-product symmetry. -/
theorem L1Source.fredholmGreen_symm (m : L1Source) {s : ℝ} (hs : 0≤s)
    (hp : s*observe m .top<1) (x y : ℝ) :
    m.fredholmGreen s hs hp x y=m.fredholmGreen s hs hp y x := by
  unfold L1Source.fredholmGreen
  congr 1
  exact ((m.fredholmResolvent_symmetric hs hp) (feature x) (feature y)).trans (real_inner_comm _ _)

/-- The free exponential Green kernel is a pointwise lower bound, including away from the diagonal.
Use: supplies strict positivity for Green solutions and the lower diagonal bound.
Article: jacobi, Appendix D.4 (green first integral and optimizer geometry).
Proof: apply feature evaluation to the actual Neumann series; all terms are
nonnegative, and its zeroth term is the free exponential kernel. -/
theorem L1Source.fredholmGreen_lower (m : L1Source) {s : ℝ} (hs : 0≤s)
    (hp : s*observe m .top<1) (x y : ℝ) :
    exp (-|x-y|)≤2*m.fredholmGreen s hs hp x y := by
  -- Applying two continuous linear maps preserves the norm-convergent series.
  have hv := (ContinuousLinearMap.apply ℝ FeatureSpace (feature x)).hasSum
    (m.fredholmResolvent_hasSum hs hp)
  have hi := (innerSL ℝ (feature y)).hasSum hv
  change HasSum (fun n : ℕ => inner ℝ (feature y)
    (((s • densityOperator m.value)^n) (feature x)))
    (inner ℝ (feature y) (m.fredholmResolvent s hs hp (feature x))) at hi
  have hn (n : ℕ) : 0 ≤ inner ℝ (feature y) (((s • densityOperator m.value)^n) (feature x)) :=
    m.feature_power_nonneg hs n x y
  have hb := hi.summable.le_tsum 0 (fun n _ => hn n)
  rw [hi.tsum_eq] at hb
  simp only [pow_zero,one_apply_eq_self,feature_inner] at hb
  unfold L1Source.fredholmGreen
  rw [real_inner_comm (m.fredholmResolvent s hs hp (feature x)),abs_sub_comm y x] at hb
  linarith

/-- The actual Green diagonal has exactly the article's lower and upper spectral-margin bounds.
Use: bounds s*(2g-1), the Fredholm gradient, on the entire real line.
Article: jacobi, Appendix D.4 (green diagonal and determinant identities).
Proof: use the pointwise free-kernel lower bound and the sharp inverse norm bound on unit features. -/
theorem L1Source.fredholmGreen_diagonal (m : L1Source) {s : ℝ} (hs : 0≤s)
    (hp : s*observe m .top<1) (x : ℝ) :
    (1/2:ℝ)≤m.fredholmGreen s hs hp x x ∧
      m.fredholmGreen s hs hp x x≤1/(2*(1-s*observe m .top)) := by
  -- The free kernel gives the lower endpoint; unit feature norms give the sharp upper endpoint.
  have hl := m.fredholmGreen_lower hs hp x x
  simp only [sub_self,abs_zero,neg_zero,exp_zero] at hl
  have hu : inner ℝ (m.fredholmResolvent s hs hp (feature x)) (feature x)≤
      (1-s*observe m .top)⁻¹ := by
    calc
      _ ≤ ‖m.fredholmResolvent s hs hp (feature x)‖*‖feature x‖ := real_inner_le_norm _ _
      _ ≤ ‖m.fredholmResolvent s hs hp‖ := by
        simpa only [feature_norm,mul_one] using (m.fredholmResolvent s hs hp).le_opNorm (feature x)
      _ ≤ _ := m.fredholmResolvent_norm hs hp
  constructor
  · linarith
  · unfold L1Source.fredholmGreen
    calc
      _ ≤ (1/2:ℝ)*(1-s*observe m .top)⁻¹ := mul_le_mul_of_nonneg_left hu (by norm_num)
      _ = _ := by field_simp

/-- The actual weak Green vector obtained by inverting point evaluation in H1.
Use: proves that the displayed kernel is the unique Green function of the article's differential form.
Article: jacobi, Appendix D.4 (green diagonal and determinant identities).
-/
def L1Source.fredholmGreenVector (m : L1Source) (s : ℝ) (hs : 0≤s)
    (hp : s*observe m .top<1) (x : ℝ) : H1 :=
  m.fredholmResolvent s hs hp (H1.k x)

/-- The weak Green vector represents exactly the previously defined physical Green kernel.
Use: the variational Green identity concerns the displayed G(x,y), not an auxiliary kernel.
Article: jacobi, Appendix D.4 (green diagonal and determinant identities).
Proof: apply H1's reproducing identity and cancel the two factors 1/sqrt(2). -/
theorem L1Source.fredholmGreenVector_rep (m : L1Source) {s : ℝ} (hs : 0≤s)
    (hp : s*observe m .top<1) (x y : ℝ) :
    H1.rep (m.fredholmGreenVector s hs hp x) y=m.fredholmGreen s hs hp x y := by
  -- Reproducing point evaluation introduces exactly two reciprocal square-root factors.
  rw [← H1.reproducing]
  unfold L1Source.fredholmGreenVector L1Source.fredholmGreen H1.k
  rw [map_smul,real_inner_smul_left,real_inner_smul_right,
    real_inner_comm (m.fredholmResolvent s hs hp (feature x))]
  have he : (sqrt 2)⁻¹*((sqrt 2)⁻¹)= (1/2:ℝ) := by
    rw [← mul_inv,← pow_two,Real.sq_sqrt (by norm_num : (0:ℝ)≤2)]
    norm_num
  rw [← mul_assoc,he]

/-- The feature pencil is exactly the weak differential form with potential 1-2s*m.
Use: identifies the constructed inverse with the actual Schrödinger Green operator.
Article: jacobi, Appendix D.4 (green diagonal and determinant identities).
Proof: H1's proved inner energy identity and the actual density-operator form give the three terms. -/
theorem L1Source.fredholmPencil_form (m : L1Source) (s : ℝ) (u w : H1) :
    inner ℝ (m.fredholmPencil s u) w=
      (∫ x,H1.slope u x*H1.slope w x)+(∫ x,H1.rep u x*H1.rep w x)-
        2*s*(∫ x,m.value x*H1.rep u x*H1.rep w x) := by
  -- The actual H1 inner product already includes both derivative and value energies.
  change inner ℝ (u-s • densityOperator m.value u) w=_
  rw [inner_sub_left,real_inner_smul_left,H1.inner_energy,
    real_inner_comm w (densityOperator m.value u),sobolevDensityOperator_form m.integrable]
  have he : (fun x => m.value x*H1.rep w x*H1.rep u x)=
      fun x => m.value x*H1.rep u x*H1.rep w x := by funext x; ring
  rw [he]
  ring

/-- The actual Green representative solves the differential form equation for every H1 test vector.
Use: establishes the article's Green inverse identity on the full form domain.
Article: jacobi, Appendix D.4 (green diagonal and determinant identities).
Proof: the pencil cancels its actual inverse, leaving the reproducing vector k_x. -/
theorem L1Source.fredholmGreen_identity (m : L1Source) {s : ℝ} (hs : 0≤s)
    (hp : s*observe m .top<1) (x : ℝ) (w : H1) :
    inner ℝ (m.fredholmPencil s (m.fredholmGreenVector s hs hp x)) w=H1.rep w x := by
  rw [L1Source.fredholmGreenVector,m.pencil_resolvent hs hp,H1.reproducing]

/-- The Green form solution is unique on the actual H1 domain.
Use: completes identification of G as the Green kernel of the coercive differential operator.
Article: jacobi, Appendix D.4 (green diagonal and determinant identities).
Proof: equality against every test vector identifies the two pencil images;
the actual two-sided inverse then identifies the vectors themselves. -/
theorem L1Source.fredholmGreen_unique (m : L1Source) {s : ℝ} (hs : 0≤s)
    (hp : s*observe m .top<1) (x : ℝ) (u : H1)
    (hu : ∀ w : H1,inner ℝ (m.fredholmPencil s u) w=H1.rep w x) :
    u=m.fredholmGreenVector s hs hp x := by
  -- Testing all H1 vectors determines the pencil image before its inverse is applied.
  have he : m.fredholmPencil s u=H1.k x := by
    apply ext_inner_right ℝ
    intro w
    rw [hu w,H1.reproducing]
  have h := congrArg (m.fredholmResolvent s hs hp) he
  simpa only [m.resolvent_pencil hs hp,L1Source.fredholmGreenVector] using h

end
end jacobi.Variational
