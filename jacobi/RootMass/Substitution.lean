import jacobi.RootMass.NodeGeometry

/-!
Article: jacobi, Appendix D.5 (regularized state quadratures).
The genuine inverse curve is used in the one-dimensional Lebesgue Jacobian
theorem, not just in a formal differential identity. Cancellation of its
exact derivative and radicand proves the stated quadrature substitution.
Source: mathlib's injective one-dimensional change-of-variables theorem.
Use: connects the optimizing spatial profile to all four nonsingular printed integrals.
-/
namespace jacobi.RootMass
noncomputable section
open Real Set MeasureTheory Filter
set_option backward.isDefEq.respectTransparency false

/-- The literal turning-interval quadrature of a state observable.
Use: connects the optimizing spatial profile to all four nonsingular printed integrals.
Article: jacobi, Appendix D.5 (regularized state quadratures).
-/
def turningIntegral (a : ℝ) (ha : -2*sqrt 3<a) (y : ℝ) (F : ℝ → ℝ) : ℝ :=
  ∫ n in Ioo (1:ℝ) (inverse a ha y),F n*(3*n^2-1)/(n*sqrt (radicand a y n))

/-- The absolute derivative of the actual inverse curve cancels the true turning singularity exactly.
Use: the actual Lebesgue change of variables yields the printed nonsingular state integrals.
Article: jacobi, Appendix D.5 (regularized state quadratures).
Proof: the actual radicand is p(n_u)²*u². Its positive square root is p(n_u)*u;
the proved rational formula for psi' then cancels, with all denominators positive. -/
theorem node_jacobian {a y u : ℝ} (ha : -2*sqrt 3<a) (hy : 0<y) (hu : u∈Ioo (0:ℝ) 1)
    (F : ℝ → ℝ) :
    |(-2*y*u/psiSlope a (node a ha y u))| *
      (F (node a ha y u)*(3*(node a ha y u)^2-1)/
        (node a ha y u*sqrt (radicand a y (node a ha y u))))=
      2*y*(F (node a ha y u)*(p a (node a ha y u))^2/
        ((node a ha y u)^3*q a (node a ha y u))) := by
  -- Positivity follows on the actual inverse branch, not on an assumed formal variable.
  have hn : 1≤node a ha y u := inverse_ge_one a ha _
  have hn0 : 0<node a ha y u := zero_lt_one.trans_le hn
  have hp := (p_bounds ha hn).1.trans_le (p_bounds ha hn).2.1
  have hq := q_pos ha hn
  have hd := psiSlope_pos ha hn
  have hthree : 0<3*(node a ha y u)^2-1 := by nlinarith
  rw [abs_of_neg (div_neg_of_neg_of_pos (mul_neg_of_neg_of_pos (mul_neg_of_neg_of_pos (by norm_num : (-2:ℝ)<0) hy) hu.1) hd),
    radicand_node ha hy ⟨hu.1.le,hu.2.le⟩,
    sqrt_mul (sq_nonneg _),sqrt_sq hp.le,sqrt_sq hu.1.le]
  unfold psiSlope
  field_simp [ne_of_gt hu.1,ne_of_gt hthree,
    show -1+(node a ha y u)^2*3≠0 by nlinarith]
  ring_nf
  have hc : (-1+(node a ha y u)^2*3)*(-1+(node a ha y u)^2*3)⁻¹=1 :=
    mul_inv_cancel₀ (by nlinarith)
  nlinarith [congrArg (fun r : ℝ => F (node a ha y u)*r) hc]

/-- The full genuine inverse-coordinate substitution holds for every real state observable.
Use: k=1,2,3 and F=n*p(n) evaluate the attained optimizer's root mass, mass, energy and spectral moment.
Article: jacobi, Appendix D.5 (regularized state quadratures).
Proof: the actual inverse curve maps (0,1) injectively onto the true turning
interval. The Lebesgue Jacobian theorem and the proved exact cancellation
give the equality; endpoint null sets identify the oriented unit integral. -/
theorem turningIntegral_substitution {a y : ℝ} (ha : -2*sqrt 3<a) (hy : 0<y) (F : ℝ → ℝ) :
    turningIntegral a ha y F=2*y*∫ u in (0:ℝ)..1,
      F (node a ha y u)*(p a (node a ha y u))^2/
        ((node a ha y u)^3*q a (node a ha y u)) := by
  -- Apply the true one-dimensional measure substitution before doing any formal cancellations.
  have hder (u : ℝ) (hu : u∈Ioo (0:ℝ) 1) :
      HasDerivWithinAt (node a ha y) (-2*y*u/psiSlope a (node a ha y u)) (Ioo (0:ℝ) 1) u :=
    (node_hasDerivAt ha hy hu).hasDerivWithinAt
  have hinj : InjOn (node a ha y) (Ioo (0:ℝ) 1) :=
    ((node_strictAnti ha hy).mono Ioo_subset_Icc_self).injOn
  have hh := integral_image_eq_integral_abs_deriv_smul measurableSet_Ioo hder hinj
    (fun n => F n*(3*n^2-1)/(n*sqrt (radicand a y n)))
  rw [node_image ha hy] at hh
  unfold turningIntegral
  rw [hh]
  have hj := setIntegral_congr_fun (μ := volume) measurableSet_Ioo fun u hu => by
    simpa only [smul_eq_mul] using node_jacobian ha hy hu F
  simp only [smul_eq_mul]
  rw [hj,integral_const_mul,← integral_Ioc_eq_integral_Ioo,
    ← intervalIntegral.integral_of_le (by norm_num : (0:ℝ)≤1)]

/-- The actual normalized power quadratures are the turning integrals of the corresponding literal powers.
Use: supplies root mass, mass and energy from one shared quadrature formula.
Article: jacobi, Appendix D.5 (regularized state quadratures).
Proof: substitute the literal power observable in the proved true change of variables. -/
theorem turningIntegral_power {a y : ℝ} (ha : -2*sqrt 3<a) (hy : 0<y) (k : ℕ) :
    turningIntegral a ha y (fun n => n^k)=hat k a ha y := turningIntegral_substitution ha hy _

end
end jacobi.RootMass
