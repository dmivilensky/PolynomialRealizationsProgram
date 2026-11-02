import jacobi.RootMass.ConstraintDerivative

/-!
Article: jacobi, Theorem D.8.
The derivative of the actual constraint is strictly positive, including the
endpoint-safe justification of differentiation under its integral. Certified
Q positivity controls the interior, while the original K formula controls
u=1. Continuity of the nonsingular derivative gives the full C1 statement.
Source: exact rational identity Q=psi²*K and actual classical derivatives.
Use: differentiating it relates the certified Q derivative to the nonsingular constraint derivative.
-/
namespace jacobi.RootMass
noncomputable section
open Real Set MeasureTheory Filter
open scoped Topology ContDiff
set_option backward.isDefEq.respectTransparency false

/-- The literal Q representation holds as an identity of real functions, including removable zero-denominator cases.
Use: differentiating it relates the certified Q derivative to the nonsingular constraint derivative.
Article: jacobi, Theorem D.8.
Proof: zero polynomial factors give zero on both sides; otherwise clear the nonzero rational denominators. -/
theorem Q_eq (a n : ℝ) : Q a n=(psi a n)^2*K a n := by
  -- Handle all zero-denominator cases explicitly before rational cancellation.
  by_cases hp : p a n=0
  · simp only [Q,psi,K,hp,zero_mul,div_zero,zero_pow (by decide : 2≠0),zero_pow (by decide : 3≠0),zero_div,mul_zero]
  by_cases hq : q a n=0
  · simp only [Q,K,hq,mul_zero,div_zero]
  by_cases hn : n=0
  · subst n
    simp [Q,psi,K]
  unfold Q psi K
  field_simp

/-- The actual Q derivative equals the derivative of its nonsingular factorization.
Use: turns the exact positive polynomial certificate into positivity of the true Ghat derivative integrand.
Article: jacobi, Theorem D.8.
Proof: differentiate the proved identity of actual functions; uniqueness of classical derivatives identifies the coefficients. -/
theorem QSlope_factor {a n : ℝ} (ha : -2*sqrt 3<a) (hn : 1≤n) :
    QSlope a n=2*psi a n*psiSlope a n*K a n+(psi a n)^2*deriv (K a) n := by
  -- The two actual derivatives belong to the identical rational function.
  have hp := ((p_bounds ha hn).1.trans_le (p_bounds ha hn).2.1).ne'
  have hq := (q_pos ha hn).ne'
  have hk := (K_contDiffAt ha hn).differentiableAt (by simp)
  have hh : HasDerivAt (fun t => (psi a t)^2*K a t)
      (2*psi a n*psiSlope a n*K a n+(psi a n)^2*deriv (K a) n) n := by
    convert ((psi_hasDerivAt hp).pow 2).mul hk.hasDerivAt using 1
    norm_num only [Nat.cast_ofNat,Nat.reduceSub,pow_one,Pi.pow_apply]
  have he : (fun t => (psi a t)^2*K a t)=Q a := funext fun t => (Q_eq a t).symm
  rw [he] at hh
  exact (Q_hasDerivAt hp hq).unique hh

/-- The true nonsingular derivative integrand is strictly positive on the entire unit integration interval.
Use: proves strict positivity of the actual derivative after integration.
Article: jacobi, Theorem D.8.
Proof: for u<1 use the actual inverse equation and the certified positive
Q derivative. At u=1 the original derivative formula is 8*y*K(1)>0,
which also verifies the sign of the continuous endpoint extension. -/
theorem constraintSlopeIntegrand_pos {a y u : ℝ} (ha : -(17/5:ℝ)≤a) (hy : 0<y) (hu : u∈Icc (0:ℝ) 1) :
    0<constraintSlopeIntegrand a (sharp_parameter ha) y u := by
  -- Positivity uses the actual inverse branch at every point, including the endpoint.
  let hpa := sharp_parameter ha
  by_cases he : u=1
  · subst u
    simp only [constraintSlopeIntegrand,node_one,one_pow,sub_self,zero_div,mul_zero,add_zero]
    have hk : 0<K a 1 := div_pos (pow_pos ((p_bounds hpa le_rfl).1.trans_le (p_bounds hpa le_rfl).2.1) 3)
      (mul_pos (by norm_num) (q_pos hpa le_rfl))
    positivity
  · have hr : 0<1-u^2 := by nlinarith [hu.1,hu.2,lt_of_le_of_ne hu.2 he]
    have hn : 1<node a hpa y u := inverse_gt_one hpa (mul_pos hy hr)
    have hd := psiSlope_pos hpa hn.le
    have hQ := QSlope_pos ha hn
    have hf := QSlope_factor hpa hn.le
    have hpsi : psi a (node a hpa y u)=y*(1-u^2) := psi_inverse hpa (mul_pos hy hr).le
    rw [hpsi] at hf
    have hid : constraintSlopeIntegrand a hpa y u=4*QSlope a (node a hpa y u)/
        ((1-u^2)*psiSlope a (node a hpa y u)) := by
      unfold constraintSlopeIntegrand
      field_simp [hd.ne',hr.ne']
      nlinarith
    rw [hid]
    exact div_pos (mul_pos (by norm_num) hQ) (mul_pos hr hd)

/-- The true classical derivative of the actual constraint quadrature is strictly positive everywhere on its positive parameter domain.
Use: completes the differential assertion of the source's Monotonicity lemma, beyond strict order monotonicity alone.
Article: jacobi, Theorem D.8.
Proof: the genuine derivative integral has a continuous strictly positive
integrand throughout [0,1]. This interval has positive measure, so its true integral is positive. -/
theorem Ghat_deriv_pos {a y : ℝ} (ha : -(17/5:ℝ)≤a) (hy : 0<y) :
    0<deriv (Ghat a (sharp_parameter ha)) y := by
  -- All derivative and integrability hypotheses are conclusions of actual compact domination.
  rw [(Ghat_hasDerivAt (sharp_parameter ha) hy).deriv]
  have hc : Continuous (constraintSlopeIntegrand a (sharp_parameter ha) y) :=
    (constraintSlopeIntegrand_continuous a (sharp_parameter ha)).comp (continuous_const.prodMk continuous_id)
  have hi : IntegrableOn (constraintSlopeIntegrand a (sharp_parameter ha) y) (Icc (0:ℝ) 1) volume := hc.continuousOn.integrableOn_compact (isCompact_Icc : IsCompact (Icc (0:ℝ) 1))
  have hp : ∀ᵐ u ∂volume.restrict (Icc (0:ℝ) 1),0<constraintSlopeIntegrand a (sharp_parameter ha) y u :=
    (ae_restrict_mem measurableSet_Icc).mono fun _ hu => constraintSlopeIntegrand_pos ha hy hu
  apply (integral_pos_iff_support_of_nonneg_ae (hp.mono fun _ h => h.le) hi).mpr
  have he : (Function.support (constraintSlopeIntegrand a (sharp_parameter ha) y))=ᵐ[volume.restrict (Icc (0:ℝ) 1)] univ :=
    hp.mono fun _ hu => by
      change (_≠0)=True
      exact propext (iff_true_intro hu.ne')
  rw [measure_congr he]
  norm_num

/-- The actual defining constraint is C1 on its complete positive domain.
Use: completes the regularity assertion used by all implicit defining-parameter arguments.
Article: jacobi, Theorem D.8.
Proof: its genuine classical derivative equals the integral of the jointly
continuous nonsingular derivative integrand. Compact parametric integration
makes that derivative continuous; the classical C1 characterization applies. -/
theorem Ghat_contDiffOn {a : ℝ} (ha : -2*sqrt 3<a) : ContDiffOn ℝ 1 (Ghat a ha) (Ioi (0:ℝ)) := by
  -- The continuous derivative is represented by an actual convergent compact integral.
  have hc : Continuous (fun y => ∫ u in Icc (0:ℝ) 1,constraintSlopeIntegrand a ha y u) :=
    continuous_parametric_integral_of_continuous (constraintSlopeIntegrand_continuous a ha) isCompact_Icc
  have he : EqOn (deriv (Ghat a ha)) (fun y => ∫ u in Icc (0:ℝ) 1,constraintSlopeIntegrand a ha y u) (Ioi (0:ℝ)) :=
    fun y hy => (Ghat_hasDerivAt ha hy).deriv
  exact (contDiffOn_succ_iff_deriv_of_isOpen (n := 0) isOpen_Ioi).mpr
    ⟨fun y hy => (Ghat_hasDerivAt ha hy).differentiableAt.differentiableWithinAt,
      by simp,contDiffOn_zero.mpr (hc.continuousOn.congr he)⟩

end
end jacobi.RootMass
