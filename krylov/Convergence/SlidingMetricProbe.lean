import krylov.Convergence.SlidingRFCMetric

/-!
Article: main_krylov, thm:Ip, physical probe and independence budgets.
Use: derive the true metric probe bound and sigma_H from actual physical
observations. Source: positive-root energy and exact actual unit-column
normalization. No canonical independence or probe bound is assumed.
-/
namespace krylov.Convergence
noncomputable section
open Matrix Filter Topology krylov.Methods krylov.Nonlinear krylov.Reference krylov.Correction
open scoped InnerProductSpace Matrix.Norms.L2Operator
variable {n p : ℕ}
set_option maxHeartbeats 800000

/-- A primitive upper quadratic endpoint gives the exact true metric
root norm bound on every actual physical vector. -/
theorem metricCoordinates_norm_upper (base : Matrix (Fin n) (Fin n) ℝ) (hb : base.PosDef)
    {upper : ℝ} (hu : 0<upper)
    (hupper : ∀ v,inner ℝ v (cgOperator base v)≤upper*‖v‖^2)
    (v : EuclideanSpace ℝ (Fin n)) :
    ‖metricCoordinates base hb v‖≤Real.sqrt upper*‖v‖ := by
  apply (sq_le_sq₀ (norm_nonneg _) (by positivity)).mp
  rw [mul_pow,Real.sq_sqrt hu.le]
  simpa only [metricCoordinates_apply,restart_root_pairing base hb,real_inner_self_eq_norm_sq] using hupper v

/-- Original bounded physical probes have a derived bounded size in the
true Hstar metric; nonzero probes remain nonzero. -/
theorem metric_path_probe_bound (base : Matrix (Fin n) (Fin n) ℝ) (hb : base.PosDef)
    (center : EuclideanSpace ℝ (Fin n)) (x v : ℕ → EuclideanSpace ℝ (Fin n))
    {upper cP : ℝ} (hu : 0<upper)
    (hupper : ∀ a,inner ℝ a (cgOperator base a)≤upper*‖a‖^2)
    (hp : ∀ᶠ k in atTop,v k≠0 ∧‖v k‖≤cP*‖metricCoordinates base hb (x k-center)‖) :
    ∀ᶠ k in atTop,metricCoordinates base hb (v k)≠0 ∧
      ‖metricCoordinates base hb (v k)‖≤(Real.sqrt upper*|cP|)*‖metricCoordinates base hb (x k-center)‖ := by
  filter_upwards [hp] with k hk
  constructor
  · exact fun hz=>hk.1 ((metricCoordinates base hb).injective (hz.trans (map_zero _).symm))
  · exact (metricCoordinates_norm_upper base hb hu hupper (v k)).trans
      ((mul_le_mul_of_nonneg_left
        (hk.2.trans (mul_le_mul_of_nonneg_right (le_abs_self _) (norm_nonneg _))) (Real.sqrt_nonneg _)).trans_eq
        (by ring))

/-- Physical unit-step independence transports to the exact canonical
sigma_H=sigma_flat*sqrt(mu/upper), using actual source step nonzeroness. -/
theorem metric_path_window_gain (base : Matrix (Fin n) (Fin n) ℝ) (hb : base.PosDef)
    (center : EuclideanSpace ℝ (Fin n)) (x : ℕ → EuclideanSpace ℝ (Fin n))
    {mu upper σ : ℝ} (hmu : 0<mu) (hu : 0<upper) (hσ : 0≤σ)
    (hlower : ∀ a,mu*‖a‖^2≤ inner ℝ a (cgOperator base a))
    (hupper : ∀ a,inner ℝ a (cgOperator base a)≤upper*‖a‖^2)
    (hs : ∀ᶠ k in atTop,∀ i : Fin p,windowStep (n:=p) x k i≠0)
    (hgain : ∀ᶠ k in atTop,∀ c : Fin p → ℝ,
      σ^2*‖WithLp.toLp 2 c‖^2≤‖combine (unitWindow (windowStep (n:=p) x k)) c‖^2) :
    ∀ᶠ k in atTop,∀ c : Fin p → ℝ,
      (σ*Real.sqrt (mu/upper))^2*‖WithLp.toLp 2 c‖^2≤
        ‖combine (unitWindow (windowStep (n:=p) (fun j=>metricCoordinates base hb (x j-center)) k)) c‖^2 := by
  filter_upwards [hs,hgain] with k hsk hg c
  rw [centered_metric_windowStep]
  exact metric_window_gain base hb _ hsk hmu hu hσ hlower hupper hg c

end
end krylov.Convergence
