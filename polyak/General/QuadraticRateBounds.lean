import polyak.General.QuadraticRateEnvelope
import polyak.General.QuadraticDiagonal

/-! Genuine quadratic gradient executions have a uniform spectral bound
in every finite dimension. Their actual ratios form a subclass of the
original smooth strongly convex problem, before taking either supremum. -/
noncomputable section
namespace polyak.General
open Filter Set
open scoped Topology

/-- Every actual affine quadratic in the class is an admissible original
objective with the same minimizer, start and zero-momentum execution. -/
theorem quadraticRatios_subset_allRatios {μ L α β : ℝ} (hμ : 0<μ) (hL : μ<L)
    (n : ℕ) : quadraticRatios μ L α β n⊆Dynamics.allRatios μ L α β n := by
  rintro r ⟨d,hd,Q,x₀,hx,rfl⟩
  exact ⟨d,hd,Q.potential,Q.admissible hμ hL,Q.center,x₀,
    Q.center_minimizer hμ.le,hx,rfl⟩

theorem quadraticRatios_bddAbove {μ L α β : ℝ} (hμ : 0<μ) (hL : μ<L)
    (hα : 0≤α) (hβ : 0≤β) (n : ℕ) :
    BddAbove (insert 0 (quadraticRatios μ L α β n)) :=
  (Dynamics.allRatios_bddAbove hμ hL hα hβ n).mono
    (insert_subset_insert (quadraticRatios_subset_allRatios hμ hL n))

theorem quadraticWorst_nonneg {μ L α β : ℝ} (hμ : 0<μ) (hL : μ<L)
    (hα : 0≤α) (hβ : 0≤β) (n : ℕ) : 0≤quadraticWorst μ L α β n :=
  le_csSup (quadraticRatios_bddAbove hμ hL hα hβ n) (mem_insert _ _)

theorem quadraticWorst_le_worstAll {μ L α β : ℝ} (hμ : 0<μ) (hL : μ<L)
    (hα : 0≤α) (hβ : 0≤β) (n : ℕ) :
    quadraticWorst μ L α β n≤Dynamics.worstAll μ L α β n :=
  csSup_le_csSup (Dynamics.allRatios_bddAbove hμ hL hα hβ n) (insert_nonempty _ _)
    (insert_subset_insert (quadraticRatios_subset_allRatios hμ hL n))

/-- The genuine quadratic subclass gives a direct lower bound for the
original nonlinear rate, without any nonlinear interpolation construction. -/
theorem quadraticExecutionRate_le_rate {μ L α β : ℝ} (hμ : 0<μ) (hL : μ<L)
    (hα : 0≤α) (hβ : 0≤β) :
    quadraticExecutionRate μ L α β≤Dynamics.rate μ L α β := by
  exact limsup_le_limsup (Eventually.of_forall (fun n=>
    Real.rpow_le_rpow (quadraticWorst_nonneg hμ hL hα hβ n)
      (quadraticWorst_le_worstAll hμ hL hα hβ n) (by positivity)))
    (isCoboundedUnder_le_of_le atTop (fun n=>
      Real.rpow_nonneg (quadraticWorst_nonneg hμ hL hα hβ n) _))
    (isBoundedUnder_of ⟨1+α*L+2*β,Dynamics.worstAll_root_le hμ hL hα hβ⟩)

/-- Full orthogonal spectral decomposition transfers the scalar envelope
with its original constant, independently of the dimension and objective. -/
theorem quadraticModel_iterate_bound {μ L α β : ℝ} (hμ : 0<μ) (hL : μ<L)
    (hα : 0<α) (hβ : 0≤β) (hβ1 : β<1) (hquad : α*L<2*(1+β))
    {d : ℕ} (Q : QuadraticModel μ L d) (x₀ : EuclideanSpace ℝ (Fin d)) (n : ℕ) :
    ‖Dynamics.iterate (gradient Q.potential) α β x₀ n-Q.center‖≤
      quadraticEnvelope (Dynamics.quadraticRate μ L α β) β n*‖x₀-Q.center‖ := by
  apply QuadraticDiagonal.norm_iterate_centered_le Q.H Q.symmetric Q.lower Q.upper
    (gradient Q.potential) Q.center Q.gradient_potential
    (quadraticEnvelope_nonneg (Growth.quadraticRate_pos hμ hL hα hβ hβ1 hquad).le hβ n)
    α β n ?_ x₀
  intro lam hlam
  simpa only [Real.norm_eq_abs] using scalarQuadratic_uniform_bound hμ hL hα hβ hβ1 hquad hlam n

theorem quadraticWorst_le_envelope {μ L α β : ℝ} (hμ : 0<μ) (hL : μ<L)
    (hα : 0<α) (hβ : 0≤β) (hβ1 : β<1) (hquad : α*L<2*(1+β)) (n : ℕ) :
    quadraticWorst μ L α β n≤quadraticEnvelope (Dynamics.quadraticRate μ L α β) β n := by
  apply csSup_le (insert_nonempty _ _)
  intro r hr
  rcases hr with rfl|⟨d,_,Q,x₀,hx,rfl⟩
  · exact quadraticEnvelope_nonneg (Growth.quadraticRate_pos hμ hL hα hβ hβ1 hquad).le hβ n
  · exact (div_le_iff₀ (norm_pos_iff.mpr (sub_ne_zero.mpr hx))).mpr
      (quadraticModel_iterate_bound hμ hL hα hβ hβ1 hquad Q x₀ n)

/-- The actual dimension-uniform quadratic execution rate cannot exceed the
characteristic-root maximum, including repeated-root transients. -/
theorem quadraticExecutionRate_le_quadraticRate {μ L α β : ℝ} (hμ : 0<μ) (hL : μ<L)
    (hα : 0<α) (hβ : 0≤β) (hβ1 : β<1) (hquad : α*L<2*(1+β)) :
    quadraticExecutionRate μ L α β≤Dynamics.quadraticRate μ L α β :=
  limsup_root_le_of_quadraticEnvelope (quadraticWorst_nonneg hμ hL hα.le hβ)
    (Growth.quadraticRate_pos hμ hL hα hβ hβ1 hquad) hβ
    (quadraticWorst_le_envelope hμ hL hα hβ hβ1 hquad)

end polyak.General
