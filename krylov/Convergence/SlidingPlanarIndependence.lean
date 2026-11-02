import krylov.Convergence.SlidingRFCMetricRate

/-!
Article: main_krylov, thm:Ip, vacuous planar RFC independence.
Use: remove (A4) in dimension two: its sole stored unit column always
has gain exactly one. Source: the actual nonzero stored step is forced
by the original defined observed inverse; no quantitative independence
or angle premise remains.
-/
namespace krylov.Convergence
noncomputable section
open Matrix Filter Topology krylov.Methods
open scoped InnerProductSpace Matrix.Norms.L2Operator
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- A single actual normalized column has exactly unit synthesis gain. -/
theorem single_unit_window_gain (s : Fin 1 → E) (hs : ∀ i,s i≠0) (c : Fin 1 → ℝ) :
    (1:ℝ)^2*‖WithLp.toLp 2 c‖^2≤‖combine (unitWindow s) c‖^2 := by
  simp only [one_pow,one_mul,combine,Fin.sum_univ_one,norm_smul,Real.norm_eq_abs,
    unitWindow_norm s hs 0,mul_one,EuclideanSpace.real_norm_sq_eq,Fin.sum_univ_one]
  exact (sq_abs (c 0)).symm.le

/-- In the actual planar RFC source, the old-window independence condition
follows from the article's defined-solve assumption with constant one. -/
theorem slidingRFC_planar_gain_automatic (G : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 2))
    (x : ℕ → EuclideanSpace ℝ (Fin 2))
    (hsolve : ∀ᶠ k in atTop,IsUnit (slidingRFCSolveMatrix (n:=0) G x k).det) :
    ∀ᶠ k in atTop,∀ c : Fin 1 → ℝ,(1:ℝ)^2*‖WithLp.toLp 2 c‖^2≤
      ‖combine (unitWindow (windowStep (n:=1) x k)) c‖^2 := by
  filter_upwards [hsolve] with k hk c
  exact single_unit_window_gain _ (fun i=>observed_solve_step_ne_zero _ _ hk i) c

end
end krylov.Convergence
