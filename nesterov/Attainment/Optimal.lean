import nesterov.Attainment.FiniteSupport
import nesterov.Attainment.Tail
import polyak.Spectral.Atomic

/-! Every optimal probability spectrum above the quadratic boundary has
strict minimizer reserve and finitely many active lag constraints. -/
noncomputable section
open MeasureTheory
namespace nesterov.Attainment
open Spectral

theorem optimal_strict_minimizer (M : StationaryMethod) {μ L C : ℝ} {ν : Spectrum}
    (hμ : 0 < μ) (hμL : μ < L) (ht : Closure.T M μ L ≠ 0)
    (htq : Real.log (Rates.quadraticRate M μ L) < Closure.T M μ L)
    (h : Feasible (M.symbolPair μ L (Closure.T M μ L)) (Closure.T M μ L) ν C) :
    |C| < meanG ν (M.symbolPair μ L (Closure.T M μ L)) := by
  classical
  obtain ⟨F,hF,hFi,hcarrier⟩ := exists_finite_boundary_carrier M hμ hμL ht htq
  let : Fintype F := hF.fintype
  obtain ⟨w,hw,he⟩ := polyak.Spectral.exists_finiteSpectrum_of_support ν (hcarrier ν C h)
  have hci : Function.Injective (fun j : F => j.val) := fun _ _ hij => Subtype.ext hij
  have hc : ∀ j : F, -1 < (j.val : ℝ) ∧ (j.val : ℝ) < 1 := fun j => hFi j.val j.property
  rw [← he] at h ⊢
  exact finite_strict_above_quadratic M hμ hμL htq ht w (fun j => j.val) hw hci hc h

theorem optimal_active_lags_bounded (M : StationaryMethod) {μ L C : ℝ} {ν : Spectrum}
    (hμ : 0 < μ) (hμL : μ < L) (ht : Closure.T M μ L ≠ 0)
    (htq : Real.log (Rates.quadraticRate M μ L) < Closure.T M μ L)
    (h : Feasible (M.symbolPair μ L (Closure.T M μ L)) (Closure.T M μ L) ν C) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      0 < meanA ν (M.symbolPair μ L (Closure.T M μ L)) (Closure.T M μ L) n-
        meanB ν (M.symbolPair μ L (Closure.T M μ L)) n+C*Real.sinh (n*Closure.T M μ L) ∧
      0 < meanA ν (M.symbolPair μ L (Closure.T M μ L)) (Closure.T M μ L) n+
        meanB ν (M.symbolPair μ L (Closure.T M μ L)) n-C*Real.sinh (n*Closure.T M μ L) :=
  active_lags_bounded ν _ (optimal_strict_minimizer M hμ hμL ht htq h) ht

/-- A single finite-dimensional genuine objective attains the optimal exponent.
The dimension is fixed for the entire trajectory. -/
theorem exists_finite_optimal_objective (M : StationaryMethod) {μ L : ℝ}
    (hμ : 0 < μ) (hμL : μ < L) (ht : Closure.T M μ L ≠ 0)
    (htq : Real.log (Rates.quadraticRate M μ L) < Closure.T M μ L) :
    ∃ (J : Type) (_ : Fintype J) (f : EuclideanSpace ℂ J → ℝ) (w : ℕ → EuclideanSpace ℂ J),
      polyak.CenteredSmoothStronglyConvex μ L f ∧ M.IsTrajectory (gradient f) w ∧
        ∀ k, ‖w k‖ = Real.exp (k*Closure.T M μ L) := by
  classical
  obtain ⟨ν,C,h⟩ := Closure.T_mem M hμ hμL
  obtain ⟨F,hF,_,hcarrier⟩ := exists_finite_boundary_carrier M hμ hμL ht htq
  let : Fintype F := hF.fintype
  obtain ⟨weights,hw,he⟩ := polyak.Spectral.exists_finiteSpectrum_of_support ν (hcarrier ν C h)
  rw [← he] at h
  obtain ⟨f,hf,htraj⟩ := finite_exists_objective M hμ hμL weights (fun j => j.val) hw h
  exact ⟨F,inferInstance,f,finiteLatent weights (fun j => j.val) (Closure.T M μ L),hf,htraj,
    norm_finiteLatent weights (fun j => j.val) hw (Closure.T M μ L)⟩

/-- At the quadratic endpoint, a maximizing actual scalar quadratic gives
one planar trajectory attaining the maximal exponent at every time. -/
theorem quadratic_optimal_attainment (M : StationaryMethod) {μ L : ℝ}
    (hμ : 0 < μ) (hμL : μ < L)
    (hT : Closure.T M μ L=Real.log (Rates.quadraticRate M μ L)) :
    ∃ lam ∈ Set.Icc μ L, ∃ z : ℂ,
      polyak.CenteredSmoothStronglyConvex μ L (fun x : ℂ => lam/2*‖x‖^2) ∧
      M.IsTrajectory (gradient (fun x : ℂ => lam/2*‖x‖^2)) (fun k => z^k) ∧
      (∀ k : ℕ, ‖z^k‖=Real.exp (k*Closure.T M μ L)) ∧
      (∀ k : ℕ, M.stateNorm (fun j => z^j) k=Real.exp (k*Closure.T M μ L)*
        M.stateNorm (fun j => z^j) 0) := by
  obtain ⟨lam,hlam,z,hz,hr⟩ := (Rates.quadraticRate_isGreatest M hμ hμL).1
  have hnorm : ‖z‖=Real.exp (Closure.T M μ L) := by
    rw [hT,Real.exp_log (Rates.quadraticRate_pos M hμ hμL)]
    exact hr.symm
  have he : Rates.scalarQuadratic μ L lam=(fun x : ℂ => lam/2*‖x‖^2) := by
    funext x
    dsimp [Rates.scalarQuadratic,polyak.denormalizeFunction,Rates.normalizedCurvature]
    field_simp [ne_of_gt (sub_pos.mpr hμL)]
    ring
  have hf := Rates.scalarQuadratic_centered hμ hμL hlam
  rw [he] at hf
  have hw := (Rates.HilbertRun.ofRoot M hμ hμL hlam z hz).trajectory
  change M.IsTrajectory (gradient (Rates.scalarQuadratic μ L lam)) (fun k => z^k) at hw
  rw [he] at hw
  refine ⟨lam,hlam,z,hf,hw,fun k => ?_,fun k => ?_⟩
  · rw [norm_pow,hnorm,← Real.exp_nat_mul]
  · rw [Rates.wave_stateNorm M,hnorm,← Real.exp_nat_mul]

end nesterov.Attainment
