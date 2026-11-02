import krylov.Convergence.ObservableFCSource
import krylov.Convergence.ObservableStep
import krylov.Methods.ChronologicalWindow

/-!
Article: main_krylov, apG:Dunif, actual FC secants and conjugacy.
Use: derive the entire real observed-pair dictionary from the literal
source execution and passed past direction tests. Source: actual chord
stationarity, the genuine gradient FTC and the implemented inverse solve.
No lower gain or residual estimate is imposed on the original source.
-/
namespace krylov.Convergence
noncomputable section
open Set Metric Matrix krylov.Methods krylov.Functions krylov.Nonlinear chebyshev1.Nonlinear
open scoped InnerProductSpace NNReal
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The actual complete searched FC step. Article: apG:Dunif. -/
def observableFCSearchStep (T : E ≃L[ℝ] E) (f : E → ℝ) (G : E → E)
    (r : ℝ) (x₀ : E) (k : ℕ) : E :=
  observableFCSearchPoint T f G r x₀ (k+1)-observableFCSearchPoint T f G r x₀ k

/-- The actually measured FC gradient difference. Article: apG:Dunif. -/
def observableFCSearchSecant (T : E ≃L[ℝ] E) (f : E → ℝ) (G : E → E)
    (r : ℝ) (x₀ : E) (k : ℕ) : E :=
  G (observableFCSearchPoint T f G r x₀ (k+1))-G (observableFCSearchPoint T f G r x₀ k)

/-- The actual full window is exactly the chronological real searched
step/secant transcript, with no prescribed operator substitution.
Article: main_krylov, apG:Dunif. -/
theorem observableFCSearchRun_pairs (T : E ≃L[ℝ] E) (f : E → ℝ) (G : E → E)
    (r : ℝ) (x₀ : E) (k : ℕ) :
    (observableFCSearchRun T f G r x₀ k).pairs=
      executedPairs (observableFCSearchStep T f G r x₀) (observableFCSearchSecant T f G r x₀) k := by
  induction k with
  | zero => rfl
  | succ k ih =>
    let H := observableFCSearchRun T f G r x₀ k
    change ((observableRecord T f G r x₀ H 0 false).step,
      (observableRecord T f G r x₀ H 0 false).gradient-H.gradient)::H.pairs=_
    rw [show H.pairs=_ from ih]
    congr 1
    apply Prod.ext
    · change rfcFunctionLinePoint T f fullMemory r x₀ H-(x₀+H.displacement)+0=_
      simp only [observableFCSearchStep,observableFCSearchPoint_succ,add_zero]
      rfl
    · change G (rfcFunctionLinePoint T f fullMemory r x₀ H+0)-H.gradient=_
      rw [add_zero,(observableFCSearchRun_semantics T f G r x₀ k).1]
      simp only [observableFCSearchSecant,observableFCSearchPoint_succ]
      rfl

/-- All actual old pairs are retained before the current observable
stop test. Article: main_krylov, apG:Dunif. -/
theorem observableFCSearchRun_window (T : E ≃L[ℝ] E) (f : E → ℝ) (G : E → E)
    (r : ℝ) (x₀ : E) (k : ℕ) :
    selectedWindow fullMemory (observableFCSearchRun T f G r x₀ k)=
      executedPairs (observableFCSearchStep T f G r x₀) (observableFCSearchSecant T f G r x₀) k := by
  rw [selectedWindow_full,observableFCSearchRun_pairs]

variable [CompleteSpace E]

/-- A genuine passed FC search test yields a nonzero actually searched
step; no lower step length is required. Article: apG:Dunif. -/
theorem ObservableLocalSource.fc_step_nonzero {T : E ≃L[ℝ] E} {f : E → ℝ} {G : E → E}
    {H : E → E →L[ℝ] E} {r : ℝ} {L : ℝ≥0} (S : ObservableLocalSource T f G H r L)
    (x₀ : E) (hx₀ : ‖T x₀‖<r/4) (k : ℕ)
    (hgood : ObservableFCGood (observableFCSearchRun T f G r x₀ k)) :
    observableFCSearchStep T f G r x₀ k≠0 := by
  have hr := S.radius_pos
  let x := observableFCSearchPoint T f G r x₀
  let d := rfcFunctionDirection fullMemory (observableFCSearchRun T f G r x₀ k)
  have hloc := S.fc_localization x₀ (by linarith) k
  have hx : ‖T (x k)‖<r/2 := hloc.1.trans_lt (by linarith)
  have hmin := S.fc_chord_steps x₀ (by linarith [norm_nonneg (T x₀)]) k
  have hf z (hz : z∈closedBall (0:E) r) := S.coordinate_f z
    (by simpa only [mem_closedBall,dist_zero_right] using hz)
  have hg z (hz : z∈closedBall (0:E) r) := S.coordinate_g z
    (by simpa only [mem_closedBall,dist_zero_right] using hz)
  have hgzero : coordinateGradient T G 0=0 := by simp only [coordinateGradient,map_zero,S.gradient_zero]
  have hstat := (local_chord_minimum_spec _ _ _ S.radius_pos hgzero S.hessian_zero S.small
    S.lipschitz hf hg (T (x k)) (T d) (T (x (k+1))) hx hmin).2.2.1
  have hpair : inner ℝ (coordinateGradient T G (T (x (k+1)))) (T d)=inner ℝ (G (x (k+1))) d := by
    simp only [coordinateGradient,T.symm_apply_apply]
    rw [real_inner_comm,metric_primal_dual_pairing T S.inverse_symmetric,real_inner_comm]
  rw [hpair] at hstat
  intro hz
  have he : x (k+1)=x k := sub_eq_zero.mp hz
  rw [he] at hstat
  have hh := hgood.2.2
  rw [(observableFCSearchRun_semantics T f G r x₀ k).1] at hh
  exact (ne_of_lt hh) hstat

omit [CompleteSpace E] in
/-- Each earlier actually measured image annihilates a later true FC
step whenever that later observable solve test passed.
Article: main_krylov, apG:Dunif, real triangular conjugacy. -/
theorem ObservableLocalSource.fc_step_conjugate {T : E ≃L[ℝ] E} {f : E → ℝ} {G : E → E}
    {H : E → E →L[ℝ] E} {r : ℝ} {L : ℝ≥0} (S : ObservableLocalSource T f G H r L)
    (x₀ : E) (hx₀ : ‖T x₀‖<r/4) {i j : ℕ} (hij : i<j)
    (hgood : ObservableFCGood (observableFCSearchRun T f G r x₀ j)) :
    inner ℝ (observableFCSearchSecant T f G r x₀ i) (observableFCSearchStep T f G r x₀ j)=0 := by
  let B := observableFCSearchRun T f G r x₀ j
  let W := selectedWindow fullMemory B
  let d := rfcFunctionDirection fullMemory B
  have hp : (observableFCSearchStep T f G r x₀ i,observableFCSearchSecant T f G r x₀ i)∈W := by
    rw [show W=_ from observableFCSearchRun_window T f G r x₀ j]
    exact executedPairs_contains _ _ hij
  obtain ⟨a,ha⟩ := List.mem_iff_get.mp hp
  have hc := congrFun (conjugacyDirection_conjugate (windowSteps W) (windowImages W) B.gradient hgood.2.1) a
  have hy : windowImages W a=observableFCSearchSecant T f G r x₀ i := congrArg Prod.snd ha
  change inner ℝ (windowImages W a) d=0 at hc
  rw [hy] at hc
  have hmin := S.fc_chord_steps x₀ (by linarith [norm_nonneg (T x₀)]) j
  obtain ⟨alpha,halpha⟩ := hmin.2.1
  have hs : observableFCSearchStep T f G r x₀ j=alpha • d := by
    apply T.injective
    rw [map_smul]
    change T (observableFCSearchPoint T f G r x₀ (j+1)-observableFCSearchPoint T f G r x₀ j)=_
    rw [map_sub,halpha,add_sub_cancel_left]
  rw [hs,real_inner_smul_right,hc,mul_zero]

end
end krylov.Convergence
