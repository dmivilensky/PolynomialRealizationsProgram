import krylov.Stability.AnalyticCorrection
import krylov.Methods.ExecutedProbed
import krylov.Methods.WindowCoordinates

/-!
Article: main_krylov, lem:U(d), regularity of genuine retained-history directions.
Use: actual past step/secant regularity propagates through full, sliding and
restarted observed-window direction solves in fixed finite coordinates.
Source: the proved actual history coordinate bridge and genuine analytic conjugacy solve.
-/

namespace krylov.Stability
noncomputable section
open Matrix krylov.Methods
open scoped InnerProductSpace
variable {E X : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable [NormedAddCommGroup X] [NormedSpace ℝ X]

/-- The actual retained-history direction is analytic in the genuine past vectors and current gradient at its real inverse domain.
Use: RFC regularity reads the actual recorded secants, including all correction contributions.
Article: main_krylov, lem:U(d), actual retained conjugacy direction.
Proof: identify the true retained list with its fixed chronological-age array;
the actual computed direction equals the proved analytic finite conjugacy solve
on exactly those real steps, observed secants and current gradient. -/
theorem retained_history_direction_analytic (memory : ℕ → ℕ) (H : X → History E)
    (s y : X → ℕ → E) (x : X) (k : ℕ)
    (hshape : ∀ p, (H p).pairs=executedPairs (s p) (y p) k)
    (hs : ∀ i<k, AnalyticAt ℝ (fun p => s p i) x)
    (hy : ∀ i<k, AnalyticAt ℝ (fun p => y p i) x)
    (hg : AnalyticAt ℝ (fun p => (H p).gradient) x)
    (hC : (crossGram (fun i : Fin (min (memory k) k) => y x (k-1-i.val))
      (fun i : Fin (min (memory k) k) => s x (k-1-i.val))).det≠0) :
    AnalyticAt ℝ (fun p => windowDirection (selectedWindow memory (H p)) (H p).gradient) x := by
  -- The varying history is used only through its true current gradient and its true finite recorded data.
  have hs' (i : Fin (min (memory k) k)) : AnalyticAt ℝ (fun p => s p (k-1-i.val)) x := by
    have hi := i.isLt
    exact hs _ (by omega)
  have hy' (i : Fin (min (memory k) k)) : AnalyticAt ℝ (fun p => y p (k-1-i.val)) x := by
    have hi := i.isLt
    exact hy _ (by omega)
  apply (analytic_conjugacyDirection _ _ _ x hs' hy' hg hC).congr
  apply Filter.Eventually.of_forall
  intro p
  dsimp only
  rw [selectedWindow_of_executed_pairs memory (H p) (s p) (y p) k (hshape p),
    windowDirection_executed_take]

end
end krylov.Stability
