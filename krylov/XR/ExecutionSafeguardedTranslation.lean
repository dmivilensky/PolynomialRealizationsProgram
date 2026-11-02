import krylov.XR.ModelTranslation

/-!
Article: main_krylov, alg:xr and lem:xr-local, arbitrary coordinate origin.
Use: transport the literal safeguarded executor, including actual (G), the
single rejected probe, both ModelSteps, backtracking and capacity updates.
Source: the unchanged observed secants and gradient-related safeguard.
-/
namespace krylov.XR
noncomputable section
open scoped InnerProductSpace
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Applying (G) inside ModelStep gives the raw search exactly the actual
safeguarded direction while preserving its observations and spectral data. -/
def safeguardedModel (model : State E → ModelResult E) (S : State E) : ModelResult E :=
  { model S with direction := (model S).safeDirection S }

theorem safeguardedModel_shift (b : E) (model : State E → ModelResult E)
    (hmodel : ∀ S, model (S.shift b) = (model S).shift b) (S : State E) :
    safeguardedModel model (S.shift b) = (safeguardedModel model S).shift b := by
  rw [safeguardedModel, hmodel]
  rfl

/-- The safeguarded search, with its true rejected probe and chosen
backtracking index, is exactly independent of the coordinate origin. -/
theorem outerSearch_shift (b : E) (model : State E → ModelResult E)
    (hmodel : ∀ S, model (S.shift b) = (model S).shift b)
    (f : E → ℝ) (G : E → E) (sigma : ℝ) (S : State E) :
    outerSearch model (fun x => f (x-b)) (fun x => G (x-b)) sigma (S.shift b) =
      (outerSearch model f G sigma S).shift b :=
  rawOuterSearch_shift b (safeguardedModel model) (safeguardedModel_shift b model hmodel) f G sigma S

theorem outerAdvance_shift (b : E) (P : Parameters) (dimension : ℕ)
    (model : State E → ModelResult E)
    (hmodel : ∀ S, model (S.shift b) = (model S).shift b)
    (f : E → ℝ) (G : E → E) (S : State E) :
    outerAdvance P dimension model (fun x => f (x-b)) (fun x => G (x-b)) (S.shift b) =
      (outerAdvance P dimension model f G S).shift b :=
  rawOuterAdvance_shift b P dimension (safeguardedModel model)
    (safeguardedModel_shift b model hmodel) f G S

theorem run_shift (b : E) (P : Parameters) (dimension : ℕ)
    (model : State E → ModelResult E)
    (hmodel : ∀ S, model (S.shift b) = (model S).shift b)
    (f : E → ℝ) (G : E → E) (S : State E) (k : ℕ) :
    run P dimension model (fun x => f (x-b)) (fun x => G (x-b)) (S.shift b) k =
      (run P dimension model f G S k).shift b := by
  induction k with
  | zero => rfl
  | succ k ih => rw [run, ih, outerAdvance_shift, run]; exact hmodel

/-- The complete literal algorithm, with (G) enabled, commutes with the
change of origin used in the local reference theorems. -/
theorem algorithmRun_shift {n : ℕ} (b : EuclideanSpace ℝ (Fin n))
    (P : Parameters) (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (G : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (bounds : SpectralBounds) (k : ℕ) :
    algorithmRun P (fun x => f (x-b)) (fun x => G (x-b)) b bounds k =
      (algorithmRun P f G 0 bounds k).shift b := by
  unfold algorithmRun
  rw [algorithmInitialState_shift]
  exact run_shift b P n (algorithmModel P) (algorithmModel_shift b P) f G _ k

end
end krylov.XR
