import bezout.Probability.FiniteResponse
import Mathlib.Probability.Independence.Basic
import Mathlib.Probability.ConditionalExpectation
import Mathlib.Probability.Distributions.Uniform

/-!
Article: bezout, Theorem 3.1, attained stochastic lower bound.
Use: an actual finite probability model supplies conditionally centered
errors of exactly the prescribed conditional variance. Independence is
used only for this attaining example, never for the general upper bound.
Proof: independent uniform Boolean coordinates and their past filtration.
-/

namespace bezout.Probability.Signs
noncomputable section
open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators

/-- The fair two-point law used by the attaining oracle. -/
def coin : Measure Bool := (PMF.uniformOfFintype Bool).toMeasure

instance : IsProbabilityMeasure coin := inferInstanceAs
  (IsProbabilityMeasure (PMF.uniformOfFintype Bool).toMeasure)

/-- The finite product probability space contains one independent sign per call. -/
def law (N : ℕ) : Measure (Fin N → Bool) := Measure.pi (fun _ => coin)

instance (N : ℕ) : IsProbabilityMeasure (law N) := inferInstanceAs
  (IsProbabilityMeasure (Measure.pi (fun _ : Fin N => coin)))

/-- A scalar error taking the two values `sigma` and `-sigma`. -/
def value (σ : ℝ) (b : Bool) : ℝ := if b then σ else -σ

/-- The error at a finite oracle call. -/
def error {N : ℕ} (σ : ℝ) (s : Fin N) (ω : Fin N → Bool) : ℝ := value σ (ω s)

/-- Extend the finite error stream by zero outside its actual horizon. -/
def stream (N : ℕ) (σ : ℝ) (s : ℕ) (ω : Fin N → Bool) : ℝ :=
  if hs : s < N then error σ ⟨s, hs⟩ ω else 0

/-- The sigma-algebra before call `s` contains precisely the earlier errors. -/
def past (N : ℕ) (σ : ℝ) : Filtration ℕ (inferInstance : MeasurableSpace (Fin N → Bool)) where
  seq s := ⨆ j : Fin N, ⨆ (_ : j.val < s), MeasurableSpace.comap (error σ j) (inferInstance : MeasurableSpace ℝ)
  mono' _s _t hst := iSup_le fun j => iSup_le fun hj =>
    le_iSup_of_le j (le_iSup_of_le (hj.trans_le hst) le_rfl)
  le' _ := iSup_le fun j => iSup_le fun _ =>
    ((measurable_of_finite (value σ)).comp (measurable_pi_apply j)).comap_le

/-- Sign errors have exactly constant squared norm, sample by sample. -/
theorem error_norm_sq {N : ℕ} (σ : ℝ) (s : Fin N) (ω : Fin N → Bool) :
    ‖error σ s ω‖ ^ 2 = σ ^ 2 := by
  simp only [error, value, Real.norm_eq_abs, sq_abs]
  split <;> simp_all

/-- Each finite error is measurable in the ambient product space. -/
theorem error_measurable {N : ℕ} (σ : ℝ) (s : Fin N) : Measurable (error σ s) :=
  (measurable_of_finite (value σ)).comp (measurable_pi_apply s)

/-- Every error has zero mean under the fair product law. -/
theorem error_integral {N : ℕ} (σ : ℝ) (s : Fin N) :
    (∫ ω, error σ s ω ∂law N) = 0 := by
  have hmap := (measurePreserving_eval (fun _ : Fin N => coin) s).map_eq
  have heq : (∫ ω, error σ s ω ∂law N) = ∫ b, value σ b ∂coin := by
    rw [← hmap, integral_map (measurable_pi_apply s).aemeasurable
      (measurable_of_finite (value σ)).aestronglyMeasurable]
    rfl
  rw [heq, integral_fintype (by fun_prop : Integrable (value σ) coin)]
  simp only [coin, measureReal_def, PMF.toMeasure_uniformOfFintype_apply _
    (measurableSet_singleton _), Fintype.card_unique, Fintype.card_bool, value,
    Fintype.sum_bool]
  norm_num

/-- The finite errors are mutually independent; only the lower-bound example uses this. -/
theorem independent (N : ℕ) (σ : ℝ) : iIndepFun (error (N := N) σ) (law N) :=
  iIndepFun_pi (fun _ => (measurable_of_finite (value σ)).aemeasurable)

/-- An error is independent of the sigma-algebra preceding its own oracle call. -/
theorem independent_past {N : ℕ} (σ : ℝ) (s : Fin N) :
    Indep (MeasurableSpace.comap (error σ s) (inferInstance : MeasurableSpace ℝ)) (past N σ s.val) (law N) := by
  have hi := indep_iSup_of_disjoint
    (fun j => (error_measurable σ j).comap_le) (independent N σ)
    (S := {s}) (T := {j : Fin N | j.val < s.val})
    (by simp : Disjoint ({s} : Set (Fin N)) {j | j.val < s.val})
  change Indep _ (⨆ j : Fin N, ⨆ (_ : j.val < s.val),
    MeasurableSpace.comap (error σ j) (inferInstance : MeasurableSpace ℝ)) _
  simpa only [iSup_singleton, Set.mem_ofPred_eq] using hi

/-- The actual sign stream satisfies the article's martingale assumptions. -/
theorem martingale (N : ℕ) (σ : ℝ) :
    bezout.Probability.MartingaleDifferences N (past N σ) (stream N σ) (law N) where
  adapted s hs := by
    rw [show stream N σ s = error σ ⟨s, hs⟩ by funext ω; simp [stream, hs]]
    have hle : MeasurableSpace.comap (error σ (⟨s, hs⟩ : Fin N)) (inferInstance : MeasurableSpace ℝ) ≤
        past N σ (s + 1) :=
      le_iSup_of_le (⟨s, hs⟩ : Fin N) (le_iSup_of_le (Nat.lt_succ_self s) le_rfl)
    exact (comap_measurable (error σ ⟨s, hs⟩)).stronglyMeasurable.mono hle
  squareIntegrable s hs := by
    rw [show stream N σ s = error σ ⟨s, hs⟩ by funext ω; simp [stream, hs]]
    apply MemLp.of_bound ((error_measurable σ ⟨s, hs⟩).stronglyMeasurable.aestronglyMeasurable)
      |σ|
    exact Eventually.of_forall fun ω => by
      simp only [error, value]
      split <;> simp
  centered s hs := by
    rw [show stream N σ s = error σ ⟨s, hs⟩ by funext ω; simp [stream, hs]]
    have hi := condExp_indep_eq (error_measurable σ ⟨s, hs⟩).comap_le
      ((past N σ).le s) (comap_measurable (error σ ⟨s, hs⟩)).stronglyMeasurable
      (independent_past σ ⟨s, hs⟩)
    change _ =ᵐ[law N] (fun _ => 0)
    simpa only [error_integral] using hi

/-- The conditional variance is exactly `sigma^2`, including at zero noise. -/
theorem conditional_variance (N : ℕ) (σ : ℝ) (s : ℕ) (hs : s < N) :
    (law N)[fun ω => ‖stream N σ s ω‖ ^ 2 | past N σ s] = fun _ => σ ^ 2 := by
  have heq : (fun ω => ‖stream N σ s ω‖ ^ 2) = fun _ => σ ^ 2 := by
    funext ω
    simpa only [stream, hs, dite_true] using error_norm_sq σ ⟨s, hs⟩ ω
  rw [heq, condExp_const ((past N σ).le s)]

end
end bezout.Probability.Signs
