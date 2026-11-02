import krylov.LotkaVolterra.GlobalBoundedODE

/-!
Two-sided Grönwall estimate for actual global scalar solutions. The negative
time half follows by reversing both time and the vector field. Source:
mathlib's Grönwall estimate, with no assumed global flow object.
-/
namespace krylov.LotkaVolterra
noncomputable section
open Set
open scoped NNReal

theorem global_solution_dist_bound {F : ℝ → ℝ → ℝ} {K : ℝ≥0}
    (hLip : ∀ t, LipschitzWith K (F t)) {e f : ℝ → ℝ}
    (he : ∀ t, HasDerivAt e (F t (e t)) t)
    (hf : ∀ t, HasDerivAt f (F t (f t)) t) (t : ℝ) :
    dist (e t) (f t) ≤ dist (e 0) (f 0) * Real.exp (K * |t|) := by
  have hforward {F : ℝ → ℝ → ℝ} {e f : ℝ → ℝ}
      (hLip : ∀ t, LipschitzWith K (F t))
      (he : ∀ t, HasDerivAt e (F t (e t)) t)
      (hf : ∀ t, HasDerivAt f (F t (f t)) t)
      {t : ℝ} (ht : 0 ≤ t) :
      dist (e t) (f t) ≤ dist (e 0) (f 0) * Real.exp (K * t) := by
    simpa using dist_le_of_trajectories_ODE hLip
      (HasDerivAt.continuousOn fun u _ ↦ he u)
      (fun u _ ↦ (he u).hasDerivWithinAt)
      (HasDerivAt.continuousOn fun u _ ↦ hf u)
      (fun u _ ↦ (hf u).hasDerivWithinAt) le_rfl t ⟨ht, le_rfl⟩
  rcases le_total 0 t with ht | ht
  · simpa [abs_of_nonneg ht] using hforward hLip he hf ht
  · let G : ℝ → ℝ → ℝ := fun t x ↦ -F (-t) x
    have he' (u : ℝ) : HasDerivAt (fun t ↦ e (-t)) (G u (e (-u))) u := by
      simpa [G, Function.comp_def] using (he (-u)).comp u (hasDerivAt_neg u)
    have hf' (u : ℝ) : HasDerivAt (fun t ↦ f (-t)) (G u (f (-u))) u := by
      simpa [G, Function.comp_def] using (hf (-u)).comp u (hasDerivAt_neg u)
    have hG (u : ℝ) : LipschitzWith K (G u) := (hLip (-u)).neg
    simpa [abs_of_nonpos ht] using hforward hG he' hf' (neg_nonneg.mpr ht)

end
end krylov.LotkaVolterra
