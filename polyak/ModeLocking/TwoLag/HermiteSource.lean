import polyak.ModeLocking.TwoLag.TangencyEquivalence

/-! The Hermite quadratic and compatibility equation follow from the
original symbol conditions, uniformly in K. -/
noncomputable section
namespace polyak.ModeLocking.TwoLag
open General Levels

theorem Xi_deriv_coefficients (q : Tuning) (c : ℝ) :
    deriv q.Xi c=(Chart.coefficients q).c1+2*(Chart.coefficients q).c2*c := by
  rw [(Xi_hasDerivAt q c).deriv]
  dsimp [Chart.coefficients]
  ring

/-- Values and first slopes are forced, as is the displayed all-K equation. -/
theorem Hermite_of_lag_tangencies (q : Tuning) {K : ℕ} (hK : 2≤K) {a b : ℝ}
    (ha : 0<a) (hb : 0<b) (u : Fin 2→Frequency)
    (hu : ∀i,0<(u i : ℝ) ∧ (u i : ℝ)<Real.pi)
    (hne : Real.cos (u 0 : ℝ)≠Real.cos (u 1 : ℝ))
    (H : LagTangencies q K a b u) :
    (∀i,deriv q.Xi (Real.cos (u i : ℝ))=deriv (Psi K (b/a)) (Real.cos (u i : ℝ))) ∧
    G K (b/a) (Real.cos (u 0 : ℝ)) (Real.cos (u 1 : ℝ))=0 := by
  have R := (double_tangencies_iff q hK ha hb u hu).mp H
  have hs (i : Fin 2) := contact_slopes q K (div_pos hb ha).le
    (cos_mem_open (hu i)) R.bound (R.value i)
  exact ⟨hs,G_eq_zero q K (b/a) hne (R.value 0) (R.value 1) (hs 0) (hs 1)⟩

/-- The value at each contact and slope at the first determine the
quadratic uniquely, in the literal coefficient chart of the article. -/
theorem Hermite_quadratic_unique (q : Tuning) (K : ℕ) {r c₁ c₂ : ℝ}
    (hc : c₁≠c₂) (hv₁ : q.Xi c₁=Psi K r c₁) (hv₂ : q.Xi c₂=Psi K r c₂)
    (hs : deriv q.Xi c₁=deriv (Psi K r) c₁)
    {A B D : ℝ}
    (h₁ : A*c₁^2+B*c₁+D=Psi K r c₁)
    (h₂ : A*c₂^2+B*c₂+D=Psi K r c₂)
    (h₃ : 2*A*c₁+B=deriv (Psi K r) c₁) :
    A=(Chart.coefficients q).c2 ∧ B=(Chart.coefficients q).c1 ∧ D=(Chart.coefficients q).c0 := by
  have hx : A*c₁^2+B*c₁+D=(Chart.coefficients q).c2*c₁^2+
      (Chart.coefficients q).c1*c₁+(Chart.coefficients q).c0 := by
    rw [h₁,←hv₁,←Chart.eval_coefficients]
    unfold Chart.Coefficients.eval
    ring
  have hy : A*c₂^2+B*c₂+D=(Chart.coefficients q).c2*c₂^2+
      (Chart.coefficients q).c1*c₂+(Chart.coefficients q).c0 := by
    rw [h₂,←hv₂,←Chart.eval_coefficients]
    unfold Chart.Coefficients.eval
    ring
  have hz : 2*A*c₁+B=2*(Chart.coefficients q).c2*c₁+(Chart.coefficients q).c1 := by
    rw [h₃,←hs,Xi_deriv_coefficients]
    ring
  exact quadratic_Hermite_unique hc hx hy hz

end polyak.ModeLocking.TwoLag
