import polyak.GapEdges.Tips.ThreeLag

/-! The constructed small perturbation supplies every primary certificate
condition, with the literal three signed lags of the article. -/
noncomputable section
namespace polyak.GapEdges.Tip
open General Levels ModeLocking Set
open scoped BigOperators
variable {q : Tuning} {k : ℕ} (T : Tip q k)
include T

theorem exists_certificate : ∃ C : FareyPlateau.Edge.Certificate q 0 1 k,
    C.lags = lags k := by
  classical
  obtain ⟨ε, hε, hεhalf, ⟨B⟩⟩ := T.exists_negative_cover
  have hk := T.period_ge
  have h₁ : (1 : ℤ) ≠ 1 + (k : ℤ) := by omega
  have h₂ : (1 : ℤ) ≠ 1 - (k : ℤ) := by omega
  have h₃ : 1 + (k : ℤ) ≠ 1 - (k : ℤ) := by omega
  have hmem₁ : (1 : ℤ) ∉ ({1 + (k : ℤ), 1 - (k : ℤ)} : Finset ℤ) := by simp [h₁, h₂]
  have hmem₂ : 1 + (k : ℤ) ∉ ({1 - (k : ℤ)} : Finset ℤ) := by simp [h₃]
  have hwsum : ∑ n ∈ lags k, weight ε n = 1 := by
    simp only [lags, Finset.sum_insert hmem₁, Finset.sum_insert hmem₂, Finset.sum_singleton,
      weight, ite_true, ite_eq_right h₁.symm, ite_eq_right h₂.symm]
    ring
  have hcurv : ∀ z ∈ ({0, (T.frequency : ℝ)} : Finset ℝ),
      deriv^[2] (finiteSymbol q 0 (lags k) (weight ε)) z < 0 := by
    intro z hz
    have hh := B.local_bound z hz z (B.centers z hz)
      (by simp only [sub_self, abs_zero]; exact B.radius_pos.le)
    rw [iteratedDeriv_eq_iterate] at hh
    exact hh.trans_lt (neg_neg_of_pos B.curvature_pos)
  let C : FareyPlateau.Edge.Certificate q 0 1 k := {
    period_ge := hk
    numerator_pos := by norm_num
    numerator_lt := by omega
    inverse := 1
    inverse_pos := by norm_num
    inverse_lt := by omega
    inverse_mod := by simp
    phase := T.shifted_phase
    lags := lags k
    nonzero := by
      intro n hn
      simp only [lags, Finset.mem_insert, Finset.mem_singleton] at hn
      rcases hn with rfl | rfl | rfl <;> omega
    classes := fun n hn => Or.inr (T.lag_mem_classes hn)
    weight := weight ε
    weight_pos := by
      intro n _
      unfold weight
      split_ifs
      · linarith
      · exact hε
    weight_sum := hwsum
    pair := ⟨1, by simp [lags], 1 + (k : ℤ), by simp [lags], h₁,
      T.lag_mem_classes (by simp [lags]), T.lag_mem_classes (by simp [lags])⟩
    strict := by
      intro x hx hxπ hn
      apply B.strict ⟨hx.le, hxπ⟩
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
      exact ⟨hx.ne', hn⟩
    curvature := hcurv T.frequency (by simp)
    endpoint := by
      have hh := hcurv 0 (by simp)
      rw [finiteSymbol_second_zero] at hh
      linarith }
  exact ⟨C, rfl⟩

theorem regular_at_tip : ∃ D : RegularData q 0 k,
    Set.range D.atoms = {T.frequency} ∧ D.lags = lags k := by
  obtain ⟨C, hC⟩ := T.exists_certificate
  refine ⟨C.regularData, ?_, hC⟩
  ext ω
  simp only [FareyPlateau.Edge.Certificate.regularData, Set.mem_range, Set.mem_singleton_iff]
  constructor
  · rintro ⟨i, rfl⟩
    rfl
  · intro h
    exact ⟨0, h.symm⟩

theorem sigma_at_tip : Threshold.sigma q = 0 := by
  obtain ⟨C, _⟩ := T.exists_certificate
  exact C.sigma_eq

end polyak.GapEdges.Tip
