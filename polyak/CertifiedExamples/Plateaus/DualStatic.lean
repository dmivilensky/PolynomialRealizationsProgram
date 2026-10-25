import polyak.CertifiedExamples.Plateaus.DualSource

/-! Finite signed-lag bookkeeping and normalization for the two actual duals. -/
noncomputable section
namespace polyak.CertifiedExamples.Plateaus
open scoped BigOperators

theorem row18_reps_pos : ∀i,0<reps18 i := by decide

theorem row18_reps_lt : ∀i,reps18 i<18 := by decide

theorem row18_reps_injective : Function.Injective reps18 := by decide

theorem row18_first_nonzero : ∀i,first18 i≠0 := by decide

theorem row18_first_mod : ∀i,first18 i%18=reps18 i := by decide

theorem row18_lifts_mod : ∀i,lifts18 i%18=reps18 i := by decide

theorem row18_lag_one : (1:ℤ)∈lags18 := by decide

theorem row18_lags_nonzero : ∀n∈lags18,n≠0 := by
  intro n hn
  simp only [lags18,Finset.mem_insert,Finset.mem_singleton] at hn
  rcases hn with h|h|h|h <;> subst n <;> norm_num

theorem row18_classes : ∀n∈lags18,n%18=0 ∨∃i,n%18=reps18 i := by
  intro n hn
  simp only [lags18,Finset.mem_insert,Finset.mem_singleton] at hn
  rcases hn with h|h|h|h
  · subst n
    exact Or.inr ⟨0,by decide⟩
  · subst n
    exact Or.inr ⟨0,by decide⟩
  · subst n
    exact Or.inr ⟨1,by decide⟩
  · subst n
    exact Or.inr ⟨1,by decide⟩

theorem row18_class_pair : ∀i,∃n₁∈lags18,∃n₂∈lags18,
    n₁≠n₂ ∧ n₁%18=reps18 i ∧ n₂%18=reps18 i := by
  intro i
  fin_cases i
  · exact ⟨1,by decide,19,by decide,by decide,by decide,by decide⟩
  · exact ⟨-4,by decide,14,by decide,by decide,by decide,by decide⟩

theorem row18_dual_sum (hμ : (∑i,mu18 i)=1) : (∑n∈lags18,dual18 n)=1 := by
  calc
    (∑n∈lags18,dual18 n)=∑i,weights18 i := by
      simpa only [mul_one] using dual18_weighted_sum (fun _=>1)
    _=∑i,mu18 i := by
      norm_num [weights18,Fin.sum_univ_succ]
      ring
    _=1 := hμ

theorem row18_dual_pos (hw : ∀i,0<weights18 i) : ∀n∈lags18,0<dual18 n := by
  intro n hn
  simp only [lags18,Finset.mem_insert,Finset.mem_singleton] at hn
  rcases hn with h|h|h|h
  · subst n
    simpa [dual18] using hw 0
  · subst n
    simpa [dual18] using hw 1
  · subst n
    simpa [dual18] using hw 2
  · subst n
    simpa [dual18] using hw 3

theorem row21_reps_pos : ∀i,0<reps21 i := by decide

theorem row21_reps_lt : ∀i,reps21 i<21 := by decide

theorem row21_reps_injective : Function.Injective reps21 := by decide

theorem row21_first_nonzero : ∀i,first21 i≠0 := by decide

theorem row21_first_mod : ∀i,first21 i%21=reps21 i := by decide

theorem row21_lifts_mod : ∀i,lifts21 i%21=reps21 i := by decide

theorem row21_lag_one : (1:ℤ)∈lags21 := by decide

theorem row21_lags_nonzero : ∀n∈lags21,n≠0 := by
  intro n hn
  simp only [lags21,Finset.mem_insert,Finset.mem_singleton] at hn
  rcases hn with h|h|h|h|h|h <;> subst n <;> norm_num

theorem row21_classes : ∀n∈lags21,n%21=0 ∨∃i,n%21=reps21 i := by
  intro n hn
  simp only [lags21,Finset.mem_insert,Finset.mem_singleton] at hn
  rcases hn with h|h|h|h|h|h
  · subst n
    exact Or.inr ⟨0,by decide⟩
  · subst n
    exact Or.inr ⟨0,by decide⟩
  · subst n
    exact Or.inr ⟨1,by decide⟩
  · subst n
    exact Or.inr ⟨1,by decide⟩
  · subst n
    exact Or.inr ⟨2,by decide⟩
  · subst n
    exact Or.inr ⟨2,by decide⟩

theorem row21_class_pair : ∀i,∃n₁∈lags21,∃n₂∈lags21,
    n₁≠n₂ ∧ n₁%21=reps21 i ∧ n₂%21=reps21 i := by
  intro i
  fin_cases i
  · exact ⟨1,by decide,-20,by decide,by decide,by decide,by decide⟩
  · exact ⟨-12,by decide,9,by decide,by decide,by decide,by decide⟩
  · exact ⟨-4,by decide,-25,by decide,by decide,by decide,by decide⟩

theorem row21_dual_sum (hμ : (∑i,mu21 i)=1) : (∑n∈lags21,dual21 n)=1 := by
  calc
    (∑n∈lags21,dual21 n)=∑i,weights21 i := by
      simpa only [mul_one] using dual21_weighted_sum (fun _=>1)
    _=∑i,mu21 i := by
      norm_num [weights21,Fin.sum_univ_succ]
      ring
    _=1 := hμ

theorem row21_dual_pos (hw : ∀i,0<weights21 i) : ∀n∈lags21,0<dual21 n := by
  intro n hn
  simp only [lags21,Finset.mem_insert,Finset.mem_singleton] at hn
  rcases hn with h|h|h|h|h|h
  · subst n
    simpa [dual21] using hw 0
  · subst n
    simpa [dual21] using hw 1
  · subst n
    simpa [dual21] using hw 2
  · subst n
    simpa [dual21] using hw 3
  · subst n
    simpa [dual21] using hw 4
  · subst n
    simpa [dual21] using hw 5

end polyak.CertifiedExamples.Plateaus
