import polyak.Energy.Fourier
import polyak.Energy.Slack
import Mathlib.Algebra.BigOperators.Intervals

/-!
Article: Appendix A, the cutoff argument in Lemma energy.
Use: compare a finite real-Hilbert autocorrelation with the local quadratic terms
of an untruncated trajectory. All discrepancies are controlled by boundary energy.
Proof: exact finite reindexing and Young's inequality; there are no infinite sums.
-/

noncomputable section

namespace polyak.Energy

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Article: finitely supported sequence obtained by setting a trajectory to zero off S. -/
def cutoff (S : Finset ℤ) (f : ℤ → E) (k : ℤ) : E := if k ∈ S then f k else 0

/-- Article: autocorrelation written directly over a finite support of integers. -/
def finiteCorrelation (S : Finset ℤ) (f : ℤ → E) (n : ℤ) : ℝ :=
  ∑ a ∈ S, ∑ b ∈ S, if b-a = n then inner ℝ (f a) (f b) else 0

/-- Article: identification with the Hilbert Parseval autocorrelation. -/
theorem integerCorrelation_subtype (S : Finset ℤ) (f : ℤ → E) (n : ℤ) :
    integerCorrelation (fun k : S => (k : ℤ)) (fun k : S => f k) n =
      finiteCorrelation S f n := by
  classical
  unfold integerCorrelation finiteCorrelation
  change (∑ a : S, ∑ b : S, if (b : ℤ)-(a : ℤ) = n then
    inner ℝ (f a) (f b) else 0) = _
  rw [Finset.sum_coe_sort S (fun a => ∑ b : S, if (b : ℤ)-a = n then
    inner ℝ (f a) (f b) else 0)]
  apply Finset.sum_congr rfl
  intro a _
  exact Finset.sum_coe_sort S (fun b => if b-a = n then inner ℝ (f a) (f b) else 0)

/-- Article: for a fixed first index there is precisely one possible second correlation index. -/
theorem finiteCorrelation_eq_single_sum (S : Finset ℤ) (f : ℤ → E) (n : ℤ) :
    finiteCorrelation S f n =
      ∑ a ∈ S, if a+n ∈ S then inner ℝ (f a) (f (a+n)) else 0 := by
  classical
  unfold finiteCorrelation
  apply Finset.sum_congr rfl
  intro a _
  simp only [show ∀ b : ℤ, b-a = n ↔ b = a+n by intro b; omega]
  exact Finset.sum_ite_eq' S (a+n) (fun b => inner ℝ (f a) (f b))

/-- Article: the cutoff inner product is zero unless both sampled indices belong to its support. -/
theorem inner_cutoff (S : Finset ℤ) (f : ℤ → E) (a b : ℤ) :
    inner ℝ (cutoff S f a) (cutoff S f b) =
      if a ∈ S ∧ b ∈ S then inner ℝ (f a) (f b) else 0 := by
  classical
  by_cases ha : a ∈ S <;> by_cases hb : b ∈ S <;>
    simp [cutoff, ha, hb]

/-- Article: the complete cutoff correlation is a sum of translated local terms.
Use: T may be any finite set containing all centers that can contribute.
Proof: translate the unique possible first correlation index by a. -/
theorem finiteCorrelation_eq_center_sum (S T : Finset ℤ) (f : ℤ → E) (a b : ℤ)
    (hcover : ∀ l ∈ S, l-a ∈ T) :
    finiteCorrelation S f (b-a) =
      ∑ k ∈ T, inner ℝ (cutoff S f (k+a)) (cutoff S f (k+b)) := by
  classical
  rw [finiteCorrelation_eq_single_sum]
  simp_rw [inner_cutoff]
  have hzero : (∑ k ∈ T, if k+a ∈ S ∧ k+b ∈ S then
      inner ℝ (f (k+a)) (f (k+b)) else 0) =
      ∑ k ∈ T.filter (fun k => k+a ∈ S),
        if k+b ∈ S then inner ℝ (f (k+a)) (f (k+b)) else 0 := by
    rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro k _
    split_ifs <;> simp_all
  rw [hzero]
  apply Finset.sum_bij (fun l _ => l-a)
  · intro l hl
    exact Finset.mem_filter.mpr ⟨hcover l hl, by simpa using hl⟩
  · intro l₁ _ l₂ _ he
    omega
  · intro k hk
    have hk' := Finset.mem_filter.mp hk
    refine ⟨k+a, hk'.2, ?_⟩
    omega
  · intro l _
    simp only [sub_add_cancel, show l-a+b = l+(b-a) by omega]

/-- Article: translating an indicator sum cannot exceed the energy on its target boundary set. -/
theorem sum_shift_indicator_le (T B : Finset ℤ) {b : ℤ → ℝ}
    (hb : ∀ k, 0 ≤ b k) (a : ℤ) :
    (∑ k ∈ T, if k+a ∈ B then b (k+a) else 0) ≤ ∑ l ∈ B, b l := by
  classical
  rw [← Finset.sum_filter]
  have hinj : Set.InjOn (fun k : ℤ => k+a) ↑(T.filter (fun k => k+a ∈ B)) := by
    intro k₁ _ k₂ _ he
    dsimp at he
    omega
  rw [← Finset.sum_image hinj]
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro l hl
    obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp hl
    exact (Finset.mem_filter.mp hk).2
  · intro l _ _
    exact hb l

/-- Article: a single local/cutoff discrepancy is supported at the boundary.
Use: abstract form separating the finite-set bookkeeping from interval geometry. -/
theorem abs_cutoff_discrepancy_le (S B : Finset ℤ) (f : ℤ → E) (k a b : ℤ)
    (hboundary : ¬ (k ∈ S ↔ k+a ∈ S ∧ k+b ∈ S) → k+a ∈ B ∧ k+b ∈ B) :
    |(if k ∈ S then inner ℝ (f (k+a)) (f (k+b)) else 0) -
      inner ℝ (cutoff S f (k+a)) (cutoff S f (k+b))| ≤
      ((if k+a ∈ B then ‖f (k+a)‖^2 else 0) +
        (if k+b ∈ B then ‖f (k+b)‖^2 else 0)) / 2 := by
  classical
  rw [inner_cutoff]
  by_cases heq : k ∈ S ↔ k+a ∈ S ∧ k+b ∈ S
  · have he : (if k ∈ S then inner ℝ (f (k+a)) (f (k+b)) else 0) =
        if k+a ∈ S ∧ k+b ∈ S then inner ℝ (f (k+a)) (f (k+b)) else 0 := by
      simp only [heq]
    rw [he, sub_self, abs_zero]
    positivity
  · obtain ⟨ha, hb⟩ := hboundary heq
    simp only [ha, hb, ite_true]
    by_cases hk : k ∈ S
    · have hn : ¬ (k+a ∈ S ∧ k+b ∈ S) := by tauto
      simpa [hk, hn] using abs_inner_le_half_sq (f (k+a)) (f (k+b))
    · have hy : k+a ∈ S ∧ k+b ∈ S := by tauto
      simpa [hk, hy] using abs_inner_le_half_sq (f (k+a)) (f (k+b))

/-- Article: the error of a complete finite autocorrelation is bounded by boundary energy.
Proof: sum the pointwise cutoff discrepancies and use injectivity of both translations. -/
theorem abs_local_sum_sub_finiteCorrelation_le (S T B : Finset ℤ) (f : ℤ → E)
    (a b : ℤ) (hST : S ⊆ T) (hcover : ∀ l ∈ S, l-a ∈ T)
    (hboundary : ∀ k ∈ T,
      ¬ (k ∈ S ↔ k+a ∈ S ∧ k+b ∈ S) → k+a ∈ B ∧ k+b ∈ B) :
    |(∑ k ∈ S, inner ℝ (f (k+a)) (f (k+b))) -
      finiteCorrelation S f (b-a)| ≤ ∑ l ∈ B, ‖f l‖^2 := by
  classical
  rw [finiteCorrelation_eq_center_sum S T f a b hcover]
  have hext : (∑ k ∈ S, inner ℝ (f (k+a)) (f (k+b))) =
      ∑ k ∈ T, if k ∈ S then inner ℝ (f (k+a)) (f (k+b)) else 0 := by
    rw [← Finset.sum_filter]
    have hfilter : T.filter (fun k => k ∈ S) = S := by
      ext k
      simp only [Finset.mem_filter]
      exact ⟨fun hk => hk.2, fun hk => ⟨hST hk, hk⟩⟩
    rw [hfilter]
  rw [hext, ← Finset.sum_sub_distrib]
  calc
    _ ≤ ∑ k ∈ T, |(if k ∈ S then inner ℝ (f (k+a)) (f (k+b)) else 0) -
        inner ℝ (cutoff S f (k+a)) (cutoff S f (k+b))| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ k ∈ T, ((if k+a ∈ B then ‖f (k+a)‖^2 else 0) +
        (if k+b ∈ B then ‖f (k+b)‖^2 else 0)) / 2 := by
      exact Finset.sum_le_sum (fun k hk => abs_cutoff_discrepancy_le S B f k a b
        (hboundary k hk))
    _ = ((∑ k ∈ T, if k+a ∈ B then ‖f (k+a)‖^2 else 0) +
        ∑ k ∈ T, if k+b ∈ B then ‖f (k+b)‖^2 else 0) / 2 := by
      rw [← Finset.sum_div, Finset.sum_add_distrib]
    _ ≤ ((∑ l ∈ B, ‖f l‖^2) + ∑ l ∈ B, ‖f l‖^2) / 2 := by
      exact div_le_div_of_nonneg_right (add_le_add
        (sum_shift_indicator_le T B (fun l => sq_nonneg ‖f l‖) a)
        (sum_shift_indicator_le T B (fun l => sq_nonneg ‖f l‖) b)) (by norm_num)
    _ = _ := by ring

end polyak.Energy
