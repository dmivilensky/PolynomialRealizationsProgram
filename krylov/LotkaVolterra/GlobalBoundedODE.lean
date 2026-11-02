import Mathlib.Analysis.ODE.ExistUnique
import Mathlib.Algebra.Order.Floor.Ring

/-!
Global existence for a bounded, globally Lipschitz nonautonomous field.

This elementary continuation lemma is used for the clipped scalar shooting
equation of `apC:prop:g1`. Its hypotheses will be verified for that concrete
equation; the polynomial Lotka--Volterra field itself is not globally bounded.

Source: mathlib's Picard--Lindelöf theorem, on successively larger intervals,
and its uniqueness theorem. No maximal-flow or continuation axiom is used.
-/

namespace krylov.LotkaVolterra
noncomputable section
open Set
open scoped NNReal Topology

/-- A globally bounded Lipschitz field has an actual solution at every real
time. Picard--Lindelöf is applied on each finite interval, and uniqueness
glues the resulting curves. No bound on `K * time` is necessary: the
underlying Picard theorem uses a contracting iterate. -/
theorem exists_global_solution_of_bounded_lipschitz_on_balls
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {f : ℝ → E → E} {L : ℝ≥0} (x₀ : E)
    (hLip : ∀ a : ℝ≥0, ∃ K : ℝ≥0, ∀ t, LipschitzOnWith K (f t) (Metric.closedBall x₀ a))
    (hcont : ∀ x, Continuous (f · x))
    (hbound : ∀ t x, ‖f t x‖ ≤ L) :
    ∃ α : ℝ → E, α 0 = x₀ ∧ ∀ t, HasDerivAt α (f t (α t)) t := by
  have hex (n : ℕ) : ∃ α : ℝ → E, α 0 = x₀ ∧
      ∀ t ∈ Ioo (-(n + 1 : ℝ)) (n + 1), HasDerivAt α (f t (α t)) t := by
    let R : ℝ := n + 1
    have hR : 0 < R := by dsimp [R]; positivity
    let a : ℝ≥0 := L * (n + 1)
    obtain ⟨K, hK⟩ := hLip a
    have hPL : IsPicardLindelof f (⟨0, by constructor <;> linarith⟩ : Icc (-R) R)
        x₀ a 0 L K := by
      constructor
      · intro t _
        exact hK t
      · intro x _
        exact (hcont x).continuousOn
      · intro t _ x _
        exact hbound t x
      · simp only [sub_zero, zero_sub, neg_neg, max_self]
        simp [a, R]
    obtain ⟨α, hα₀, hα⟩ := hPL.exists_eq_forall_mem_Icc_hasDerivWithinAt₀
    refine ⟨α, hα₀, fun t ht ↦ ?_⟩
    exact (hα t (Ioo_subset_Icc_self ht)).hasDerivAt (Icc_mem_nhds ht.1 ht.2)
  choose A hA₀ hA using hex
  have hAbound (n : ℕ) {t : ℝ} (ht : t ∈ Ioo (-(n + 1 : ℝ)) (n + 1)) :
      dist (A n t) x₀ ≤ L * |t| := by
    have hAlip : LipschitzOnWith L (A n) (Ioo (-(n + 1 : ℝ)) (n + 1)) :=
      (convex_Ioo _ _).lipschitzOnWith_of_nnnorm_hasDerivWithin_le
        (fun u hu ↦ (hA n u hu).hasDerivWithinAt)
        (fun u _ ↦ by exact_mod_cast hbound u (A n u))
    have hz : (0 : ℝ) ∈ Ioo (-(n + 1 : ℝ)) (n + 1) := by
      constructor <;> linarith [Nat.cast_nonneg (α := ℝ) n]
    simpa [hA₀ n, Real.dist_eq] using hAlip.dist_le_mul t ht 0 hz
  have hcompat (m n : ℕ) {t : ℝ}
      (htm : t ∈ Ioo (-(m + 1 : ℝ)) (m + 1))
      (htn : t ∈ Ioo (-(n + 1 : ℝ)) (n + 1)) : A m t = A n t := by
    let R : ℝ := min (m + 1 : ℝ) (n + 1)
    have hR : 0 < R := lt_min (by positivity) (by positivity)
    have hm : Ioo (-R) R ⊆ Ioo (-(m + 1 : ℝ)) (m + 1) := by
      intro u hu
      exact ⟨lt_of_le_of_lt (neg_le_neg (min_le_left _ _)) hu.1,
        hu.2.trans_le (min_le_left _ _)⟩
    have hn : Ioo (-R) R ⊆ Ioo (-(n + 1 : ℝ)) (n + 1) := by
      intro u hu
      exact ⟨lt_of_le_of_lt (neg_le_neg (min_le_right _ _)) hu.1,
        hu.2.trans_le (min_le_right _ _)⟩
    let a : ℝ≥0 := L * min (m + 1) (n + 1)
    obtain ⟨K, hK⟩ := hLip a
    have hmem (j : ℕ) (hj : Ioo (-R) R ⊆ Ioo (-(j + 1 : ℝ)) (j + 1))
        (u : ℝ) (hu : u ∈ Ioo (-R) R) : A j u ∈ Metric.closedBall x₀ a := by
      apply Metric.mem_closedBall.mpr
      have hRu : |u| ≤ R := (abs_lt.mpr hu).le
      have ha : (a : ℝ) = L * R := by simp [a, R, min_add_add_right]
      rw [ha]
      exact (hAbound j (hj hu)).trans (mul_le_mul_of_nonneg_left hRu L.coe_nonneg)
    apply ODE_solution_unique_of_mem_Ioo (v := f) (s := fun _ ↦ Metric.closedBall x₀ a)
      (fun u _ ↦ hK u) (show (0 : ℝ) ∈ Ioo (-R) R by
        constructor <;> linarith)
      (fun u hu ↦ ⟨hA m u (hm hu), hmem m hm u hu⟩)
      (fun u hu ↦ ⟨hA n u (hn hu), hmem n hn u hu⟩)
      (by rw [hA₀, hA₀])
    exact ⟨by
      have hh : -t < min (m + 1 : ℝ) (n + 1) :=
        lt_min (by linarith [htm.1]) (by linarith [htn.1])
      dsimp [R]
      linarith,
      lt_min htm.2 htn.2⟩
  let N : ℝ → ℕ := fun t ↦ ⌈|t|⌉₊
  have hN (t : ℝ) : t ∈ Ioo (-(N t + 1 : ℝ)) (N t + 1) := by
    have hh : |t| ≤ (N t : ℝ) := Nat.le_ceil _
    have ht := abs_le.mp hh
    constructor <;> linarith [ht.1, ht.2]
  let α : ℝ → E := fun t ↦ A (N t) t
  have heq (n : ℕ) : EqOn α (A n) (Ioo (-(n + 1 : ℝ)) (n + 1)) :=
    fun t ht ↦ hcompat (N t) n (hN t) ht
  refine ⟨α, ?_, fun t ↦ ?_⟩
  · exact hA₀ (N 0)
  · have ht := hN t
    have hev : α =ᶠ[nhds t] A (N t) :=
      Filter.eventually_of_mem (Ioo_mem_nhds ht.1 ht.2) (heq (N t))
    rw [heq (N t) ht]
    exact (hA (N t) t ht).congr_of_eventuallyEq hev

/-- The global Lipschitz special case of the bounded continuation theorem. -/
theorem exists_global_solution_of_bounded_lipschitz
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {f : ℝ → E → E} {L K : ℝ≥0}
    (hLip : ∀ t, LipschitzWith K (f t))
    (hcont : ∀ x, Continuous (f · x))
    (hbound : ∀ t x, ‖f t x‖ ≤ L) (x₀ : E) :
    ∃ α : ℝ → E, α 0 = x₀ ∧ ∀ t, HasDerivAt α (f t (α t)) t :=
  exists_global_solution_of_bounded_lipschitz_on_balls x₀
    (fun _ ↦ ⟨K, fun t ↦ (hLip t).lipschitzOnWith⟩) hcont hbound

/-- Initial time may be prescribed arbitrarily; this is the translated
version used for terminal-value shooting. -/
theorem exists_global_solution_at_of_bounded_lipschitz
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {f : ℝ → E → E} {L K : ℝ≥0}
    (hLip : ∀ t, LipschitzWith K (f t))
    (hcont : ∀ x, Continuous (f · x))
    (hbound : ∀ t x, ‖f t x‖ ≤ L) (t₀ : ℝ) (x₀ : E) :
    ∃ α : ℝ → E, α t₀ = x₀ ∧ ∀ t, HasDerivAt α (f t (α t)) t := by
  obtain ⟨β, hβ₀, hβ⟩ := exists_global_solution_of_bounded_lipschitz
    (L := L) (K := K) (f := fun t x ↦ f (t + t₀) x)
    (fun t ↦ hLip (t + t₀))
    (fun x ↦ (hcont x).comp (continuous_id.add_const t₀))
    (fun t x ↦ hbound (t + t₀) x) x₀
  refine ⟨fun t ↦ β (t - t₀), by simpa using hβ₀, fun t ↦ ?_⟩
  convert (hβ (t - t₀)).scomp t ((hasDerivAt_id t).sub_const t₀) using 1
  · rfl
  · simp

end
end krylov.LotkaVolterra
