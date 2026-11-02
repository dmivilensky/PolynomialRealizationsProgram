import krylov.LotkaVolterra.GlobalFlowEstimate
import krylov.LotkaVolterra.Barrier
import Mathlib.Topology.Compactness.Compact

/-!
Whole-line compact shooting for an outward-pointing scalar strip. This
extends the half-line construction to all real graph parameters, allowing
the subcritical stable branches to cover their full state ranges.

Source: Picard--Lindelöf, two-sided Grönwall, strict first-contact barriers,
and Cantor's nested compact-set theorem, all used on actual solutions.
-/
namespace krylov.LotkaVolterra
noncomputable section
open Set
open scoped NNReal Topology

theorem exists_whole_strip_solution {F : ℝ → ℝ → ℝ} {L K : ℝ≥0}
    (hLip : ∀ t, LipschitzWith K (F t)) (hcont : ∀ x, Continuous (F · x))
    (hbound : ∀ t x, ‖F t x‖ ≤ L) {a b : ℝ} (hab : a < b)
    (ha : ∀ t, F t a < 0) (hb : ∀ t, 0 < F t b) :
    ∃ e : ℝ → ℝ, ∀ t, e t ∈ Icc a b ∧ HasDerivAt e (F t (e t)) t := by
  have hex (T ξ : ℝ) := exists_global_solution_at_of_bounded_lipschitz hLip hcont hbound T ξ
  choose A hA₀ hA using hex
  let Φ : ℝ → ℝ → ℝ := A 0
  have hΦ₀ (ξ : ℝ) : Φ ξ 0 = ξ := hA₀ 0 ξ
  have hΦ (ξ t : ℝ) : HasDerivAt (Φ ξ) (F t (Φ ξ t)) t := hA 0 ξ t
  have huniq {e : ℝ → ℝ} {ξ : ℝ}
      (he : ∀ t, HasDerivAt e (F t (e t)) t) (he₀ : e 0 = ξ) : e = Φ ξ := by
    apply ODE_solution_unique_univ (v := F) (s := fun _ ↦ univ) (t₀ := 0)
      (fun t ↦ (hLip t).lipschitzOnWith) (fun t ↦ ⟨he t, mem_univ _⟩)
      (fun t ↦ ⟨hΦ ξ t, mem_univ _⟩)
    exact he₀.trans (hΦ₀ ξ).symm
  have hΦcont (t : ℝ) : Continuous (fun ξ ↦ Φ ξ t) := by
    have hh : LipschitzWith (Real.toNNReal (Real.exp (K * |t|))) (fun ξ ↦ Φ ξ t) := by
      apply LipschitzWith.of_dist_le_mul
      intro ξ η
      simpa [hΦ₀, Real.coe_toNNReal, max_eq_left (Real.exp_pos _).le, mul_comm] using
        global_solution_dist_bound hLip (hΦ ξ) (hΦ η) t
    exact hh.continuous
  have hterminal {T t : ℝ} (htT : t ≤ T) : A T ((a + b) / 2) t ∈ Ioo a b := by
    let e : ℝ → ℝ := A T ((a + b) / 2)
    have he₀ : e T = (a + b) / 2 := hA₀ _ _
    have he (u : ℝ) := hA T ((a + b) / 2) u
    have hf (u : ℝ) : HasDerivAt (fun u ↦ e (T - u) - a)
        (-F (T - u) (e (T - u))) u := by
      simpa using ((he (T - u)).comp u ((hasDerivAt_id u).const_sub T)).sub_const a
    have hg (u : ℝ) : HasDerivAt (fun u ↦ b - e (T - u))
        (F (T - u) (e (T - u))) u := by
      simpa using ((he (T - u)).comp u ((hasDerivAt_id u).const_sub T)).const_sub b
    have hh := pair_positive_invariant (sub_nonneg.mpr htT)
      (fun u _ ↦ hf u) (fun u _ ↦ hg u)
      (show 0 < e (T - 0) - a by rw [sub_zero, he₀]; linarith)
      (show 0 < b - e (T - 0) by rw [sub_zero, he₀]; linarith)
      (fun u _ heq _ ↦ by
        have heq' : e (T - u) = a := by linarith
        rw [heq']; exact neg_pos.mpr (ha _))
      (fun u _ heq _ ↦ by
        have heq' : e (T - u) = b := by linarith
        rw [heq']; exact hb _)
    have hid : T - (T - t) = t := by ring
    rw [hid] at hh
    exact ⟨by linarith [hh.1], by linarith [hh.2]⟩
  let C : ℕ → Set ℝ := fun n ↦
    Icc a b ∩ {ξ | ∀ t ∈ Icc (-(n : ℝ)) n, Φ ξ t ∈ Icc a b}
  have hCclosed (n : ℕ) : IsClosed (C n) := by
    apply isClosed_Icc.inter
    simp only [ofPred_forall]
    exact isClosed_iInter fun t ↦ isClosed_iInter fun _ ↦
      isClosed_Icc.preimage (hΦcont t)
  have hCnonempty (n : ℕ) : (C n).Nonempty := by
    let e := A n ((a + b) / 2)
    have heq : e = Φ (e 0) := huniq (hA _ _) rfl
    refine ⟨e 0, ?_, fun t ht ↦ ?_⟩
    · have hh := hterminal (T := n) (t := 0) (Nat.cast_nonneg n)
      exact ⟨hh.1.le, hh.2.le⟩
    · rw [← heq]
      have hh := hterminal ht.2
      exact ⟨hh.1.le, hh.2.le⟩
  have hCmono : Antitone C := by
    intro m n hmn ξ hξ
    have hmn' : (m : ℝ) ≤ n := by exact_mod_cast hmn
    exact ⟨hξ.1, fun t ht ↦ hξ.2 t ⟨(neg_le_neg hmn').trans ht.1, ht.2.trans hmn'⟩⟩
  obtain ⟨ξ, hξ⟩ := IsCompact.nonempty_iInter_of_sequence_nonempty_isCompact_isClosed
    C (fun n ↦ hCmono (Nat.le_succ n)) hCnonempty
    (isCompact_Icc.of_isClosed_subset (hCclosed 0) fun _ h ↦ h.1) hCclosed
  refine ⟨Φ ξ, fun t ↦ ⟨?_, hΦ ξ t⟩⟩
  have hh := abs_le.mp (Nat.le_ceil |t|)
  exact (mem_iInter.mp hξ ⌈|t|⌉₊).2 t hh

end
end krylov.LotkaVolterra
