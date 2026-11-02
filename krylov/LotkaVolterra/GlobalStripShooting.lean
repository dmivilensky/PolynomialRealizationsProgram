import krylov.LotkaVolterra.GlobalBoundedODE
import krylov.LotkaVolterra.Barrier
import Mathlib.Topology.Compactness.Compact

/-!
Compact shooting for an outward-pointing scalar strip. This is the common
existence mechanism for the endpoint graph and (after time reversal) the
subcritical saddle graph. The curve in the conclusion is constructed by
Picard--Lindelöf and Cantor intersection, not supplied as a hypothesis.

Source: finite terminal-value shooting, strict first-contact barriers,
Grönwall continuous dependence, and Cantor's nested compact-set theorem.
-/
namespace krylov.LotkaVolterra
noncomputable section
open Set
open scoped NNReal Topology

/-- Outward signs on the strip walls leave at least one actual globally
bounded trajectory in the strip. -/
theorem exists_forward_strip_solution {f : ℝ → ℝ → ℝ} {L K : ℝ≥0}
    (hLip : ∀ t, LipschitzWith K (f t)) (hcont : ∀ x, Continuous (f · x))
    (hbound : ∀ t x, ‖f t x‖ ≤ L) {a b : ℝ} (hab : a < b)
    (ha : ∀ t ≥ 0, f t a < 0) (hb : ∀ t ≥ 0, 0 < f t b) :
    ∃ e : ℝ → ℝ, ∀ t ≥ 0, e t ∈ Icc a b ∧ HasDerivAt e (f t (e t)) t := by
  have hex (T ξ : ℝ) := exists_global_solution_at_of_bounded_lipschitz hLip hcont hbound T ξ
  choose A hA₀ hA using hex
  let Φ : ℝ → ℝ → ℝ := A 0
  have hΦ₀ (ξ : ℝ) : Φ ξ 0 = ξ := hA₀ 0 ξ
  have hΦ (ξ t : ℝ) : HasDerivAt (Φ ξ) (f t (Φ ξ t)) t := hA 0 ξ t
  have huniq {e : ℝ → ℝ} {ξ : ℝ}
      (he : ∀ t, HasDerivAt e (f t (e t)) t) (he₀ : e 0 = ξ) : e = Φ ξ := by
    apply ODE_solution_unique_univ (v := f) (s := fun _ ↦ univ) (t₀ := 0)
      (fun t ↦ (hLip t).lipschitzOnWith) (fun t ↦ ⟨he t, mem_univ _⟩)
      (fun t ↦ ⟨hΦ ξ t, mem_univ _⟩)
    exact he₀.trans (hΦ₀ ξ).symm
  have hΦcont {t : ℝ} (ht : 0 ≤ t) : Continuous (fun ξ ↦ Φ ξ t) := by
    have hLipΦ : LipschitzWith (Real.toNNReal (Real.exp (K * t))) (fun ξ ↦ Φ ξ t) := by
      apply LipschitzWith.of_dist_le_mul
      intro ξ η
      have hh := dist_le_of_trajectories_ODE hLip
        (HasDerivAt.continuousOn fun u _ ↦ hΦ ξ u)
        (fun u _ ↦ (hΦ ξ u).hasDerivWithinAt)
        (HasDerivAt.continuousOn fun u _ ↦ hΦ η u)
        (fun u _ ↦ (hΦ η u).hasDerivWithinAt)
        (show dist (Φ ξ 0) (Φ η 0) ≤ dist ξ η by rw [hΦ₀, hΦ₀]) t ⟨ht, le_rfl⟩
      simpa [Real.coe_toNNReal, mul_comm, max_eq_left (Real.exp_pos _).le] using hh
    exact hLipΦ.continuous
  have hterminal {T t : ℝ} (ht : 0 ≤ t) (htT : t ≤ T) : A T ((a + b) / 2) t ∈ Ioo a b := by
    let e : ℝ → ℝ := A T ((a + b) / 2)
    have he₀ : e T = (a + b) / 2 := hA₀ _ _
    have he (u : ℝ) := hA T ((a + b) / 2) u
    have hV (u : ℝ) (hu : u ∈ Icc 0 (T - t)) : 0 ≤ T - u := by linarith [hu.2]
    have hf (u : ℝ) : HasDerivAt (fun u ↦ e (T - u) - a)
        (-f (T - u) (e (T - u))) u := by
      simpa using ((he (T - u)).comp u ((hasDerivAt_id u).const_sub T)).sub_const a
    have hg (u : ℝ) : HasDerivAt (fun u ↦ b - e (T - u))
        (f (T - u) (e (T - u))) u := by
      simpa using ((he (T - u)).comp u ((hasDerivAt_id u).const_sub T)).const_sub b
    have hh := pair_positive_invariant (sub_nonneg.mpr htT)
      (fun u _ ↦ hf u) (fun u _ ↦ hg u)
      (show 0 < e (T - 0) - a by rw [sub_zero, he₀]; linarith)
      (show 0 < b - e (T - 0) by rw [sub_zero, he₀]; linarith)
      (fun u hu heq _ ↦ ?_) (fun u hu heq _ ↦ ?_)
    · have hid : T - (T - t) = t := by ring
      rw [hid] at hh
      exact ⟨by linarith [hh.1], by linarith [hh.2]⟩
    · have heq' : e (T - u) = a := by linarith
      rw [heq']
      exact neg_pos.mpr (ha _ (hV u hu))
    · have heq' : e (T - u) = b := by linarith
      rw [heq']
      exact hb _ (hV u hu)
  let C : ℕ → Set ℝ := fun n ↦
    Icc a b ∩ {ξ | ∀ t ∈ Icc (0 : ℝ) n, Φ ξ t ∈ Icc a b}
  have hCclosed (n : ℕ) : IsClosed (C n) := by
    apply isClosed_Icc.inter
    simp only [ofPred_forall]
    exact isClosed_iInter fun t ↦ isClosed_iInter fun ht ↦
      isClosed_Icc.preimage (hΦcont ht.1)
  have hCnonempty (n : ℕ) : (C n).Nonempty := by
    let e := A n ((a + b) / 2)
    have heq : e = Φ (e 0) := huniq (hA _ _) rfl
    refine ⟨e 0, ?_, fun t ht ↦ ?_⟩
    · have hh := hterminal (T := n) (t := 0) le_rfl (Nat.cast_nonneg n)
      exact ⟨hh.1.le, hh.2.le⟩
    · rw [← heq]
      have hh := hterminal ht.1 ht.2
      exact ⟨hh.1.le, hh.2.le⟩
  have hCmono : Antitone C := by
    intro m n hmn ξ hξ
    exact ⟨hξ.1, fun t ht ↦ hξ.2 t ⟨ht.1, ht.2.trans (by exact_mod_cast hmn)⟩⟩
  obtain ⟨ξ, hξ⟩ := IsCompact.nonempty_iInter_of_sequence_nonempty_isCompact_isClosed
    C (fun n ↦ hCmono (Nat.le_succ n)) hCnonempty
    (isCompact_Icc.of_isClosed_subset (hCclosed 0) fun _ h ↦ h.1) hCclosed
  refine ⟨Φ ξ, fun t ht ↦ ⟨?_, hΦ ξ t⟩⟩
  exact (mem_iInter.mp hξ ⌈t⌉₊).2 t ⟨ht, Nat.le_ceil t⟩

end
end krylov.LotkaVolterra
