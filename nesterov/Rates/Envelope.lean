import nesterov.Stationary.Bounds

/-!
Article: Definition `def:rate` and Lemma `lem:envelope`.
Use: the literal supremum over arbitrary real Hilbert spaces, centered genuine
objectives, free initial states and arbitrary restart times. No restriction to
quadratic, spectral or finite-dimensional examples is built into the definition.
-/
namespace nesterov.Rates
noncomputable section
open scoped BigOperators
open Set

/-- A genuine execution in an arbitrary real Hilbert space. The carrier is
quantified inside the supremum, so the supremum precedes every time limit. -/
structure HilbertRun (M : StationaryMethod) (μ L : ℝ) where
  Carrier : Type
  [normed : NormedAddCommGroup Carrier]
  [inner : InnerProductSpace ℝ Carrier]
  [complete : CompleteSpace Carrier]
  f : Carrier → ℝ
  admissible : polyak.CenteredSmoothStronglyConvex μ L f
  w : ℕ → Carrier
  trajectory : M.IsTrajectory (gradient f) w

attribute [instance] HilbertRun.normed HilbertRun.inner HilbertRun.complete

namespace HilbertRun
variable {M : StationaryMethod} {μ L : ℝ}

def stateNorm (r : HilbertRun M μ L) (k : ℕ) : ℝ := M.stateNorm r.w k

def shift (r : HilbertRun M μ L) (k : ℕ) : HilbertRun M μ L where
  Carrier := r.Carrier
  f := r.f
  admissible := r.admissible
  w n := r.w (k+n)
  trajectory := r.trajectory.shift M k

@[simp] theorem stateNorm_shift (r : HilbertRun M μ L) (k n : ℕ) :
    (r.shift k).stateNorm n = r.stateNorm (k+n) := M.stateNorm_shift r.w k n

theorem gradient_bound (r : HilbertRun M μ L) (x : r.Carrier) :
    ‖gradient r.f x‖ ≤ |L| * ‖x‖ := by
  have h := r.admissible.grad_lipschitz x 0
  simpa only [r.admissible.gradient_zero,sub_zero,abs_of_pos
    (r.admissible.mu_pos.trans r.admissible.mu_lt_L)] using h

theorem stateNorm_le (r : HilbertRun M μ L) (n : ℕ) :
    r.stateNorm n ≤ (M.stepBound L)^n * r.stateNorm 0 :=
  r.trajectory.stateNorm_le M r.gradient_bound n

theorem zero_state_absorbing (r : HilbertRun M μ L) {k : ℕ}
    (hk : r.stateNorm k = 0) (n : ℕ) : r.stateNorm (k+n) = 0 :=
  r.trajectory.zero_state_absorbing M r.gradient_bound hk n

end HilbertRun

/-- Every ratio is taken at a nonzero state. Restart closure accounts for all k. -/
def ratios (M : StationaryMethod) (μ L : ℝ) (n : ℕ) : Set ℝ :=
  {x | ∃ r : HilbertRun M μ L, r.stateNorm 0 ≠ 0 ∧ x=r.stateNorm n/r.stateNorm 0}

/-- Γ(n), with zero inserted solely to make the real supremum nonempty. -/
def envelope (M : StationaryMethod) (μ L : ℝ) (n : ℕ) : ℝ :=
  sSup (insert 0 (ratios M μ L n))

theorem ratios_bddAbove (M : StationaryMethod) (μ L : ℝ) (n : ℕ) :
    BddAbove (insert 0 (ratios M μ L n)) := by
  refine ⟨(M.stepBound L)^n, ?_⟩
  intro x hx
  rcases hx with rfl | ⟨r,hr,rfl⟩
  · exact pow_nonneg (M.stepBound_pos L).le _
  · apply (div_le_iff₀ (lt_of_le_of_ne (M.stateNorm_nonneg r.w 0) (Ne.symm hr))).mpr
    exact r.stateNorm_le n

theorem envelope_nonneg (M : StationaryMethod) (μ L : ℝ) (n : ℕ) :
    0 ≤ envelope M μ L n := le_csSup (ratios_bddAbove M μ L n) (mem_insert _ _)

theorem envelope_le (M : StationaryMethod) (μ L : ℝ) (n : ℕ) :
    envelope M μ L n ≤ (M.stepBound L)^n := by
  apply csSup_le (insert_nonempty _ _)
  intro x hx
  rcases hx with rfl | ⟨r,hr,rfl⟩
  · exact pow_nonneg (M.stepBound_pos L).le _
  · exact (div_le_iff₀ (lt_of_le_of_ne (M.stateNorm_nonneg r.w 0) (Ne.symm hr))).mpr
      (r.stateNorm_le n)

theorem stateNorm_le_envelope {M : StationaryMethod} {μ L : ℝ}
    (r : HilbertRun M μ L) (n : ℕ) :
    r.stateNorm n ≤ envelope M μ L n * r.stateNorm 0 := by
  by_cases hz : r.stateNorm 0=0
  · simpa only [hz,mul_zero,Nat.zero_add] using
      le_of_eq (r.zero_state_absorbing hz n)
  · apply (div_le_iff₀ (lt_of_le_of_ne (M.stateNorm_nonneg r.w 0) (Ne.symm hz))).mp
    exact le_csSup (ratios_bddAbove M μ L n) (mem_insert_of_mem _ ⟨r,hz,rfl⟩)

theorem stateNorm_window_le_envelope {M : StationaryMethod} {μ L : ℝ}
    (r : HilbertRun M μ L) (k n : ℕ) :
    r.stateNorm (k+n) ≤ envelope M μ L n * r.stateNorm k := by
  simpa using stateNorm_le_envelope (r.shift k) n

/-- Every actual Hilbert trajectory is covered by the supremum. -/
theorem actual_stateNorm_le_envelope (M : StationaryMethod) {μ L : ℝ}
    {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    {f : E → ℝ} (hf : polyak.CenteredSmoothStronglyConvex μ L f)
    {w : ℕ → E} (hw : M.IsTrajectory (gradient f) w) (k n : ℕ) :
    M.stateNorm w (k+n) ≤ envelope M μ L n * M.stateNorm w k := by
  let r : HilbertRun M μ L := ⟨E,f,hf,w,hw⟩
  exact stateNorm_window_le_envelope r k n

theorem envelope_submultiplicative (M : StationaryMethod) (μ L : ℝ) (m n : ℕ) :
    envelope M μ L (m+n) ≤ envelope M μ L m * envelope M μ L n := by
  apply csSup_le (insert_nonempty _ _)
  intro x hx
  rcases hx with rfl | ⟨r,hr,rfl⟩
  · exact mul_nonneg (envelope_nonneg M μ L m) (envelope_nonneg M μ L n)
  · apply (div_le_iff₀ (lt_of_le_of_ne (M.stateNorm_nonneg r.w 0) (Ne.symm hr))).mpr
    calc
      _ ≤ envelope M μ L n * r.stateNorm m := stateNorm_window_le_envelope r m n
      _ ≤ envelope M μ L n * (envelope M μ L m * r.stateNorm 0) :=
        mul_le_mul_of_nonneg_left (stateNorm_le_envelope r m) (envelope_nonneg M μ L n)
      _ = _ := by dsimp [HilbertRun.stateNorm]; ring

/-- Literal all-restart ratio set agrees with the free-state convention. -/
theorem ratios_eq_restart_ratios (M : StationaryMethod) (μ L : ℝ) (n : ℕ) :
    ratios M μ L n = {x | ∃ (r : HilbertRun M μ L) (k : ℕ),
      r.stateNorm k ≠ 0 ∧ x=r.stateNorm (k+n)/r.stateNorm k} := by
  ext x
  constructor
  · rintro ⟨r,hr,rfl⟩
    exact ⟨r,0,hr,by simp⟩
  · rintro ⟨r,k,hr,rfl⟩
    exact ⟨r.shift k,by simpa using hr,by simp⟩

end
end nesterov.Rates
