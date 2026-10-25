import polyak.Energy.KernelEstimate
import polyak.Energy.Values

/-!
Article: Appendix A, quadratic endpoint windows in Lemma energy.
Use: a dimension-independent, explicit localization bound for every finite
kernel and every Hilbert sequence. Its spectral premise is subsequently discharged
by the exact symbol of the interpolation certificate.
-/

noncomputable section

namespace polyak.Energy

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Article: integer-indexed endpoint energy window, before reindexing actual segments. -/
def integerWindow (f : ℤ → E) (w k : ℤ) : ℝ :=
  ∑ l ∈ Finset.Icc (k-w) (k+w), ‖f l‖^2

/-- Article: interval geometry of the cutoff discrepancy.
Proof: a changed term has either its center or a shifted endpoint outside the interval,
which places both endpoints within twice the shift radius of one end. -/
theorem cutoff_boundary_interval {i j R k a b : ℤ} (_hR : 0 ≤ R)
    (ha : |a| ≤ R) (hb : |b| ≤ R)
    (hk : k ∈ Finset.Icc (i-R) (j+R))
    (hmis : ¬ (k ∈ Finset.Icc i j ↔
      k+a ∈ Finset.Icc i j ∧ k+b ∈ Finset.Icc i j)) :
    k+a ∈ Finset.Icc (i-2*R) (i+2*R) ∪ Finset.Icc (j-2*R) (j+2*R) ∧
    k+b ∈ Finset.Icc (i-2*R) (i+2*R) ∪ Finset.Icc (j-2*R) (j+2*R) := by
  have ha' := abs_le.mp ha
  have hb' := abs_le.mp hb
  simp only [Finset.mem_Icc] at hk hmis
  simp only [Finset.mem_union, Finset.mem_Icc]
  omega

omit [InnerProductSpace ℝ E] in
/-- Article: the energy on the union of the two boundary intervals is bounded by their sum. -/
theorem boundary_union_energy_le (f : ℤ → E) (i j w : ℤ) :
    (∑ l ∈ Finset.Icc (i-w) (i+w) ∪ Finset.Icc (j-w) (j+w), ‖f l‖^2) ≤
      integerWindow f w i + integerWindow f w j := by
  have he := Finset.sum_union_inter (s₁ := Finset.Icc (i-w) (i+w))
    (s₂ := Finset.Icc (j-w) (j+w)) (f := fun l => ‖f l‖^2)
  have hn : 0 ≤ ∑ l ∈ Finset.Icc (i-w) (i+w) ∩ Finset.Icc (j-w) (j+w), ‖f l‖^2 :=
    Finset.sum_nonneg (fun l _ => sq_nonneg ‖f l‖)
  unfold integerWindow
  linarith

/-- Article: complete quadratic localization estimate on a finite interval.
Proof: Parseval for the cutoff and the exact twice-radius boundary discrepancy estimate. -/
theorem sum_kernelEval_interval_le (K : Kernel) (f : ℤ → E) {ε : ℝ}
    (hneg : ∀ θ, kernelSymbol K θ ≤ -ε) (R : ℤ) (hR : 0 ≤ R)
    (hsupport : ∀ p ∈ K, |p.2.1| ≤ R ∧ |p.2.2| ≤ R) (i j : ℤ) :
    (∑ k ∈ Finset.Icc i j, kernelEval K f k) ≤
      -ε * (∑ k ∈ Finset.Icc i j, ‖f k‖^2) +
        kernelSize K * (integerWindow f (2*R) i + integerWindow f (2*R) j) := by
  let S := Finset.Icc i j
  let T := Finset.Icc (i-R) (j+R)
  let B := Finset.Icc (i-2*R) (i+2*R) ∪ Finset.Icc (j-2*R) (j+2*R)
  have hST : S ⊆ T := by
    intro k hk
    simp only [S, T, Finset.mem_Icc] at hk ⊢
    omega
  have hcover : ∀ p ∈ K, ∀ l ∈ S, l-p.2.1 ∈ T := by
    intro p hp l hl
    have ha := abs_le.mp (hsupport p hp).1
    simp only [S, T, Finset.mem_Icc] at hl ⊢
    omega
  have hboundary : ∀ p ∈ K, ∀ k ∈ T,
      ¬ (k ∈ S ↔ k+p.2.1 ∈ S ∧ k+p.2.2 ∈ S) →
        k+p.2.1 ∈ B ∧ k+p.2.2 ∈ B := by
    intro p hp k hk hmis
    exact cutoff_boundary_interval hR (hsupport p hp).1 (hsupport p hp).2 hk hmis
  have hquad := sum_kernelEval_le_of_symbol K S T B f hneg hST hcover hboundary
  have hbound := mul_le_mul_of_nonneg_left (boundary_union_energy_le f i j (2*R))
    (kernelSize_nonneg K)
  dsimp [S, B] at hquad
  linarith

/-- Article: passing from natural indices to integer indices preserves a finite interval sum. -/
theorem sum_integer_Icc_natCast (v : ℤ → ℝ) (i j : ℕ) :
    (∑ k ∈ Finset.Icc (i : ℤ) (j : ℤ), v k) =
      ∑ k ∈ Finset.Icc i j, v k := by
  apply Finset.sum_bij (fun k _ => k.toNat)
  · intro k hk
    have hk' := Finset.mem_Icc.mp hk
    exact Finset.mem_Icc.mpr ⟨by omega, by omega⟩
  · intro k₁ hk₁ k₂ hk₂ he
    have h₁ := (Finset.mem_Icc.mp hk₁).1
    have h₂ := (Finset.mem_Icc.mp hk₂).1
    omega
  · intro k hk
    have hk' := Finset.mem_Icc.mp hk
    refine ⟨k, Finset.mem_Icc.mpr ⟨by omega, by omega⟩, by simp⟩
  · intro k hk
    have hk' := (Finset.mem_Icc.mp hk).1
    congr 1
    omega

omit [InnerProductSpace ℝ E] in
/-- Article: integer windows become exactly the natural-indexed energy windows away from zero. -/
theorem integerWindow_natCast (f : ℕ → E) {w k : ℕ} (hwk : w ≤ k) :
    integerWindow (fun l => f l.toNat) (w : ℤ) (k : ℤ) =
      window (fun l => ‖f l‖^2) w k := by
  unfold integerWindow window
  rw [← Int.natCast_sub hwk, ← Nat.cast_add, sum_integer_Icc_natCast]
  simp only [Int.toNat_natCast]

/-- Article: the quadratic estimate in the natural indexing of actual segments. -/
theorem sum_kernelEval_nat_interval_le (K : Kernel) (f : ℕ → E) {ε : ℝ}
    (hneg : ∀ θ, kernelSymbol K θ ≤ -ε) (R : ℕ)
    (hsupport : ∀ p ∈ K, |p.2.1| ≤ (R : ℤ) ∧ |p.2.2| ≤ (R : ℤ))
    (i j : ℕ) (hi : 2*R ≤ i) (hij : i ≤ j) :
    (∑ k ∈ Finset.Icc i j, kernelEval K (fun l => f l.toNat) k) ≤
      -ε * (∑ k ∈ Finset.Icc i j, ‖f k‖^2) +
        kernelSize K * (window (fun l => ‖f l‖^2) (2*R) i +
          window (fun l => ‖f l‖^2) (2*R) j) := by
  have he := sum_kernelEval_interval_le K (fun l => f l.toNat) hneg (R : ℤ)
    (by omega) hsupport (i : ℤ) (j : ℤ)
  rw [sum_integer_Icc_natCast, sum_integer_Icc_natCast] at he
  have h2 : 2*(R : ℤ) = ((2*R : ℕ) : ℤ) := by omega
  rw [h2, integerWindow_natCast f hi, integerWindow_natCast f (by omega)] at he
  simpa only [Int.toNat_natCast] using he

/-- Article: a finite kernel has a finite spatial radius. -/
def kernelRadius : Kernel → ℕ
  | [] => 0
  | p::K => max (max p.2.1.natAbs p.2.2.natAbs) (kernelRadius K)

/-- Article: the computed spatial radius bounds every coefficient's two shifts. -/
theorem kernelRadius_bounds (K : Kernel) :
    ∀ p ∈ K, |p.2.1| ≤ (kernelRadius K : ℤ) ∧ |p.2.2| ≤ (kernelRadius K : ℤ) := by
  induction K with
  | nil => simp
  | cons q K ih =>
    intro p hp
    rcases List.mem_cons.mp hp with hp | hp
    · subst p
      have h₁ : q.2.1.natAbs ≤ kernelRadius (q::K) :=
        (Nat.le_max_left _ _).trans (Nat.le_max_left _ _)
      have h₂ : q.2.2.natAbs ≤ kernelRadius (q::K) :=
        (Nat.le_max_right _ _).trans (Nat.le_max_left _ _)
      constructor
      · simpa only [Int.natCast_natAbs] using Int.ofNat_le.mpr h₁
      · simpa only [Int.natCast_natAbs] using Int.ofNat_le.mpr h₂
    · have hh := ih p hp
      have hle : (kernelRadius K : ℤ) ≤ (kernelRadius (q::K) : ℤ) := by
        exact Int.ofNat_le.mpr (Nat.le_max_right (max q.2.1.natAbs q.2.2.natAbs) (kernelRadius K))
      exact ⟨hh.1.trans hle, hh.2.trans hle⟩

/-- Article: endpoint-window radius can be enlarged to include every lag and both recurrence neighbors. -/
theorem exists_kernel_radius (K : Kernel) (N : ℕ) :
    ∃ R : ℕ, N ≤ R ∧ ∀ p ∈ K, |p.2.1| ≤ (R : ℤ) ∧ |p.2.2| ≤ (R : ℤ) := by
  refine ⟨max N (kernelRadius K), Nat.le_max_left _ _, fun p hp => ?_⟩
  have h := kernelRadius_bounds K p hp
  have hle : (kernelRadius K : ℤ) ≤ ((max N (kernelRadius K) : ℕ) : ℤ) :=
    Int.ofNat_le.mpr (Nat.le_max_right N (kernelRadius K))
  exact ⟨h.1.trans hle, h.2.trans hle⟩

end polyak.Energy
