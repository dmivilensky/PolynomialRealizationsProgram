import krylov.Secant.ConjugateWindow

/-!
Article: Theorem 2.4 [thm:window] of krylov.tex.
Use: define the actual operator-history fibre and optimize over every possible
common estimator; extended nonnegative radii also accommodate unbounded sets.
Source: TraubWozniakowski80, TraubEtAl88, radius of information; proved witnesses
and the conjugate-window bound supply the exact value here.
-/

namespace krylov.Secant
noncomputable section
open Matrix Finset
open scoped Matrix MatrixOrder BigOperators
variable {n p : ℕ}

/-- The actual hidden canonical forms compatible with the prescribed quadratic observations.
Use: the information fibre consists of genuine admissible symmetric operator histories.
Article: main_krylov, thm:window, the fibre at M=G. -/
def quadraticWindowFibre (S : Matrix (Fin n) (Fin p) ℝ)
    (base : Matrix (Fin n) (Fin n) ℝ) (ω : ℕ → ℝ) : Set (Matrix (Fin p) (Fin p) ℝ) :=
  {Z | ∃ A : ℕ → Matrix (Fin n) (Fin n) ℝ,
    A 0 = base ∧ (∀ k, (A k).IsSymm) ∧
    (∀ l < p, -(ω l • base) ≤ A (l + 1) - A l ∧ A (l + 1) - A l ≤ ω l • base) ∧
    Sᵀ * pairImages S A = Sᵀ * base * S ∧ Z = canonicalWindowError S base A}

/-- The minimax spectral radius of the actual history fibre, with arbitrary common centres.
Use: infimum and supremum are genuine complete-lattice operations, including zero budgets.
Article: main_krylov, thm:window, local radius of information. -/
def windowInformationRadius (S : Matrix (Fin n) (Fin p) ℝ)
    (base : Matrix (Fin n) (Fin n) ℝ) (ω : ℕ → ℝ) : ENNReal :=
  ⨅ K : Matrix (Fin p) (Fin p) ℝ, ⨆ Z : quadraticWindowFibre S base ω,
    ENNReal.ofReal (chebyshev1.opNorm (Z.val - K))

/-- Quadratic observations have the exact Gram model and zero canonical defect.
Use: the two constructed positive histories have Ω_*=0 despite their full hidden radius.
Article: main_krylov, thm:window, Ω_*=0.
Proof: the physical Gram form is symmetric, so latest fixes it and its skew part vanishes. -/
theorem quadratic_data_zero_defect (S : Matrix (Fin n) (Fin p) ℝ)
    (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.IsSymm)
    (M : Matrix (Fin p) (Fin p) ℝ) (hM : M = Sᵀ * A * S) :
    latest M = Sᵀ * A * S ∧ relativeOperator (latest M) (defect M) = 0 := by
  have hG : M.IsSymm := by
    rw [hM]
    simp only [Matrix.IsSymm, transpose_mul, transpose_transpose, hA.eq, Matrix.mul_assoc]
  rw [latest_eq_of_isSymm hG]
  exact ⟨hM, by simp only [defect, hG.eq, sub_self, relativeOperator, Matrix.mul_zero,
    Matrix.zero_mul]⟩

/-- Every full-rank nonempty window has information radius at least the full budget sum.
Use: the lower bound optimizes over all estimators on the complete observation fibre.
Article: main_krylov, thm:window, radius ≥ W for every window.
Proof: place both constructed admissible histories into the actual fibre and
bound the common-centre supremum by their proved two-scenario obstruction. -/
theorem window_information_lower (S : Matrix (Fin n) (Fin (p + 1)) ℝ)
    (hS : Function.Injective S.mulVec) (base : Matrix (Fin n) (Fin n) ℝ) (hbase : base.PosDef)
    (ω : ℕ → ℝ) (hω : ∀ l < p + 1, 0 ≤ ω l) (hW : (∑ l ∈ range (p + 1), ω l) < 1) :
    ENNReal.ofReal (∑ l ∈ range (p + 1), ω l) ≤ windowInformationRadius S base ω := by
  obtain ⟨Ap, Am, hp0, hm0, hsym, hb, _, hpd, hmd, _, _, hrad⟩ :=
    window_hidden_scenarios S hS base hbase ω hω hW
  have hp : canonicalWindowError S base Ap ∈ quadraticWindowFibre S base ω := by
    refine ⟨Ap, hp0, fun k => (hsym k).1, fun l hl => (hb l hl).1, ?_, rfl⟩
    rw [hpd, Matrix.mul_assoc]
  have hm : canonicalWindowError S base Am ∈ quadraticWindowFibre S base ω := by
    refine ⟨Am, hm0, fun k => (hsym k).2, fun l hl => (hb l hl).2, ?_, rfl⟩
    rw [hmd, Matrix.mul_assoc]
  apply le_iInf
  intro K
  -- The estimator K is common because these are members of one exact observed-data fibre.
  apply (ENNReal.ofReal_le_ofReal (hrad K)).trans
  rw [ENNReal.ofReal_max]
  exact max_le (le_iSup (fun Z : quadraticWindowFibre S base ω =>
    ENNReal.ofReal (chebyshev1.opNorm (Z.val - K))) ⟨canonicalWindowError S base Ap, hp⟩)
    (le_iSup (fun Z : quadraticWindowFibre S base ω =>
      ENNReal.ofReal (chebyshev1.opNorm (Z.val - K))) ⟨canonicalWindowError S base Am, hm⟩)

/-- The zero centre attains the full-budget upper radius for every conjugate window.
Use: closes the infimum over all estimators with an actual attaining common centre.
Article: main_krylov, thm:window, conjugate-window radius ≤ W.
Proof: every genuine member of the fibre obeys the exact conjugate-window upper bound. -/
theorem window_information_upper (S : Matrix (Fin n) (Fin p) ℝ)
    (hS : Function.Injective S.mulVec) (base : Matrix (Fin n) (Fin n) ℝ) (hbase : base.PosDef)
    (ω : ℕ → ℝ) (hω : ∀ l < p, 0 ≤ ω l)
    (c : Fin p → ℝ) (hc : Sᵀ * base * S = diagonal c) :
    windowInformationRadius S base ω ≤ ENNReal.ofReal (∑ l ∈ range p, ω l) := by
  apply iInf_le_of_le (0 : Matrix (Fin p) (Fin p) ℝ)
  apply iSup_le
  rintro ⟨Z, A, _, hA, hb, _, rfl⟩
  simp only [sub_zero]
  exact ENNReal.ofReal_le_ofReal (conjugate_window_upper S hS base hbase A hA ω hω
    (fun l hl => (hb l hl).1) (fun l hl => (hb l hl).2) c hc)

/-- The local information radius at quadratic data is exactly W for a conjugate window.
Use: the matching lower and upper bounds refer to the same actual admissible history fibre.
Article: main_krylov, thm:window, exact conjugate-window information radius.
Proof: antisymmetry combines the constructed indistinguishable histories with the zero-centre bound. -/
theorem conjugate_window_information_radius (S : Matrix (Fin n) (Fin (p + 1)) ℝ)
    (hS : Function.Injective S.mulVec) (base : Matrix (Fin n) (Fin n) ℝ) (hbase : base.PosDef)
    (ω : ℕ → ℝ) (hω : ∀ l < p + 1, 0 ≤ ω l) (hW : (∑ l ∈ range (p + 1), ω l) < 1)
    (c : Fin (p + 1) → ℝ) (hc : Sᵀ * base * S = diagonal c) :
    windowInformationRadius S base ω = ENNReal.ofReal (∑ l ∈ range (p + 1), ω l) :=
  le_antisymm (window_information_upper S hS base hbase ω hω c hc)
    (window_information_lower S hS base hbase ω hω hW)

/-- The empty window has exactly zero information radius, with no oldest-coordinate convention.
Use: completes the degenerate boundary case separately from the nonempty rank-one formula.
Article: main_krylov, thm:window, the empty-window boundary.
Proof: specialize the proved upper bound to the unique empty diagonal Gram matrix. -/
theorem empty_window_information_radius (S : Matrix (Fin n) (Fin 0) ℝ)
    (base : Matrix (Fin n) (Fin n) ℝ) (hbase : base.PosDef) (ω : ℕ → ℝ) :
    windowInformationRadius S base ω = 0 := by
  have hu := window_information_upper S (fun _ _ _ => Subsingleton.elim _ _) base hbase ω
    (fun l hl => False.elim (Nat.not_lt_zero l hl)) (fun _ => 0) (Subsingleton.elim _ _)
  simpa only [range_zero, sum_empty, ENNReal.ofReal_zero, nonpos_iff_eq_zero] using hu

end
end krylov.Secant
