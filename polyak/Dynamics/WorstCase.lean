import polyak.Basic
import polyak.Dynamics.Iteration
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
Article: polyaksiopt, introduction eq:WN.
Use: actual finite-dimensional worst cases and their dimension-uniform limsup rate.
-/

namespace polyak.Dynamics
noncomputable section
open Filter Set
open scoped Topology

/-- Article: eq:WN. Use: genuine ratios on the original scalar-function class. -/
def ratios (μ L α β : ℝ) (d N : ℕ) : Set ℝ :=
  {r | ∃ (f : EuclideanSpace ℝ (Fin d) → ℝ), SmoothStronglyConvex μ L f ∧
    ∃ xstar x₀, (∀ y, f xstar ≤ f y) ∧ x₀ ≠ xstar ∧
      r = ‖iterate (gradient f) α β x₀ N - xstar‖ / ‖x₀-xstar‖}

/-- Article: eq:WN. Use: finite-dimensional supremum, with the harmless zero lower bound. -/
def worst (μ L α β : ℝ) (d N : ℕ) : ℝ := sSup (insert 0 (ratios μ L α β d N))

/-- Article: eq:WN. Use: all positive finite dimensions of the original problem. -/
def allRatios (μ L α β : ℝ) (N : ℕ) : Set ℝ :=
  {r | ∃ d, 0 < d ∧ r ∈ ratios μ L α β d N}

/-- Article: eq:WN. Use: the supremum over all actual finite-dimensional instances. -/
def worstAll (μ L α β : ℝ) (N : ℕ) : ℝ :=
  sSup (insert 0 (allRatios μ L α β N))

/-- Article: eq:WN. Use: the source limsup definition, before existence of a limit. -/
def rate (μ L α β : ℝ) : ℝ :=
  limsup (fun N : ℕ => worstAll μ L α β N ^ ((N : ℝ)⁻¹)) atTop

/-- Article: eq:WN. Use: every global minimizer is stationary for the true gradient. -/
theorem gradient_eq_zero_of_min {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [CompleteSpace E] {f : E → ℝ} {xstar : E}
    (hmin : ∀ y, f xstar ≤ f y) : gradient f xstar = 0 := by
  have hlocal : IsLocalMin f xstar := Filter.Eventually.of_forall hmin
  simp [gradient, hlocal.fderiv_eq_zero]

/-- Article: eq:WN. Use: source ratios cannot be negative. -/
theorem ratio_nonneg {μ L α β r : ℝ} {d N : ℕ}
    (hr : r ∈ ratios μ L α β d N) : 0 ≤ r := by
  obtain ⟨f, _, xstar, x₀, _, _, rfl⟩ := hr
  positivity

/-- Article: eq:WN. Use: finite-horizon upper bounds need no compactness of functions. -/
theorem ratio_le {μ L α β r : ℝ} (hα : 0 ≤ α) (hβ : 0 ≤ β) {d N : ℕ}
    (hr : r ∈ ratios μ L α β d N) : r ≤ (1+α*L+2*β)^N := by
  obtain ⟨f, hf, xstar, x₀, hmin, hne, rfl⟩ := hr
  have hL : 0 ≤ L := (hf.mu_pos.trans hf.mu_lt_L).le
  have hg : LipschitzWith ⟨L, hL⟩ (gradient f) := by
    apply LipschitzWith.of_dist_le_mul
    intro x y
    change ‖gradient f x-gradient f y‖ ≤ L*‖x-y‖
    exact hf.grad_lipschitz x y
  have hn : 0 < ‖x₀-xstar‖ := norm_pos_iff.2 (sub_ne_zero.2 hne)
  apply (div_le_iff₀ hn).2
  exact iterate_error_le hg hα hβ (gradient_eq_zero_of_min hmin) x₀ N

/-- Article: eq:WN. Use: the inserted zero and all source ratios have one uniform bound. -/
theorem ratios_bddAbove {μ L α β : ℝ} (hμ : 0 < μ) (hL : μ < L)
    (hα : 0 ≤ α) (hβ : 0 ≤ β) (d N : ℕ) :
    BddAbove (insert 0 (ratios μ L α β d N)) := by
  refine ⟨(1+α*L+2*β)^N, ?_⟩
  intro r hr
  rcases hr with rfl | hr
  · have : 0 ≤ L := (hμ.trans hL).le
    positivity
  · exact ratio_le hα hβ hr

/-- Article: eq:WN. Use: dimension-uniform boundedness of the exact finite supremum. -/
theorem allRatios_bddAbove {μ L α β : ℝ} (hμ : 0 < μ) (hL : μ < L)
    (hα : 0 ≤ α) (hβ : 0 ≤ β) (N : ℕ) :
    BddAbove (insert 0 (allRatios μ L α β N)) := by
  refine ⟨(1+α*L+2*β)^N, ?_⟩
  intro r hr
  rcases hr with rfl | ⟨d, _, hr⟩
  · have : 0 ≤ L := (hμ.trans hL).le
    positivity
  · exact ratio_le hα hβ hr

/-- Article: eq:WN. Use: the exact finite-dimensional supremum is nonnegative. -/
theorem worst_nonneg {μ L α β : ℝ} (hμ : 0 < μ) (hL : μ < L)
    (hα : 0 ≤ α) (hβ : 0 ≤ β) (d N : ℕ) : 0 ≤ worst μ L α β d N :=
  le_csSup (ratios_bddAbove hμ hL hα hβ d N) (mem_insert _ _)

/-- Article: eq:WN. Use: the source supremum has a finite uniform majorant. -/
theorem worst_le {μ L α β : ℝ} (hμ : 0 < μ) (hL : μ < L)
    (hα : 0 ≤ α) (hβ : 0 ≤ β) (d N : ℕ) :
    worst μ L α β d N ≤ (1+α*L+2*β)^N := by
  apply csSup_le (insert_nonempty _ _)
  intro r hr
  rcases hr with rfl | hr
  · have : 0 ≤ L := (hμ.trans hL).le
    positivity
  · exact ratio_le hα hβ hr

/-- Article: eq:WN. Use: nonnegativity before taking the rate root. -/
theorem worstAll_nonneg {μ L α β : ℝ} (hμ : 0 < μ) (hL : μ < L)
    (hα : 0 ≤ α) (hβ : 0 ≤ β) (N : ℕ) : 0 ≤ worstAll μ L α β N :=
  le_csSup (allRatios_bddAbove hμ hL hα hβ N) (mem_insert _ _)

/-- Article: eq:WN. Use: a dimension-independent bound on the exact source supremum. -/
theorem worstAll_le {μ L α β : ℝ} (hμ : 0 < μ) (hL : μ < L)
    (hα : 0 ≤ α) (hβ : 0 ≤ β) (N : ℕ) :
    worstAll μ L α β N ≤ (1+α*L+2*β)^N := by
  apply csSup_le (insert_nonempty _ _)
  intro r hr
  rcases hr with rfl | ⟨d, _, hr⟩
  · have : 0 ≤ L := (hμ.trans hL).le
    positivity
  · exact ratio_le hα hβ hr

/-- Article: eq:WN. Use: every fixed positive dimension embeds in the unrestricted supremum. -/
theorem worst_le_worstAll {μ L α β : ℝ} (hμ : 0 < μ) (hL : μ < L)
    (hα : 0 ≤ α) (hβ : 0 ≤ β) {d : ℕ} (hd : 0 < d) (N : ℕ) :
    worst μ L α β d N ≤ worstAll μ L α β N := by
  apply csSup_le_csSup (allRatios_bddAbove hμ hL hα hβ N) (insert_nonempty _ _)
  intro r hr
  rcases hr with rfl | hr
  · exact mem_insert _ _
  · exact mem_insert_of_mem _ ⟨d, hd, hr⟩

end
end polyak.Dynamics
