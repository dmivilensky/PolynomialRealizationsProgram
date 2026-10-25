import polyak.Interpolation.Conjugate
import polyak.Functions.Normalization

/-!
Article: Theorem `thm:interpolation`, including arbitrary sets and unbounded data.
Use: the public interpolation equivalence for genuine differentiable potentials.
Proof: convexification, closed strongly convex epigraph minimization and the
conjugate quadratic sandwich; necessity uses descent for the convexification.
-/

noncomputable section

namespace polyak.Interpolation

variable {E I : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-- Article: necessity in Theorem interpolation.
Use: any actual normalized potential satisfies all table inequalities.
Proof: convexify ψ, apply the convex descent gap with constant 2, and expand. -/
theorem _root_.polyak.NormalizedSmooth.tableFeasible {ψ : E → ℝ} (hψ : polyak.NormalizedSmooth ψ)
    (x : I → E) : TableFeasible x (fun i => gradient ψ (x i)) (fun i => ψ (x i)) := by
  let f : E → ℝ := fun z => ψ z + (1 / 2 : ℝ) * ‖z‖ ^ 2
  let g : E → E := fun z => gradient ψ z + z
  have hg (z : E) : HasGradientAt f (g z) z := by
    convert hasGradientAt_quadratic_add (hψ.differentiable z).hasGradientAt 1 1 using 1
    · funext w
      dsimp [f]
      ring
    · dsimp [g]
      module
  have hlip (z w : E) : ‖g z - g w‖ ≤ 2 * ‖z - w‖ := by
    have hnorm : ‖gradient ψ z - gradient ψ w‖ ≤ ‖z - w‖ := by
      simpa [dist_eq_norm] using hψ.grad_lipschitz.dist_le_mul z w
    have he : g z - g w = (gradient ψ z - gradient ψ w) + (z - w) := by dsimp [g]; abel
    rw [he]
    exact (norm_add_le _ _).trans (by linarith)
  have hlower (z w : E) : f z + inner ℝ (g z) (w - z) ≤ f w := by
    have hh := hψ.lower_model z w
    dsimp [f, g]
    simp only [inner_add_left, inner_sub_right, norm_sub_sq_real,
      real_inner_self_eq_norm_sq] at hh ⊢
    rw [real_inner_comm z w] at hh
    linarith
  have hupper := descent_inequality hg hlip
  apply (tableFeasible_iff_convex _ _ _).mpr
  intro i j
  have hh := convex_descent_gap (by norm_num : (0 : ℝ) < 2) hlower hupper (x i) (x j)
  change ‖g (x i) - g (x j)‖ ^ 2 ≤ _ at hh
  change f (x j) + inner ℝ (g (x j)) (x i - x j) +
    (1 / 4 : ℝ) * ‖g (x i) - g (x j)‖ ^ 2 ≤ f (x i)
  linarith

/-- Article: sufficiency in Theorem interpolation.
Use: one global ψ interpolates the whole table in any real Hilbert space,
without finite-index, boundedness, compactness or C² hypotheses.
Proof: exact convex reduction, the conjugate extension and Hilbert reflection. -/
theorem exists_normalized_interpolant {x σ : I → E} {values : I → ℝ}
    (h : TableFeasible x σ values) (star : I)
    (hx : x star = 0) (hσ : σ star = 0) (hvalues : values star = 0) :
    ∃ ψ : E → ℝ, polyak.NormalizedSmooth ψ ∧
      ∀ i, ψ (x i) = values i ∧ gradient ψ (x i) = σ i := by
  have hc := (tableFeasible_iff_convex x σ values).mp h
  obtain ⟨f, g, hg, _, _, hco, hdata⟩ := exists_convex_interpolant hc star
    hx (by simp [convexGradient, hx, hσ]) (by simp [convexValue, hx, hvalues])
  let ψ : E → ℝ := fun z => f z - (1 / 2 : ℝ) * ‖z‖ ^ 2
  have hgrad (z : E) : HasGradientAt ψ (g z - z) z := by
    convert hasGradientAt_quadratic_add (hg z) (-1) 1 using 1
    · funext w
      dsimp [ψ]
      ring
    · module
  have hdata' (i : I) : ψ (x i) = values i ∧ gradient ψ (x i) = σ i := by
    obtain ⟨hval, hgr⟩ := hdata i
    constructor
    · dsimp [ψ]
      rw [hval]
      dsimp [convexValue]
      ring
    · rw [(hgrad (x i)).gradient, hgr]
      simp [convexGradient]
  refine ⟨ψ, ⟨fun z => (hgrad z).differentiableAt, ?_, ?_, ?_⟩, hdata'⟩
  · apply LipschitzWith.of_dist_le_mul
    intro u v
    simp only [dist_eq_norm, NNReal.coe_one, one_mul]
    rw [(hgrad u).gradient, (hgrad v).gradient]
    have he : (g u - u) - (g v - v) = (g u - g v) - (u - v) := by abel
    rw [he]
    apply (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
    rw [norm_sub_sq_real]
    have hh := hco u v
    linarith
  · simpa [hx, hvalues] using (hdata' star).1
  · simpa [hx, hσ] using (hdata' star).2

/-- Article: Theorem interpolation on arbitrary sets.
Use: the complete equivalence, with the original actual function class.
Proof: necessity and the global conjugate construction. -/
theorem interpolation_iff {x σ : I → E} {values : I → ℝ} (star : I)
    (hx : x star = 0) (hσ : σ star = 0) (hvalues : values star = 0) :
    (∃ ψ : E → ℝ, polyak.NormalizedSmooth ψ ∧
      ∀ i, ψ (x i) = values i ∧ gradient ψ (x i) = σ i) ↔
      TableFeasible x σ values := by
  constructor
  · rintro ⟨ψ, hψ, hdata⟩
    have hh := hψ.tableFeasible x
    have hval : (fun i => ψ (x i)) = values := funext fun i => (hdata i).1
    have hgrad : (fun i => gradient ψ (x i)) = σ := funext fun i => (hdata i).2
    rwa [hval, hgrad] at hh
  · exact fun h => exists_normalized_interpolant h star hx hσ hvalues

end polyak.Interpolation
