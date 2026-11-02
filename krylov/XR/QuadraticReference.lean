import krylov.XR.QuadraticRetention
import krylov.XR.ModelStep

/-!
Article: main_krylov, thm:XR, genuine quadratic virtual-reference invariant.
Use: identify the real observed-array model at either an accepted point
or the unchanged anchor after a rejected probe. The current point need
only lie in the actually observed flag; it need not be a sum of every
stored probe. Source: positive Galerkin uniqueness and true CG conjugacy.
-/

namespace krylov.XR
noncomputable section
open Matrix krylov.Methods krylov.Reference krylov.Secant
open scoped InnerProductSpace
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {p : ℕ}

/-- Chronological true quadratic observations give exactly the positive
operator Gram matrix used by the already proved Galerkin solver. -/
theorem quadratic_array_model (Q : E →L[ℝ] E) (hQ : Q.toLinearMap.IsSymmetric)
    (s : Fin p → E) :
    latest (crossGram s (fun i => Q (s i))) = crossGram (fun i => Q (s i)) s := by
  have hraw : crossGram s (fun i => Q (s i)) = crossGram (fun i => Q (s i)) s := by
    ext i j
    exact (hQ _ _).symm
  have hsym : (crossGram (fun i => Q (s i)) s).IsSymm := by
    ext i j
    exact ((hQ _ _).trans (real_inner_comm _ _)).symm
  rw [hraw, latest_eq_of_isSymm hsym]

/-- The actual virtual point and gradient coincide with true CG on every
genuine independent observed Krylov basis, even when rejected probes have
been stored without changing the current anchor. -/
theorem quadratic_virtual_reference (Q : E →L[ℝ] E) (hQ : Q.toLinearMap.IsSymmetric)
    (hpos : ∀ v : E, v ≠ 0 → 0 < inner ℝ v (Q v))
    (g₀ : E) (k : ℕ) (hg : ∀ i < k, CG.gradient Q g₀ i ≠ 0)
    (s : Fin p → E) (hs : LinearIndependent ℝ s)
    (hspan : Submodule.span ℝ (Set.range s) = directionFlag Q g₀ k)
    (x : E) (hx : x ∈ Submodule.span ℝ (Set.range s)) :
    let y := fun i => Q (s i)
    let T := latest (crossGram s y)
    let g := g₀ + Q x
    x + modelVirtualCorrection s T g = CG.displacement Q g₀ k ∧
      modelVirtualGradient s y T g = CG.gradient Q g₀ k ∧
      modelDirection s y T g = CG.direction Q g₀ k := by
  dsimp only
  let T := crossGram (fun i => Q (s i)) s
  have hT : IsUnit T.det := isUnit_iff_ne_zero.mpr (operatorGram_posDef Q hQ hpos hs).det_pos.ne'
  have hu : CG.displacement Q g₀ k - x ∈ Submodule.span ℝ (Set.range s) := by
    apply Submodule.sub_mem _ _ hx
    rw [hspan]
    exact displacement_mem_directionFlag Q g₀ k
  have hbalance : g₀ + Q x + Q (CG.displacement Q g₀ k - x) = CG.gradient Q g₀ k := by
    rw [map_sub, CG.gradient_displacement]
    abel
  have ho : coordinates s (g₀ + Q x + Q (CG.displacement Q g₀ k - x)) = 0 := by
    rw [hbalance]
    ext i
    apply directionFlag_gradient_orthogonal Q hQ hpos g₀ k hg
    rw [← hspan]
    exact Submodule.subset_span (Set.mem_range_self i)
  have hc := modelCorrection_unique Q hQ s (g₀ + Q x)
    (CG.displacement Q g₀ k - x) hT hu ho
  have hv : modelVirtualGradient s (fun i => Q (s i)) T (g₀ + Q x) = CG.gradient Q g₀ k := by
    rw [modelVirtualGradient, ← combine_operator, hc, hbalance]
  rw [quadratic_array_model Q hQ s]
  refine ⟨?_, hv, ?_⟩
  · change x + combine s (modelCoefficients s T (g₀ + Q x)) = _
    rw [hc]
    abel
  · rw [modelDirection, hv]
    apply conjugacyDirection_unique s (fun i => Q (s i)) _ _ hT
    · rw [hspan]
      exact direction_add_gradient_mem_flag Q g₀ k
    · ext i
      change inner ℝ (Q (s i)) (CG.direction Q g₀ k) = 0
      have he := hQ (s i) (CG.direction Q g₀ k)
      change inner ℝ (Q (s i)) (CG.direction Q g₀ k) =
        inner ℝ (s i) (Q (CG.direction Q g₀ k)) at he
      rw [he]
      apply directionFlag_conjugate Q hQ hpos g₀ k hg
      rw [← hspan]
      exact Submodule.subset_span (Set.mem_range_self i)

/-- The true current CG direction lies outside its old flag while the
actual reference residual is nonzero. -/
theorem quadratic_new_direction_not_mem (Q : E →L[ℝ] E)
    (hQ : Q.toLinearMap.IsSymmetric) (hpos : ∀ v : E, v ≠ 0 → 0 < inner ℝ v (Q v))
    (g₀ : E) (k : ℕ) (hg : ∀ i < k, CG.gradient Q g₀ i ≠ 0)
    (hgk : CG.gradient Q g₀ k ≠ 0) : CG.direction Q g₀ k ∉ directionFlag Q g₀ k := by
  intro hd
  have he := directionFlag_conjugate Q hQ hpos g₀ k hg hd
  have hn := (CG.invariant_line_pos Q hpos g₀ k (CG.invariant Q hQ hpos g₀ k hg) hgk).1
  exact (hpos _ hn).ne' he

end
end krylov.XR
