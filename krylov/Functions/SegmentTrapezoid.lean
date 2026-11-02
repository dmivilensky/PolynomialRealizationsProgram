import krylov.Functions.TrapezoidLipschitz

/-!
Article: main_krylov, thm:Fexact, actual multidimensional endpoint remainders.
Use: derive the scalar segment derivatives from the genuine first, second and
third Frechet derivatives of the objective. Preserve the physical fourth power
of the step length and the original Lipschitz third-variation assumption.
Source: the proved scalar Peano kernels and the actual chain rule from mathlib.
-/

namespace krylov.Functions
noncomputable section
open Set
open scoped NNReal
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- A real affine segment differentiates a genuine Frechet derivative in its actual step direction.
Article: main_krylov, thm:Fexact. Proof: the ordinary Frechet/real chain rule. -/
theorem segment_hasDerivAt {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (g : E → F) (D : E → E →L[ℝ] F) (a s : E) (t : ℝ)
    (hD : HasFDerivAt g (D (a + t • s)) (a + t • s)) :
    HasDerivAt (fun t : ℝ => g (a + t • s)) (D (a + t • s) s) t := by
  have hp : HasDerivAt (fun t : ℝ => a + t • s) s t := by
    simpa using ((hasDerivAt_id t).smul_const s).const_add a
  exact hD.comp_hasDerivAt t hp

/-- The actual function-value defect and corrected endpoint diagonal have the sharp physical bounds.
Article: main_krylov, thm:Fexact, the 1/24 and 1/12 terms on any real multidimensional segment.
Proof: derive all three actual scalar derivatives, obtain the fourth-power line
Lipschitz constant from the physical third variation, and reuse the proved scalar bounds. -/
theorem segment_trapezoid_endpoint_bounds (f : E → ℝ) (D : E → E →L[ℝ] ℝ)
    (H : E → E →L[ℝ] E →L[ℝ] ℝ) (T : E → E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ)
    (a s : E)
    (hD : ∀ t ∈ Icc (0 : ℝ) 1, HasFDerivAt f (D (a + t • s)) (a + t • s))
    (hH : ∀ t ∈ Icc (0 : ℝ) 1, HasFDerivAt D (H (a + t • s)) (a + t • s))
    (hT : ∀ t ∈ Icc (0 : ℝ) 1, HasFDerivAt H (T (a + t • s)) (a + t • s))
    (L : ℝ≥0)
    (hLip : ∀ t ∈ Icc (0 : ℝ) 1, ∀ v ∈ Icc (0 : ℝ) 1,
      |T (a + t • s) s s s - T (a + v • s) s s s| ≤
        (L : ℝ) * ‖(a + t • s) - (a + v • s)‖ * ‖s‖ ^ 3) :
    let δ := f (a + s) - f a - (D a s + D (a + s) s) / 2
    |δ + T (a + s) s s s / 12| ≤ (L : ℝ) * ‖s‖ ^ 4 / 24 ∧
      |(D (a + s) - D a) s - 6 * δ - H (a + s) s s| ≤ (L : ℝ) * ‖s‖ ^ 4 / 12 := by
  let f₀ := fun t : ℝ => f (a + t • s)
  let f₁ := fun t : ℝ => D (a + t • s) s
  let f₂ := fun t : ℝ => H (a + t • s) s s
  let f₃ := fun t : ℝ => T (a + t • s) s s s
  have hd₁ t (ht : t ∈ Icc (0 : ℝ) 1) : HasDerivAt f₀ (f₁ t) t :=
    segment_hasDerivAt f D a s t (hD t ht)
  have hd₂ t (ht : t ∈ Icc (0 : ℝ) 1) : HasDerivAt f₁ (f₂ t) t := by
    simpa only [map_zero, add_zero] using
      (segment_hasDerivAt D H a s t (hH t ht)).clm_apply (hasDerivAt_const t s)
  have hd₃ t (ht : t ∈ Icc (0 : ℝ) 1) : HasDerivAt f₂ (f₃ t) t := by
    simpa only [map_zero, add_zero] using
      ((segment_hasDerivAt H T a s t (hT t ht)).clm_apply
        (hasDerivAt_const t s)).clm_apply (hasDerivAt_const t s)
  let C : ℝ := (L : ℝ) * ‖s‖ ^ 4
  have hC : 0 ≤ C := by positivity
  have hl : LipschitzOnWith (Real.toNNReal C) f₃ (Icc 0 1) := by
    apply LipschitzOnWith.of_dist_le'
    intro t ht v hv
    have he : (a + t • s) - (a + v • s) = (t - v) • s := by rw [sub_smul]; abel
    calc
      dist (f₃ t) (f₃ v) = |f₃ t - f₃ v| := Real.dist_eq _ _
      _ ≤ (L : ℝ) * ‖(a + t • s) - (a + v • s)‖ * ‖s‖ ^ 3 := hLip t ht v hv
      _ = C * dist t v := by rw [he, norm_smul, Real.norm_eq_abs, Real.dist_eq]; dsimp [C]; ring
  have he t (ht : t ∈ Icc (0 : ℝ) 1) : |f₃ t - f₃ 1| ≤ C * (1 - t) := by
    have h := hl.norm_sub_le ht (by simp : (1 : ℝ) ∈ Icc 0 1)
    simpa only [Real.norm_eq_abs, abs_of_nonpos (sub_nonpos.mpr ht.2), neg_sub,
      Real.coe_toNNReal _ hC] using h
  have hb₁ := trapezoid_endpoint_remainder f₀ f₁ f₂ f₃ hd₁ hd₂ hd₃ hl.continuousOn C he
  have hb₂ := trapezoid_corrected_endpoint_bound f₀ f₁ f₂ f₃ hd₁ hd₂ hd₃ (Real.toNNReal C) hl
  constructor
  · simpa only [trapezoidDefect, f₀, f₁, f₃, C, zero_smul, one_smul, add_zero] using hb₁
  · simpa only [trapezoidDefect, f₀, f₁, f₂, C, zero_smul, one_smul, add_zero, sub_apply,
      Real.coe_toNNReal _ hC] using hb₂

end
end krylov.Functions
