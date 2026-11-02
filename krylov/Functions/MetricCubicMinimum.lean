import krylov.Functions.MetricCubicSelfConcordant

/-!
Article: main_krylov, thm:H, the genuine cubic minimizer.
Use: prove that the actual coordinate origin is the unique minimizer of
the real physical cubic on its certified metric ball, rather than assuming
a stationary-point or minimizer field.
Source: the actual diagonal tensor bound and exact quadratic-plus-cubic formula.
-/

namespace krylov.Functions
noncomputable section
open Set Metric krylov.Tensor
open scoped InnerProductSpace
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [CompleteSpace E] [FiniteDimensional ℝ E]

/-- The actual cubic objective dominates one-third of its true quadratic
metric throughout a certified ball. Article: main_krylov, thm:H. -/
theorem canonicalCubic_ball_lower (T : SymmetricCubic E) (a R : ℝ) (ha : 0≤a)
    (hR : 2*a*R≤1) (hd : ∀ v : E, ‖v‖=1 → |T.form v v v|≤2*a)
    {x : E} (hx : ‖x‖≤R) : ‖x‖^2/3≤canonicalCubic T x := by
  have ht := (abs_le.mp (cubic_diagonal_bound T (2*a) hd x x x)).1
  have hmargin : 0≤1-2*a*‖x‖ := by
    have hm := mul_le_mul_of_nonneg_left hx (by positivity : 0≤2*a)
    nlinarith only [hm,hR]
  have hm := mul_nonneg hmargin (sq_nonneg ‖x‖)
  rw [canonicalCubic_eq]
  nlinarith only [ht,hm]

/-- The actual physical metric cubic has origin as its unique minimizer on
the entire certified closed metric ball.
Article: main_krylov, thm:H, the genuine minimizer metric. -/
theorem metricCubic_unique_minimum (S : E ≃L[ℝ] E) (T : SymmetricCubic E)
    (a R : ℝ) (ha : 0≤a) (hR : 2*a*R≤1)
    (hd : ∀ v : E, ‖v‖=1 → |T.form v v v|≤2*a) :
    metricCubicObjective S T 0=0 ∧
      IsMinOn (metricCubicObjective S T) {x | ‖S x‖≤R} 0 ∧
      ∀ x : E, ‖S x‖≤R → x≠0 → metricCubicObjective S T 0<metricCubicObjective S T x := by
  have hzero : metricCubicObjective S T 0=0 := by
    simp [metricCubicObjective,coordinateObjective,canonicalCubic_eq]
  refine ⟨hzero,?_,?_⟩
  · intro x hx
    rw [hzero]
    exact (by positivity : (0 : ℝ)≤‖S x‖^2/3).trans (canonicalCubic_ball_lower T a R ha hR hd hx)
  · intro x hx hne
    rw [hzero]
    have hSx : S x≠0 := fun hz => hne (S.injective (by simpa only [map_zero] using hz))
    exact (by positivity : (0 : ℝ)<‖S x‖^2/3).trans_le (canonicalCubic_ball_lower T a R ha hR hd hx)

/-- At the printed strict-slack radius the actual physical cubic origin is
the unique minimizer on its entire closed metric ball.
Article: main_krylov, thm:H. -/
theorem metricCubic_radius_unique_minimum (S : E ≃L[ℝ] E) (T : SymmetricCubic E)
    {a : ℝ} (ha : 0<a) (hd : ∀ v : E, ‖v‖=1 → |T.form v v v|≤2*a) :
    metricCubicObjective S T 0=0 ∧
      IsMinOn (metricCubicObjective S T) {x | ‖S x‖≤canonicalCubicRadius a} 0 ∧
      ∀ x : E, ‖S x‖≤canonicalCubicRadius a → x≠0 →
        metricCubicObjective S T 0<metricCubicObjective S T x := by
  have hm := canonicalCubicRadius_margin ha
  have hR : 2*a*canonicalCubicRadius a≤1 := by
    have hp := Real.rpow_nonneg ha.le ((2 : ℝ)/3)
    linarith
  exact metricCubic_unique_minimum S T a (canonicalCubicRadius a) ha.le hR hd

end
end krylov.Functions
