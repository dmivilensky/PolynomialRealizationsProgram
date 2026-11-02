import krylov.XR.LocalUniformStep

/-!
Article: main_krylov, apG:local(b) and G4, uniformity over every window size.
Use: choose one strictly positive radius and descent constant and one norm
constant before all actual window sizes p≤n. This also includes p=0; no
constant depends on an executed window. Source: finite minima/maxima of
the primitive source-only constants already proved for each p.
-/

namespace krylov.XR
noncomputable section
open Matrix krylov.Methods
open scoped InnerProductSpace Matrix.Norms.L2Operator
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Minimum over the nonempty finite prefix 0,...,n. -/
def prefixMinimum (a : ℕ → ℝ) : ℕ → ℝ
  | 0 => a 0
  | n + 1 => min (prefixMinimum a n) (a (n + 1))

/-- Maximum over the same nonempty finite prefix. -/
def prefixMaximum (a : ℕ → ℝ) : ℕ → ℝ
  | 0 => a 0
  | n + 1 => max (prefixMaximum a n) (a (n + 1))

omit [NormedAddCommGroup E] [InnerProductSpace ℝ E] in
theorem prefixMinimum_pos (a : ℕ → ℝ) (ha : ∀ p, 0 < a p) (n : ℕ) :
    0 < prefixMinimum a n := by
  induction n with
  | zero => exact ha 0
  | succ n ih => exact lt_min ih (ha (n + 1))

omit [NormedAddCommGroup E] [InnerProductSpace ℝ E] in
theorem prefixMinimum_le (a : ℕ → ℝ) (n p : ℕ) (hp : p ≤ n) :
    prefixMinimum a n ≤ a p := by
  induction n with
  | zero =>
    have he : p = 0 := by omega
    subst p
    exact le_rfl
  | succ n ih =>
    by_cases he : p = n + 1
    · subst p; exact min_le_right _ _
    · exact (min_le_left _ _).trans (ih (by omega))

omit [NormedAddCommGroup E] [InnerProductSpace ℝ E] in
theorem le_prefixMaximum (a : ℕ → ℝ) (n p : ℕ) (hp : p ≤ n) :
    a p ≤ prefixMaximum a n := by
  induction n with
  | zero =>
    have he : p = 0 := by omega
    subst p
    exact le_rfl
  | succ n ih =>
    by_cases he : p = n + 1
    · subst p; exact le_max_right _ _
    · exact (ih (by omega)).trans (le_max_left _ _)

/-- One primitive local radius valid for every permitted window size. -/
def dimensionStepRadius (n : ℕ) (mu sigma upper : ℝ) : ℝ :=
  prefixMinimum (fun p => localStepRadius p mu sigma upper) n

/-- The printed c_flat can be fixed before the actual window size. -/
def dimensionDescentConstant (n : ℕ) (mu sigma upper trialUpper : ℝ) : ℝ :=
  prefixMinimum (fun p => localDescentConstant p mu sigma upper trialUpper) n

/-- The printed C_flat can likewise be fixed before all model steps. -/
def dimensionNormConstant (n : ℕ) (mu sigma upper ell : ℝ) : ℝ :=
  prefixMaximum (fun p => localNormConstant p mu sigma upper ell) n

/-- All source-only constants used in G4 have their required strict signs. -/
theorem dimension_constants_positive (n : ℕ) (mu sigma upper ell trialUpper : ℝ)
    (hmu : 0 < mu) (hsigma : 0 < sigma) (hupper : 0 < upper) (hell : 0 < ell) :
    0 < dimensionStepRadius n mu sigma upper ∧
      0 < dimensionDescentConstant n mu sigma upper trialUpper ∧
      0 < dimensionNormConstant n mu sigma upper ell := by
  refine ⟨prefixMinimum_pos _ (fun p => localStepRadius_pos (p := p) _ _ _ hmu hsigma hupper) n,
    prefixMinimum_pos _ (fun p => localDescentConstant_pos (p := p) _ _ _ _ hmu hsigma hupper) n, ?_⟩
  exact (localNormConstant_pos (p := 0) _ _ _ _ hmu hsigma hupper hell).trans_le
    (le_prefixMaximum (fun p => localNormConstant p mu sigma upper ell) n 0 (Nat.zero_le _))

/-- Actual primitive secant/Hessian assumptions give one uniform
gradient-related bound over all permitted model windows. -/
theorem dimension_model_step_gradientRelated {p : ℕ} (n : ℕ) (hp : p ≤ n)
    (H : E →L[ℝ] E) (hH : H.toLinearMap.IsSymmetric)
    (s y : Fin p → E) (hs : ∀ i, ‖s i‖ = 1)
    (mu sigma upper ell trialUpper epsilon : ℝ)
    (hmu : 0 < mu) (hsigma : 0 < sigma) (hupper : 0 < upper)
    (hell : 0 < ell) (htrialUpper : 0 < trialUpper) (he : 0 ≤ epsilon)
    (heps : epsilon ≤ dimensionStepRadius n mu sigma upper)
    (hpositive : ∀ v : E, mu * ‖v‖ ^ 2 ≤ inner ℝ v (H v)) (hHnorm : ‖H‖ ≤ upper)
    (hindependent : ∀ w : Fin p → ℝ,
      sigma ^ 2 * ‖WithLp.toLp 2 w‖ ^ 2 ≤ ‖combine s w‖ ^ 2)
    (hy : ∀ i, ‖y i - H (s i)‖ ≤ epsilon) (g : E) (c : ℝ)
    (htrial : modelDirection s y (krylov.Secant.latest (crossGram s y)) g ≠ 0 →
      ell * ‖modelDirection s y (krylov.Secant.latest (crossGram s y)) g‖ ^ 2 ≤ c ∧
        c ≤ trialUpper * ‖modelDirection s y (krylov.Secant.latest (crossGram s y)) g‖ ^ 2) :
    GradientRelated (dimensionDescentConstant n mu sigma upper trialUpper)
      (dimensionNormConstant n mu sigma upper ell) g (localModelStep s y g c) := by
  have hlocal := local_model_step_gradientRelated H hH s y hs mu sigma upper ell trialUpper epsilon
    hmu hsigma hupper hell htrialUpper he
    (heps.trans (prefixMinimum_le _ n p hp)) hpositive hHnorm hindependent hy g c htrial
  constructor
  · have hc := prefixMinimum_le (fun p => localDescentConstant p mu sigma upper trialUpper) n p hp
    have hmul := mul_le_mul_of_nonneg_right hc (sq_nonneg ‖g‖)
    dsimp only [dimensionDescentConstant]
    nlinarith [hlocal.1]
  · exact hlocal.2.trans (mul_le_mul_of_nonneg_right
      (le_prefixMaximum (fun p => localNormConstant p mu sigma upper ell) n p hp) (norm_nonneg g))

end
end krylov.XR
