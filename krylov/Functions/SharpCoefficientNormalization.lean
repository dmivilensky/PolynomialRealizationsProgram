import krylov.Functions.ReferencePrimitiveNormalization
import krylov.Functions.ReferencePlaneCoefficient

/-!
Article: main_krylov, prop:Fcycle(iii), preserving the sharp printed factor.
Use: absorb a quartic actual-source remainder and a first-order genuine
reference perturbation into one relative factor 1-O(e_c). Source: the
positive attained reference coefficient and elementary real inequalities.
-/
namespace krylov.Functions
noncomputable section

/-- A quartic source lower bound retains its exact positive sharp coefficient
when the actual reference changes by first order and the true error controls
the source scale. Article: main_krylov, prop:Fcycle(iii). -/
theorem sharp_coefficient_true_error_transfer
    (K₀ a C E c : ℝ) (hK₀ : 0<K₀) (ha : 0<a) (hC : 0<C) (hE : 0≤E) (hc : 0<c) :
    ∃ ep D : ℝ, 0<ep ∧ 0<D ∧ ∀ ε e K : ℝ, 0<ε → ε<ep →
      c*ε≤e → |K-K₀|≤C*ε →
      (1-D*e)*a^2*K*ε^3≤a^2*K₀*ε^3-E*ε^4 := by
  let F := a^2*C+E
  let D := 2*F/(c*a^2*K₀)
  have ha₂ : 0<a^2 := sq_pos_of_pos ha
  have hF : 0<F := by dsimp only [F]; positivity
  have hD : 0<D := div_pos (by positivity) (by positivity)
  have hDeq : D*c*(a^2*K₀/2)=F := by dsimp only [D]; field_simp
  refine ⟨K₀/(2*C),D,div_pos hK₀ (by positivity),hD,?_⟩
  intro ε e K hε heps he habs
  have hepos : 0<e := (mul_pos hc hε).trans_le he
  have hsmall : C*ε<K₀/2 := by
    have hh := (lt_div_iff₀ (by positivity : 0<2*C)).mp heps
    linarith only [hh]
  have hKL : K₀/2≤K := by linarith only [(abs_le.mp habs).1,hsmall]
  have hKU : K≤K₀+C*ε := by linarith only [(abs_le.mp habs).2]
  have hK : 0≤K := (half_pos hK₀).le.trans hKL
  have hbudget : F*ε≤D*e*(a^2*K) := by
    calc
      _ = D*(c*ε)*(a^2*K₀/2) := by rw [←hDeq]; ring
      _ ≤ D*e*(a^2*K₀/2) := mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left he hD.le) (by positivity)
      _ ≤ _ := mul_le_mul_of_nonneg_left
        (by nlinarith only [mul_le_mul_of_nonneg_left hKL ha₂.le])
        (mul_nonneg hD.le hepos.le)
  have hlin : (1-D*e)*a^2*K≤a^2*K₀-E*ε := by
    have hb := mul_le_mul_of_nonneg_left hKU ha₂.le
    dsimp only [F] at hbudget
    nlinarith only [hb,hbudget]
  have hh := mul_le_mul_of_nonneg_right hlin (pow_nonneg hε.le 3)
  convert! hh using 1
  ring

end
end krylov.Functions
