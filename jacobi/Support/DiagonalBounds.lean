import jacobi.Support.CoefficientIdentities
import jacobi.Support.SineShiftBounds
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

/-!
Article: jacobi, Appendix C.3 (coefficient bounds).
The actual support diagonal has the full printed uniform inverse-square
bound. Its numerator cancellation is exact and its genuine denominator
has a uniform positive lower bound on every original growing row range.
Use: the support polynomial oscillatory energy estimate is applied to the actual original three-term recurrence with this proved inverse-square diagonal perturbation.
-/
namespace jacobi.Support
noncomputable section
open Real Filter jacobi.Reference
open scoped Topology

/-- The actual original support diagonal satisfies the printed uniform O(m^-2) estimate throughout the complete growing half-chain range.
Use: the support polynomial oscillatory energy estimate is applied to the actual original three-term recurrence with this proved inverse-square diagonal perturbation.
Article: jacobi, Appendix C.3 (coefficient bounds).
Proof: the proved exact centered diagonal has two genuine small sine factors in its numerator, hence a bound proportional to h^2. Each original denominator sine is at least a positive constant times m*h, so their product cancels this exact step square and leaves the stated inverse-square index bound. -/
theorem diagonal_bounds {a b : ℝ} (ha:-1<a) (hb:-1<b) :
    ∃C:ℝ,0<C ∧ ∀ᶠn:ℕ in atTop,∀m:ℕ,0<m→2*m≤n+6→
      |diagonal a b n m|≤C/(m:ℝ)^2 := by
  -- The denominator signs are supplied by the actual shifted-sine estimates at every used original row.
  have hg := parameter_pos ha hb
  obtain ⟨c₀,C₀,hc₀,hC₀,h₀⟩ := shifted_sine_bounds a b (show -1<averageGamma a b by linarith [hg.2.2]) 6
  obtain ⟨c₁,C₁,hc₁,hC₁,h₁⟩ := shifted_sine_bounds a b (show -1<averageGamma a b-1/2 by linarith [hg.2.2]) 6
  obtain ⟨c₂,C₂,hc₂,hC₂,h₂⟩ := shifted_sine_bounds a b (show -1<averageGamma a b+1/2 by linarith [hg.2.2]) 6
  let P : ℝ := (gamma a-gamma b)/2
  let Q : ℝ := averageGamma a b-1/2
  let A : ℝ := |P| *|Q|
  refine ⟨1+A/(c₁*c₂),by dsimp [A]; positivity,?_⟩
  filter_upwards [h₀,h₁,h₂] with n hn₀ hn₁ hn₂
  intro m hm hmn
  have hm0 : (0:ℝ)<m := by exact_mod_cast hm
  have hm2 : 0<(m:ℝ)^2 := sq_pos_of_pos hm0
  have hh := hn₀.1
  have hs₀ := (hn₀.2 m hm hmn).1
  have hs₁ : c₁*(m:ℝ)*step a b n≤sin (((m:ℝ)+averageGamma a b-1/2)*step a b n) := by
    simpa only [sub_eq_add_neg,add_assoc] using (hn₁.2 m hm hmn).1
  have hs₂ : c₂*(m:ℝ)*step a b n≤sin (((m:ℝ)+averageGamma a b+1/2)*step a b n) := by
    simpa only [add_assoc] using (hn₂.2 m hm hmn).1
  have hp₀ : 0<sin (((m:ℝ)+averageGamma a b)*step a b n) := lt_of_lt_of_le (by positivity) hs₀
  have hp₁ : 0<sin (((m:ℝ)+averageGamma a b-1/2)*step a b n) := lt_of_lt_of_le (by positivity) hs₁
  have hp₂ : 0<sin (((m:ℝ)+averageGamma a b+1/2)*step a b n) := lt_of_lt_of_le (by positivity) hs₂
  have hden : 0<sin (((m:ℝ)+averageGamma a b-1/2)*step a b n)*sin (((m:ℝ)+averageGamma a b+1/2)*step a b n) :=
    mul_pos hp₁ hp₂
  have hdenlo : c₁*c₂*(m:ℝ)^2*(step a b n)^2≤
      sin (((m:ℝ)+averageGamma a b-1/2)*step a b n)*sin (((m:ℝ)+averageGamma a b+1/2)*step a b n) := by
    convert mul_le_mul hs₁ hs₂ (by positivity) hp₁.le using 1; ring
  have hP : |sin (P*step a b n)|≤|P| *step a b n := by
    simpa only [abs_mul,abs_of_pos hh] using (Real.abs_sin_le_abs (x:=P*step a b n))
  have hQ : |sin (Q*step a b n)|≤|Q| *step a b n := by
    simpa only [abs_mul,abs_of_pos hh] using (Real.abs_sin_le_abs (x:=Q*step a b n))
  have hnum : |-cos (step a b n/2)*sin (P*step a b n)*sin (Q*step a b n)|≤A*(step a b n)^2 := by
    rw [abs_mul,abs_mul,abs_neg]
    calc
      _ ≤ 1*(|P| *step a b n)*(|Q| *step a b n) :=
        mul_le_mul (mul_le_mul (abs_cos_le_one _) hP (abs_nonneg _) (by norm_num)) hQ
          (abs_nonneg _) (by positivity)
      _ = _ := by dsimp [A]; ring
  rw [diagonal_centered a b n m hp₀.ne' hp₁.ne' hp₂.ne',abs_div,abs_of_pos hden]
  calc
    _ ≤ A*(step a b n)^2/(c₁*c₂*(m:ℝ)^2*(step a b n)^2) :=
      div_le_div₀ (by dsimp [A]; positivity) hnum (by positivity) hdenlo
    _ = (A/(c₁*c₂))/(m:ℝ)^2 := by field_simp [hc₁.ne',hc₂.ne',hm0.ne',hh.ne']
    _ ≤ _ := div_le_div_of_nonneg_right (by linarith) hm2.le

end
end jacobi.Support
