import krylov.Convergence.ObservableFrame
import krylov.XR.ModelStep

/-!
Article: main_krylov, apG:Dunif, observable RFC model energy.
Use: relate the actually solved quadratic energy to the real correction
length before proving the accepted and failed energy-gate alternatives.
Source: the true finite coefficient quadratic forms and the actual model
normal equation. All constants are absolute and no step-length floor enters.
-/
namespace krylov.Convergence
noncomputable section
open Matrix krylov.Methods krylov.XR
open scoped InnerProductSpace Matrix.Norms.L2Operator
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {p : ℕ}

/-- A genuine quarter-identity coefficient matrix has the stated actual
quadratic-form sandwich, including dimension zero. Article: apG:Dunif. -/
theorem observable_coefficient_sandwich (M : Matrix (Fin p) (Fin p) ℝ)
    (hM : ‖M-1‖≤1/4) (c : Fin p → ℝ) :
    (3/4:ℝ)*‖WithLp.toLp 2 c‖^2≤c ⬝ᵥ (M*ᵥc) ∧
      c ⬝ᵥ (M*ᵥc)≤(5/4:ℝ)*‖WithLp.toLp 2 c‖^2 := by
  have hh := (coefficient_quadratic_norm_bound (M-1) c).trans
    (mul_le_mul_of_nonneg_right hM (sq_nonneg _))
  rw [Matrix.sub_mulVec,dotProduct_sub,observable_identity_form] at hh
  exact ⟨by linarith only [(abs_le.mp hh).1],by linarith only [(abs_le.mp hh).2]⟩

/-- The actual normalized model energy and actual physical correction
norm are uniformly equivalent under the derived Gram/model margins.
Article: main_krylov, apG:Dunif, energy gate interpretation. -/
theorem observable_energy_synthesis (s : Fin p → E) (M : Matrix (Fin p) (Fin p) ℝ)
    (hG : ‖crossGram s s-1‖≤1/4) (hM : ‖M-1‖≤1/4) (c : Fin p → ℝ) :
    0≤c ⬝ᵥ (M*ᵥc) ∧ ‖combine s c‖^2≤(5/3:ℝ)*(c ⬝ᵥ (M*ᵥc)) ∧
      c ⬝ᵥ (M*ᵥc)≤(5/3:ℝ)*‖combine s c‖^2 := by
  have hm := observable_coefficient_sandwich M hM c
  have hg := observable_coefficient_sandwich (crossGram s s) hG c
  rw [observable_gram_form] at hg
  exact ⟨(by positivity : 0≤(3/4:ℝ)*‖WithLp.toLp 2 c‖^2).trans hm.1,
    by linarith only [hg.2,hm.1],by linarith only [hm.2,hg.1]⟩

omit [InnerProductSpace ℝ E] in
/-- An actually passed model-energy gate controls the true correction
by 1.5 times its observed ratio times the actual searched length.
Article: main_krylov, apG:Dunif, observable correction bound. -/
theorem observable_energy_gate_pass (u : E) (energy curvature t bar : ℝ)
    (hE : 0≤energy) (hD : 0<curvature) (ht : 0≤t) (hb : 0≤bar)
    (hu : ‖u‖^2≤(5/3:ℝ)*energy) (hcurv : curvature≤(9/8:ℝ)*t^2)
    (hgate : Real.sqrt (energy/curvature)≤bar) :
    ‖u‖≤(3/2:ℝ)*bar*t := by
  have hED : 0≤energy/curvature := div_nonneg hE hD.le
  have hs := (sq_le_sq₀ (Real.sqrt_nonneg _) hb).mpr hgate
  rw [Real.sq_sqrt hED] at hs
  have hcap : energy≤bar^2*curvature := by
    have hh := (div_le_iff₀ hD).mp hs
    nlinarith only [hh]
  have hscale := mul_le_mul_of_nonneg_left hcurv (sq_nonneg bar)
  apply (sq_le_sq₀ (norm_nonneg u) (by positivity : 0≤(3/2:ℝ)*bar*t)).mp
  nlinarith only [hu,hcap,hscale,sq_nonneg (bar*t)]

omit [InnerProductSpace ℝ E] in
/-- An actually failed observable energy gate forces a real correction
larger than half the cutoff times the true line length.
Article: main_krylov, apG:Dunif, failed-gate short-step branch. -/
theorem observable_energy_gate_fail (u : E) (energy curvature t bar : ℝ)
    (hE : 0≤energy) (hD : 0<curvature) (ht : 0≤t) (hb : 0≤bar)
    (hu : energy≤(5/3:ℝ)*‖u‖^2) (hcurv : (7/8:ℝ)*t^2≤curvature)
    (hgate : bar<Real.sqrt (energy/curvature)) :
    (bar/2)*t<‖u‖ := by
  have hED : 0≤energy/curvature := div_nonneg hE hD.le
  have hs := (sq_lt_sq₀ hb (Real.sqrt_nonneg _)).mpr hgate
  rw [Real.sq_sqrt hED] at hs
  have hcap : bar^2*curvature<energy := (lt_div_iff₀ hD).mp hs
  have hscale := mul_le_mul_of_nonneg_left hcurv (sq_nonneg bar)
  apply (sq_lt_sq₀ (by positivity : 0≤(bar/2)*t) (norm_nonneg u)).mp
  nlinarith only [hu,hcap,hscale,sq_nonneg (bar*t)]

end
end krylov.Convergence
