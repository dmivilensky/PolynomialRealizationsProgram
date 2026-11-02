import krylov.Functions.ReferenceFibreRegularity
import krylov.Reference.EnergyPositive
import krylov.Functions.ReferencePlaneFullReference
import krylov.Nonlinear.ReferenceCycleScale

/-!
Article: main_krylov, thm:LB, true-Hessian reference-error replacement.
Use: compare the actual last CG error in every nearby positive Hessian,
uniformly over every positive forcing scale. The perturbed Hessian may
be chosen discontinuously by the last query and cubic sign.
Source: actual joint CG energy analyticity, genuine open nonstagnation,
full termination and exact initial-gradient homogeneity.
-/
namespace krylov.Convergence
noncomputable section
open Matrix Set Metric Filter Topology krylov.Reference krylov.Functions krylov.Nonlinear krylov.Correction
open scoped InnerProductSpace Matrix.Norms.L2Operator
variable {k : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin (k+1))

/-- Actual final-step energy is the actual preterminal CG error squared.
Article: main_krylov, thm:LB, genuine reference-error normalization. -/
theorem oneGradient_terminal_energy_eq_error
    (A : Matrix (Fin (k+1)) (Fin (k+1)) ℝ) (hA : A.PosDef) (g : E)
    (hfull : referenceAtomCount A hA g=k+1) :
    cgEnergy A g k=‖cgCanonicalError A g k‖^2 := by
  rw [cgEnergy_eq_norm_sq A hA,terminal_step_error_norm A hA g (by rw [hfull])]

/-- Every sufficiently nearby positive Hessian has the same true full
reference and the original last CG error changes only relatively, uniformly
in every positive starting scale. No regularity of the choice of the
Hessian is assumed. Article: main_krylov, thm:LB. -/
theorem oneGradient_last_error_relative_neighborhood
    (A : Matrix (Fin (k+1)) (Fin (k+1)) ℝ) (hA : A.PosDef) (g : E)
    (hfull : referenceAtomCount A hA g=k+1) {η : ℝ} (hη : 0<η) :
    ∃ δ : ℝ,0<δ ∧∀ B : Matrix (Fin (k+1)) (Fin (k+1)) ℝ,∀ hB : B.PosDef,‖B-A‖≤δ →
      referenceAtomCount B hB g=k+1 ∧∀ h : ℝ,0<h →
      (1-η)*‖cgCanonicalError A (h • g) k‖^2≤‖cgCanonicalError B (h • g) k‖^2 ∧
        ‖cgCanonicalError B (h • g) k‖^2≤(1+η)*‖cgCanonicalError A (h • g) k‖^2 := by
  have hpre (j : ℕ) (hj : j≤k) : CG.gradient (cgOperator A) g j≠0 :=
    cg_nonstagnation A hA g j (by rw [hfull];omega)
  have hE := (cgEnergy_variable_analyticAt (fun B : Matrix (Fin (k+1)) (Fin (k+1)) ℝ=>B)
    (fun _=>g) A k analyticAt_id analyticAt_const hA hpre).continuousAt
  have hEpos := cgEnergy_pos A hA g k (by rw [hfull];omega)
  have hnear : ∀ᶠ B in 𝓝 A,|cgEnergy B g k-cgEnergy A g k|<η*cgEnergy A g k := by
    have hh := hE.eventually (Metric.ball_mem_nhds (cgEnergy A g k) (mul_pos hη hEpos))
    exact hh.mono (fun B hB=>by simpa only [mem_ball,Real.dist_eq] using hB)
  obtain ⟨δE,hδE,hball⟩ := Metric.eventually_nhds_iff.mp hnear
  obtain ⟨δN,hδN,hcount⟩ := reference_full_count_neighborhood A hA g (by omega) hfull
  refine ⟨min δN (δE/2),by positivity,?_⟩
  intro B hB hBA
  have hfullB := hcount B hB (hBA.trans (min_le_left _ _))
  have hd : dist B A<δE := by
    rw [dist_eq_norm]
    exact (hBA.trans (min_le_right _ _)).trans_lt (half_lt_self hδE)
  have he := abs_lt.mp (hball hd)
  rw [oneGradient_terminal_energy_eq_error A hA g hfull,
    oneGradient_terminal_energy_eq_error B hB g hfullB] at he
  refine ⟨hfullB,?_⟩
  intro h hh
  rw [cgCanonicalError_smul A hA g h hh.ne' k,cgCanonicalError_smul B hB g h hh.ne' k,
    norm_smul,norm_smul,Real.norm_of_nonneg hh.le,mul_pow,mul_pow]
  constructor
  · have hb : (1-η)*‖cgCanonicalError A g k‖^2≤‖cgCanonicalError B g k‖^2 := by nlinarith only [he.1]
    nlinarith only [mul_le_mul_of_nonneg_left hb (sq_nonneg h)]
  · have hb : ‖cgCanonicalError B g k‖^2≤(1+η)*‖cgCanonicalError A g k‖^2 := by nlinarith only [he.2]
    nlinarith only [mul_le_mul_of_nonneg_left hb (sq_nonneg h)]

end
end krylov.Convergence
